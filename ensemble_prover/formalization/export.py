"""Export a verified source bundle against its pinned, existing Lake project."""

from __future__ import annotations

import hashlib
import json
import os
import shlex
import shutil
import tempfile
from pathlib import Path
from typing import Any

from ..config import LeanConfig
from ..lean_runner import LeanRunner
from ..theorem_project import _strip_root_prefix, is_valid_lean_qualified_name
from .documents import SourceLibrary, _mkdir_durable, _sync_directory
from .environment import EnvironmentSnapshot
from .lean import ModuleArtifact, ModuleCompiler
from .store import ProjectStore


def _write_json(path: Path, data: Any) -> None:
    path.write_text(
        json.dumps(data, ensure_ascii=False, allow_nan=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _sync_bundle(directory: Path) -> None:
    """Persist all staged bytes and directory entries before publication."""
    for raw, _, files in os.walk(directory, topdown=False):
        parent = Path(raw)
        for name in files:
            with (parent / name).open("rb") as handle:
                os.fsync(handle.fileno())
        _sync_directory(parent)


async def export_project(campaign_dir: Path, output_dir: Path) -> dict[str, Any]:
    """Check the complete compiled closure and re-import it from a fresh bundle.

    Trusted Mathlib/project dependencies are deliberately not vendored. Their
    complete recorded identity and original source documents accompany the Lean
    modules; the README states this reproducibility requirement explicitly.
    Existing destinations are never overwritten, even if export validation fails.
    """
    directory = Path(campaign_dir).expanduser().resolve(strict=True)
    output = Path(output_dir).expanduser().absolute()
    if output.exists() or output.is_symlink():
        raise FileExistsError(f"export destination already exists: {output}")
    with ProjectStore(directory) as store:
        metadata = store.get_metadata()
        if metadata.get("campaign_schema") != 1 or not metadata.get("initialized"):
            raise ValueError("unsupported or incomplete campaign")
        task = store.get_task(metadata["root_id"])
        if (
            task.state != "verified"
            or not task.result
            or task.result.get("kind") != "theorem"
        ):
            raise ValueError("only a verified, proved root can be exported")
        result = task.result
        generation = task.generation
        environment = EnvironmentSnapshot.from_dict(metadata["environment"])
        name = result.get("name")
        if not isinstance(name, str) or not is_valid_lean_qualified_name(name):
            raise ValueError("invalid exported theorem identity")
        compiler = ModuleCompiler(
            environment.project_path,
            directory / "modules",
            trusted_imports=environment.trusted_imports,
            environment=environment,
        )
        try:
            artifact = ModuleArtifact.from_dict(result["artifact"])
            modules = compiler.validate_closure([artifact])
            if not any(
                declaration.get("name") == _strip_root_prefix(name)
                and declaration.get("kind") == "theorem"
                for declaration in artifact.declarations
            ):
                raise ValueError(
                    "exported theorem identity is not declared by the proved root module"
                )
            statement = result.get("statement")
            if not isinstance(statement, str) or not statement.strip():
                raise ValueError("exported root requires its exact theorem statement")
            frozen = task.session.get("frozen_statement")
            if frozen is not None:
                if (
                    not isinstance(frozen, dict)
                    or frozen.get("name") != name
                    or frozen.get("statement") != statement
                ):
                    raise ValueError(
                        "exported result differs from the reviewed frozen statement"
                    )
                expected_statement = frozen.get("kernel_target")
                if not isinstance(
                    expected_statement, str
                ) or not is_valid_lean_qualified_name(expected_statement):
                    raise ValueError(
                        "frozen statement has no valid kernel target identity"
                    )
            else:
                expected_statement = statement
            # Recheck the requested theorem against its original compiled type,
            # not merely the existence of a name anywhere in imported Mathlib.
            # Only direct dependencies belong to the module's admission contract.
            _, manifest = compiler._load(artifact.module_name)
            dependencies = [
                compiler._load(module)[0] for module in manifest["dependencies"]
            ]
            checked = await compiler.compile(
                artifact.source_path.read_bytes().decode("utf-8"),
                dependencies=dependencies,
                expected_name=name,
                expected_statement=expected_statement,
            )
            if checked != artifact:
                raise ValueError(
                    "rechecked root theorem identity differs from admitted artifact"
                )
            _mkdir_durable(output.parent)
            with tempfile.TemporaryDirectory(
                prefix=".formalization-export-", dir=output.parent
            ) as temporary:
                stage = Path(temporary) / "bundle"
                stage.mkdir()
                records = []
                for module in modules:
                    stem = stage.joinpath(*module.module_name.split("."))
                    stem.parent.mkdir(parents=True, exist_ok=True)
                    source_path, olean_path = (
                        stem.with_suffix(".lean"),
                        stem.with_suffix(".olean"),
                    )
                    shutil.copyfile(module.source_path, source_path)
                    shutil.copyfile(module.olean_path, olean_path)
                    if (
                        hashlib.sha256(source_path.read_bytes()).hexdigest()
                        != module.source_sha256
                        or hashlib.sha256(olean_path.read_bytes()).hexdigest()
                        != module.olean_sha256
                    ):
                        raise ValueError("module changed while exporting")
                    record = module.to_dict()
                    record["source_path"] = str(source_path.relative_to(stage))
                    record["olean_path"] = str(olean_path.relative_to(stage))
                    records.append(record)
                sources = []
                with SourceLibrary(directory / "sources") as library:
                    cursor = ""
                    while page := library.list(limit=50, after=cursor):
                        for document in page:
                            # Labels are metadata, never filesystem paths.
                            path = stage / "sources" / f"{document.id}.txt"
                            path.parent.mkdir(exist_ok=True)
                            data = library.read(document.id).text.encode("utf-8")
                            path.write_bytes(data)
                            sources.append(
                                {
                                    "id": document.id,
                                    "name": document.name,
                                    "sha256": document.sha256,
                                    "path": str(path.relative_to(stage)),
                                }
                            )
                        cursor = page[-1].id
                root_source = f"import {artifact.module_name}\n\n#check {name}\n#print axioms {name}\n"
                (stage / "Root.lean").write_text(root_source, encoding="utf-8")
                runner = LeanRunner(
                    LeanConfig(
                        project_dir=str(environment.project_path),
                        scratch_dir=str(stage / ".checks"),
                        backend_mode="lake",
                        timeout_s=300,
                        module_search_paths=[str(stage)],
                    )
                )
                try:
                    returncode, diagnostics = await runner._run_via_lake(
                        stage / "Root.lean", timeout_s=300, extra_module_paths=[stage]
                    )
                    if returncode != 0:
                        raise ValueError(f"exported root import failed: {diagnostics}")
                finally:
                    await runner.aclose()
                environment.validate()
                current = store.get_task(task.id)
                if (
                    current.state != "verified"
                    or current.generation != generation
                    or current.result != result
                ):
                    raise ValueError(
                        "campaign root changed while exporting; retry from current generation"
                    )
                bundled_root = next(
                    record
                    for record in records
                    if record["module_name"] == artifact.module_name
                )
                receipt = {
                    "version": 1,
                    "status": "export_verified",
                    "module_count": len(modules),
                    "semantic_status": "machine_reviewed_not_certified",
                    "result": {**result, "artifact": bundled_root},
                    "origin_campaign": str(directory),
                    "root_generation": generation,
                    "goal": task.description,
                    "initial_goal": metadata["goal"],
                    "modules": records,
                    "sources": sources,
                    "environment": environment.to_dict(),
                    "lean_output": diagnostics,
                }
                _write_json(stage / "export.json", receipt)
                command = f"cd {shlex.quote(str(environment.project_path))}\nLEAN_PATH={shlex.quote(str(output.resolve()))} lake env lean {shlex.quote(str(output.resolve() / 'Root.lean'))}\n"
                (stage / "README.md").write_text(
                    "# Verified formalization source bundle\n\n"
                    "The Lean files are exact, separate dependency modules. Root.lean imports the proved theorem. "
                    "Original documents and environment fingerprints are recorded in export.json.\n\n"
                    "This is not a vendored Lake project: replay requires the recorded Lean toolchain, "
                    "Mathlib, and trusted project dependencies. Keep or recreate that environment first.\n\n"
                    "```sh\n" + command + "```\n\n"
                    "Lean verification certifies the formal theorem, not its equivalence to natural language; "
                    "the latter has machine review, not mathematical certification.\n",
                    encoding="utf-8",
                )
                _sync_bundle(stage)
                # Publish only complete, rechecked bundles. The dedicated lock
                # is outside the destination, which must remain nonexistent.
                import fcntl

                with (output.parent / f".{output.name}.export.lock").open("a+") as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX)
                    # Revisions acquire the same SQLite write reservation. Keep
                    # this transaction short: validation and copying are complete.
                    # No revision may slip between the final generation check and
                    # publication while another exporter holds the destination lock.
                    with store._transaction():
                        current = store.get_task(task.id)
                        if (
                            current.state != "verified"
                            or current.generation != generation
                            or current.result != result
                        ):
                            raise ValueError(
                                "campaign root changed while exporting; retry from current generation"
                            )
                        if output.exists() or output.is_symlink():
                            raise FileExistsError(
                                f"export destination already exists: {output}"
                            )
                        os.rename(stage, output)
                        _sync_directory(output.parent)
                return {
                    "status": "export_verified",
                    "output": str(output),
                    "module_count": len(modules),
                    "semantic_status": "machine_reviewed_not_certified",
                    "root": name,
                }
        finally:
            await compiler.close()
