"""Persisted NL translations and checked handoff to the proving project."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class NLResult:
    """Saved translation; typechecking does not establish semantic fidelity."""

    status: str
    output_dir: Path
    statement: str | None = None
    message: str = ""
    lean_sha256: str = ""
    input_sha256: str = ""
    project_path: Path | None = None
    definitions: tuple[str, ...] = ()
    preamble: str = ""
    context_sha256: str = ""

    @property
    def lean_file(self) -> Path:
        return self.output_dir / "Problem.lean"

    @property
    def input_file(self) -> Path:
        return self.output_dir / "problem.txt"

    @property
    def context_file(self) -> Path:
        return self.output_dir / "context.lean"


def _project_directory(path: Path) -> Path:
    resolved = path.expanduser().resolve(strict=True)
    if not resolved.is_dir():
        raise ValueError(f"formalization project is not a directory: {resolved}")
    return resolved


def validate_result(result: NLResult, project_path: Path) -> None:
    """Reject changed artifacts or a different/missing proving project.

    Project identity here is its resolved directory. Callers must recheck saved
    Lean source on reuse because project contents can change at that path.
    """
    if result.status != "formalized":
        raise ValueError("only a formalized result can enter proof search")
    if result.project_path is None:
        raise ValueError("formalization has no recorded project path")
    if _project_directory(project_path) != _project_directory(result.project_path):
        raise ValueError("proving project differs from the formalization project")
    files = [
        (result.lean_file, result.lean_sha256),
        (result.input_file, result.input_sha256),
    ]
    if result.context_sha256:
        files.append((result.context_file, result.context_sha256))
    elif result.context_file.exists():
        raise ValueError("formalization context has no recorded hash")
    for path, expected in files:
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(
                f"formalization files changed before prover handoff: {path.name}"
            )


def load_result(directory: Path) -> NLResult:
    """Load a completed translation and validate files without model access."""
    directory = directory.expanduser().resolve(strict=True)
    record = json.loads((directory / "formalization.json").read_text(encoding="utf-8"))
    if (
        not isinstance(record, dict)
        or not isinstance(record.get("schema_version"), int)
        or isinstance(record.get("schema_version"), bool)
    ):
        raise ValueError("invalid formalization record schema")
    if record["schema_version"] != 1 or record.get("status") != "formalized":
        raise ValueError("expected a schema-version-1 formalized record")
    for field in ("statement", "lean_sha256", "input_sha256", "project_path"):
        if not isinstance(record.get(field), str) or not record[field].strip():
            raise ValueError(f"formalization record requires a nonempty {field}")
    for field in ("message", "preamble", "context_sha256"):
        if not isinstance(record.get(field, ""), str):
            raise ValueError(f"formalization record {field} must be a string")
    if not Path(record["project_path"]).is_absolute():
        raise ValueError("formalization project path must be absolute")
    definitions = record.get("definitions", [])
    if not isinstance(definitions, list) or any(
        not isinstance(value, str) or not value.strip() for value in definitions
    ):
        raise ValueError("formalization definitions must be a list of strings")
    project = _project_directory(Path(record["project_path"]))
    result = NLResult(
        status="formalized",
        output_dir=directory,
        statement=record["statement"],
        message=record.get("message", ""),
        lean_sha256=record["lean_sha256"],
        input_sha256=record["input_sha256"],
        project_path=project,
        definitions=tuple(definitions),
        preamble=record.get("preamble", ""),
        context_sha256=record.get("context_sha256", ""),
    )
    validate_result(result, project)
    return result
