"""Inspect compiled declarations without elaborating an audit in candidate scope."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
import time
from typing import Mapping, Sequence

from .subprocess_environment import sanitized_subprocess_environment


# This program is elaborated in its own process, importing only trusted Lean
# code. The candidate is loaded as environment data, without its elaborator
# extensions. Candidate diagnostics never provide the audit result.
_AUDITOR = r'''
import Lean

def main (args : List String) : IO UInt32 := do
  let [directory, moduleText, targetJson] := args
    | throw <| IO.userError "expected directory, module and target"
  Lean.initSearchPath (← Lean.findSysroot) [System.FilePath.mk directory]
  let env ← Lean.importModules #[{module := Lean.Name.mkSimple moduleText}] {}
    (loadExts := false)
  let parsed ← IO.ofExcept (Lean.Json.parse targetJson)
  let parts ← IO.ofExcept parsed.getArr?
  let mut target := Lean.Name.anonymous
  for part in parts do
    target := Lean.Name.str target (← IO.ofExcept part.getStr?)
  unless (env.find? target).isSome do
    throw <| IO.userError "missing audited declaration"
  let (_, state) := ((Lean.CollectAxioms.collect target).run env).run {}
  IO.println <| (Lean.toJson (state.axioms.map Lean.Name.toString)).compress
  return 0
'''


def audit_compiled_source(
    content: str, name_parts: Sequence[str], *, project_dir: Path,
    scratch_dir: Path, timeout_s: float, env: Mapping[str, str],
) -> tuple[list[str] | None, str]:
    """Compile once and read the root's transitive axioms in a separate process.

    Missing artifacts (including an early successful compiler exit), missing
    declarations, malformed auditor output and timeouts all fail closed.
    Both processes share one wall-clock allowance.
    """
    deadline = time.monotonic() + max(1.0, timeout_s)
    scratch_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".compiled_audit_", dir=scratch_dir) as temporary:
        directory = Path(temporary).resolve()
        candidate = directory / "EnsembleAuditCandidate.lean"
        artifact = candidate.with_suffix(".olean")
        auditor = directory / "EnsembleAuditProgram.lean"
        candidate.write_text(content, encoding="utf-8")
        auditor.write_text(_AUDITOR, encoding="utf-8")

        def run(arguments: list[str]) -> subprocess.CompletedProcess[str]:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("compiled axiom audit deadline exhausted")
            return subprocess.run(
                ["lake", "env", "lean", *arguments], cwd=project_dir,
                env=sanitized_subprocess_environment(env),
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=remaining, check=False,
            )

        try:
            compiled = run(["-R", str(directory), "-o", str(artifact), str(candidate)])
            if compiled.returncode != 0 or not artifact.is_file():
                return None, compiled.stdout + "\ncompiled audit artifact unavailable"
            inspected = run([
                "--run", str(auditor), str(directory), candidate.stem,
                json.dumps(list(name_parts), ensure_ascii=False),
            ])
            if inspected.returncode != 0:
                return None, inspected.stdout
            axioms = json.loads(inspected.stdout)
            if type(axioms) is not list or any(type(name) is not str for name in axioms):
                return None, "invalid compiled axiom inventory"
            return list(dict.fromkeys(axioms)), inspected.stdout
        except (OSError, ValueError, subprocess.SubprocessError, TimeoutError) as error:
            return None, f"{type(error).__name__}: {error}"
