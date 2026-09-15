"""Original-target acceptance independent of research and candidate elaboration.

Compile the original proposition before candidate code can introduce instances
or notation. A separate host-owned kernel probe compares that definition's
value with the original theorem's type. Its temporary proof placeholder never
enters any admitted module or export.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
import uuid
from pathlib import Path
from typing import Any, TYPE_CHECKING

if TYPE_CHECKING:
    from ..formalization.lean import ModuleArtifact, ModuleCompiler
    from ..theorem_project import TheoremProblem
from .model import json_text


def _hash(value: str | bytes) -> str:
    return hashlib.sha256(
        value.encode() if isinstance(value, str) else value
    ).hexdigest()


def _value_probe(original: str, pin: str, nonce: str) -> str:
    return f"""import StrategyPinComparison
import Lean.Elab.Command

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← Lean.getConstInfo ({json.dumps(original)}.toName)
  let pin ← Lean.getConstInfo ({json.dumps(pin)}.toName)
  let .defnInfo pinDef := pin | Lean.throwError "pin must be a definition"
  let sourceType := original.type
  let pinValue := pinDef.value
  for e in [sourceType, pinDef.type, pinValue] do
    if e.hasMVar || e.hasFVar || e.hasLooseBVars || e.hasSorry || e.hasLevelMVar then
      Lean.throwError "unresolved pinned target"
  unless ← Lean.Meta.isDefEq pinDef.type (Lean.mkSort Lean.Level.zero) do
    Lean.throwError "pin must be a closed proposition"
  let sourceParams := (Lean.collectLevelParams {{}} sourceType).params.toList
  let pinParams := (Lean.collectLevelParams {{}} pinValue).params.toList
  unless sourceParams.length == pinParams.length do
    Lean.throwError "pin changed universe arity"
  let levels := sourceParams.map Lean.Level.param
  let sourceType := sourceType.instantiateLevelParams sourceParams levels
  let pinValue := pinValue.instantiateLevelParams pinParams levels
  unless ← Lean.Meta.isDefEq sourceType pinValue do
    Lean.throwError "pin value differs from exact original theorem type"
  let identity := Lean.mkLambda `h Lean.BinderInfo.default sourceType (Lean.mkBVar 0)
  let promised := Lean.mkForall `h Lean.BinderInfo.default sourceType pinValue
  Lean.Meta.checkWithKernel (Lean.mkLet `_pinChecked promised identity (Lean.mkBVar 0))
  Lean.logInfo {json.dumps(nonce)}
"""


async def capture_target(
    problem: TheoremProblem, compiler: ModuleCompiler
) -> dict[str, Any]:
    from ..formalization.documents import _mkdir_durable, _sync_directory
    from ..lean_runner import _free_universe_decl
    from ..theorem_project import (
        _active_command_scope_closers,
        decode_theorem_target_context,
        scan_lean_theorems,
        select_lean_theorem,
        theorem_reusable_preamble,
        theorem_type_probe_source,
    )

    declaration = select_lean_theorem(
        scan_lean_theorems(problem.raw_text), problem.theorem_name
    )
    probe = theorem_type_probe_source(problem.raw_text, declaration, problem.imports)
    ok, rendered, diagnostic = await compiler._runner.check_source_declaration_type(
        probe, problem.theorem_name, timeout_s=compiler.timeout_s, pp_explicit=True
    )
    if not ok:
        raise ValueError("cannot elaborate original target: " + diagnostic[-3000:])
    base, _ = theorem_reusable_preamble(problem.raw_text, declaration, problem.imports)
    _, scoped, omitted = decode_theorem_target_context(problem.lean_preamble)
    pin_name = "StrategyOriginalTarget_" + _hash(problem.raw_text)[:24]
    command = f"def _root_.{pin_name} : Prop := ({rendered})\n"
    if omitted:
        command = "omit " + " ".join(omitted) + " in\n" + command
    if scoped:
        command = scoped + "\n" + command
    universe = _free_universe_decl(rendered, declared_in=base)
    block = (universe + "\n" if universe else "") + command
    closers = "\n".join(
        _active_command_scope_closers(problem.raw_text, declaration.declaration_start)
    )
    source = base.rstrip() + "\n" + block + "\n" + closers + "\n"
    # The exact pin block precedes the source theorem's attributes/instances.
    prefix = base.rstrip()
    if not probe.startswith(prefix):
        raise ValueError("original target probe prefix changed")
    comparison = prefix + "\n" + block + "\n" + probe[len(prefix) :]
    nonce = "PIN_VALUE_CHECKED_" + uuid.uuid4().hex
    inspection = _value_probe(problem.theorem_name, pin_name, nonce)
    with tempfile.TemporaryDirectory(prefix="ensemble-pin-audit-") as raw:
        directory = Path(raw)
        module = directory / "StrategyPinComparison.lean"
        module.write_text(comparison, encoding="utf-8")
        code, output = await compiler._runner._run_via_lake(
            module,
            timeout_s=compiler.timeout_s,
            output_path=module.with_suffix(".olean"),
            extra_module_paths=(directory,),
        )
        if code:
            raise ValueError("original target comparison failed: " + output[-3000:])
        audit = directory / "Inspect.lean"
        audit.write_text(inspection, encoding="utf-8")
        code, output = await compiler._runner._run_via_lake(
            audit, timeout_s=compiler.timeout_s, extra_module_paths=(directory,)
        )
        if code or nonce not in output:
            raise ValueError("original target value audit failed: " + output[-3000:])
    artifact = await compiler.compile(source, expected_name=pin_name)
    record = {
        "schema": 1,
        "original_source_sha256": _hash(problem.raw_text),
        "theorem_name": problem.theorem_name,
        "statement": rendered,
        "pin_name": pin_name,
        "pin_source": source,
        "pin_source_sha256": _hash(source),
        "environment_id": compiler.environment.id,
        "comparison_sha256": _hash(comparison),
        "inspection_sha256": _hash(inspection),
        "inspection_receipt": nonce,
        "artifact": artifact.to_dict(),
    }
    record["binding"] = _hash(
        json_text({key: value for key, value in record.items() if key != "artifact"})
    )
    directory = compiler.root / "Formalization" / ".target-captures"
    _mkdir_durable(directory)
    manifest = directory / (record["binding"] + ".json")
    # Published only by this host operation after both kernel probes and module
    # admission. This is an owner manifest, like ModuleCompiler's admission
    # manifests, not a receipt supplied by a model or accepted from metadata.
    provenance = {
        "record": record,
        "original_source": problem.raw_text,
        "imports": list(problem.imports),
        "comparison": comparison,
        "inspection": inspection,
        "inspection_output": output,
    }
    with manifest.open("xb") as handle:
        handle.write(json_text(provenance).encode())
        handle.flush()
        os.fsync(handle.fileno())
    _sync_directory(directory)
    return record


def validate_pin(
    pin: dict[str, Any], compiler: ModuleCompiler, *, capture_root: Path | None = None
) -> None:
    if (
        pin.get("schema") != 1
        or pin["environment_id"] != compiler.environment.id
        or _hash(pin["pin_source"]) != pin["pin_source_sha256"]
        or _hash(
            json_text(
                {
                    key: value
                    for key, value in pin.items()
                    if key not in {"binding", "artifact"}
                }
            )
        )
        != pin["binding"]
    ):
        raise ValueError("original target binding changed")
    validate_capture(
        pin, compiler.environment, capture_root=capture_root or compiler.root
    )


def validate_capture(
    pin: dict[str, Any], environment: Any, *, capture_root: Path
) -> None:
    """Check host-issued capture authority, independently of supplied hashes.

    Capture storage has the same owner-only trust boundary as admitted Lean
    module manifests. Callers cannot turn a candidate JSON record into one.
    """
    from ..formalization.lean import ModuleArtifact, ModuleCompiler

    try:
        binding = pin["binding"]
        if not isinstance(binding, str) or not re.fullmatch(r"[0-9a-f]{64}", binding):
            raise ValueError("invalid original capture identity")
        artifact = ModuleArtifact.from_dict(pin["artifact"])
        root = capture_root.resolve()
        if artifact.source_path.parent.parent.resolve() != root:
            raise ValueError("capture is outside the fixed owner registry")
        manifest = root / "Formalization" / ".target-captures" / (binding + ".json")
        captured = json.loads(manifest.read_bytes())
        if (
            captured["record"] != pin
            or _hash(captured["original_source"]) != pin["original_source_sha256"]
            or _hash(captured["comparison"]) != pin["comparison_sha256"]
            or _hash(captured["inspection"]) != pin["inspection_sha256"]
            or pin["inspection_receipt"] not in captured["inspection_output"]
            or artifact.source_sha256 != pin["pin_source_sha256"]
        ):
            raise ValueError("original capture provenance changed")
        owner = ModuleCompiler(
            environment.project_path,
            root,
            trusted_imports=environment.trusted_imports,
            environment=environment,
        )
        owner.validate_closure([artifact])
    except (KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        raise ValueError("original target has no valid owner capture") from exc


async def check_candidate(
    pin: dict[str, Any],
    compiler: ModuleCompiler,
    candidate: ModuleArtifact,
    name: str,
    *,
    polarity: str,
    capture_root: Path | None = None,
) -> dict[str, Any]:
    from ..theorem_project import is_valid_lean_qualified_name

    validate_pin(pin, compiler, capture_root=capture_root)
    if polarity not in {"prove", "refute"} or not is_valid_lean_qualified_name(name):
        raise ValueError("invalid original target candidate or polarity")
    original = await compiler.compile(pin["pin_source"], expected_name=pin["pin_name"])
    target = pin["pin_name"] if polarity == "prove" else "Not " + pin["pin_name"]
    wrapper_name = (
        "StrategyOriginalAccepted_" + _hash(candidate.source_sha256 + polarity)[:24]
    )
    source = f"import {original.module_name}\nimport {candidate.module_name}\ntheorem {wrapper_name} : ({target}) := by\n  exact @_root_.{name}\n"
    try:
        wrapper = await compiler.compile(
            source,
            dependencies=[original, candidate],
            expected_name=wrapper_name,
            expected_statement=target,
        )
    except ValueError as exc:
        raise ValueError(
            "candidate does not prove the original target: " + str(exc)
        ) from exc
    return {
        "pin_binding": pin["binding"],
        "pin_artifact": original.to_dict(),
        "wrapper": wrapper.to_dict(),
        "wrapper_name": wrapper_name,
        "wrapper_statement": target,
        "candidate": candidate.to_dict(),
        "candidate_name": name,
        "polarity": polarity,
    }


def validate_acceptance(
    pin: dict[str, Any],
    compiler: ModuleCompiler,
    receipt: dict[str, Any],
    candidate: ModuleArtifact,
    name: str,
    polarity: str,
    *,
    capture_root: Path | None = None,
) -> list[ModuleArtifact]:
    """Read-time validation of the exact, previously kernel-checked wrapper."""
    from ..formalization.lean import ModuleArtifact

    validate_pin(pin, compiler, capture_root=capture_root)
    if (
        receipt.get("pin_binding") != pin["binding"]
        or receipt.get("candidate") != candidate.to_dict()
        or receipt.get("candidate_name") != name
        or receipt.get("polarity") != polarity
    ):
        raise ValueError("original target acceptance binding changed")
    original = ModuleArtifact.from_dict(receipt["pin_artifact"])
    wrapper = ModuleArtifact.from_dict(receipt["wrapper"])
    if original.source_sha256 != pin["pin_source_sha256"]:
        raise ValueError("original target module changed")
    target = pin["pin_name"] if polarity == "prove" else "Not " + pin["pin_name"]
    wrapper_name = (
        "StrategyOriginalAccepted_" + _hash(candidate.source_sha256 + polarity)[:24]
    )
    source = f"import {original.module_name}\nimport {candidate.module_name}\ntheorem {wrapper_name} : ({target}) := by\n  exact @_root_.{name}\n"
    if (
        wrapper.source_sha256 != _hash(source)
        or receipt.get("wrapper_name") != wrapper_name
        or receipt.get("wrapper_statement") != target
    ):
        raise ValueError("original target wrapper changed")
    closure = compiler.validate_closure([wrapper])
    if original not in closure or candidate not in closure:
        raise ValueError("original target acceptance closure is incomplete")
    return closure
