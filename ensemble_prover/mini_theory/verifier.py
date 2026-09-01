"""Independent Lean compilation and axiom audit for Mini theory bundles."""

from __future__ import annotations

import os
import hashlib
import hmac
import json
import re
import secrets
import signal
import shutil
import subprocess
import tempfile
import threading
import time
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Mapping, Optional, Sequence

from .model import (
    TheoryBundleCandidate,
    TheoryDeclaration,
    TheoryVerificationReceipt,
    content_hash,
)
from .environment import dependency_environment_fingerprint
from .policy import TheoryPolicy
from .store import TheoryStore
from ..theorem_project import _mask_noncode
from ..subprocess_environment import sanitized_subprocess_environment


_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:protected|noncomputable)\s+)*"
    r"(?P<kind>def|abbrev|structure|class|inductive|instance|theorem|lemma)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
_NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
_SECTION_RE = re.compile(
    r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$"
)
_MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
_END_RE = re.compile(
    r"^\s*end(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
_PRINT_AXIOMS_DEPENDS_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]"
)
_PRINT_AXIOMS_NONE_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms"
)
_ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_CIRCULAR_PREMISE_MARKER_RE = re.compile(
    r"MINI_THEORY_CIRCULAR_PREMISE:([^\s]+)"
)
_FORBIDDEN_PREMISE_MARKER_RE = re.compile(
    r"MINI_THEORY_FORBIDDEN_PREMISE:([^:\s]+):([^\s]+)"
)
_NAMESPACE_FORBIDDEN_AXIOM_MARKER_RE = re.compile(
    r"MINI_THEORY_NS_FORBIDDEN_AXIOM:([^\s]+):([^\s]+)"
)


@dataclass(frozen=True)
class TheoryVerificationResult:
    receipt: TheoryVerificationReceipt
    compiled_artifact: bytes = b""
    compile_output: str = ""
    audit_output: str = ""
    # Filled only by the independent verifier. Publication validates this
    # seal again at the persistence boundary.
    publication_seal: str = ""

    @property
    def accepted(self) -> bool:
        return bool(self.receipt.accepted)


class TheoryBundleVerifier:
    """Compile candidates outside the active theorem preamble and fail closed."""

    def __init__(
        self,
        *,
        lean_project_dir: Path,
        store: TheoryStore,
        policy: Optional[TheoryPolicy] = None,
        timeout_s: float = 180.0,
        environment: Optional[Mapping[str, str]] = None,
    ) -> None:
        self.lean_project_dir = Path(lean_project_dir).resolve()
        self.store = store
        self.policy = policy or TheoryPolicy()
        self.timeout_s = max(1.0, float(timeout_s or 180.0))
        self.environment = dict(environment or {})
        self.__publication_secret = secrets.token_bytes(32)

    def verify(
        self,
        candidate: TheoryBundleCandidate,
        *,
        cancellation_event: Optional[threading.Event] = None,
        forbidden_target_statements: Sequence[str] = (),
    ) -> TheoryVerificationResult:
        policy_verdict = self.policy.evaluate(
            candidate.source,
            declared_imports=candidate.imports,
        )
        if not policy_verdict.accepted:
            return self._rejected(
                candidate,
                "policy_rejected:" + ",".join(policy_verdict.reasons),
            )
        dependency_error = self._dependency_error(candidate)
        if dependency_error:
            return self._rejected(candidate, dependency_error)
        declarations = self._candidate_declarations(candidate)
        if not declarations:
            return self._rejected(candidate, "no_named_declarations")
        namespace_escape = self._namespace_escape_error(declarations)
        if namespace_escape:
            return self._rejected(candidate, namespace_escape)
        forbidden_targets = tuple(
            dict.fromkeys(
                str(statement or "").strip()
                for statement in forbidden_target_statements
                if str(statement or "").strip()
            )
        )
        for index, forbidden_target in enumerate(forbidden_targets):
            target_policy = self.policy.evaluate(
                f"def miniTheoryForbiddenTarget{index} : Prop := ({forbidden_target})",
                declared_imports=(),
            )
            if not target_policy.accepted:
                return self._rejected(
                    candidate,
                    "forbidden_target_policy_rejected:"
                    + ",".join(target_policy.reasons),
                )
        environment_result = self._lean_environment(cancellation_event)
        if isinstance(environment_result, str):
            return self._rejected(candidate, environment_result)
        lean_executable, base_lean_path = environment_result

        with tempfile.TemporaryDirectory(prefix="mini_theory_verify.") as scratch_raw:
            scratch = Path(scratch_raw)
            stage_modules = scratch / "modules"
            source_path = stage_modules.joinpath(*candidate.module_name.split(".")).with_suffix(
                ".lean"
            )
            artifact_path = source_path.with_suffix(".olean")
            source_path.parent.mkdir(parents=True, exist_ok=True)
            source_path.write_text(candidate.source.rstrip() + "\n", encoding="utf-8")
            materialization_error = self._materialize_dependencies(
                candidate,
                stage_modules=stage_modules,
            )
            if materialization_error:
                return self._rejected(candidate, materialization_error)
            lean_path = os.pathsep.join(
                part
                for part in (
                    str(stage_modules),
                    str(self.store.modules_root),
                    base_lean_path,
                )
                if part
            )
            env = os.environ.copy()
            env.update(self.environment)
            env["LEAN_PATH"] = lean_path
            compile_run = self._run(
                [
                    str(lean_executable),
                    "-R",
                    str(stage_modules),
                    "-o",
                    str(artifact_path),
                    str(source_path),
                ],
                env=env,
                cancellation_event=cancellation_event,
            )
            compile_output = self._combined_output(compile_run)
            if compile_run.returncode != 0 or not artifact_path.is_file():
                return self._rejected(
                    candidate,
                    "lean_compile_failed",
                    compile_output=compile_output,
                )

            fq_declarations = declarations
            audit_source = self._audit_source(
                candidate.module_name,
                fq_declarations,
                forbidden_target_statements=forbidden_targets,
                namespace=candidate.namespace,
            )
            audit_path = scratch / "Audit.lean"
            audit_path.write_text(audit_source, encoding="utf-8")
            audit_run = self._run(
                [str(lean_executable), "-R", str(scratch), str(audit_path)],
                env=env,
                cancellation_event=cancellation_event,
            )
            audit_output = self._combined_output(audit_run)
            if audit_run.returncode != 0:
                return self._rejected(
                    candidate,
                    "lean_audit_failed",
                    compile_output=compile_output,
                    audit_output=audit_output,
                )
            circular_declarations = tuple(
                dict.fromkeys(
                    match.group(1).strip()
                    for match in _CIRCULAR_PREMISE_MARKER_RE.finditer(audit_output)
                    if match.group(1).strip()
                )
            )
            if circular_declarations:
                return self._rejected(
                    candidate,
                    "circular_premise_conclusion:"
                    + ",".join(circular_declarations),
                    compile_output=compile_output,
                    audit_output=audit_output,
                )
            forbidden_premises = tuple(
                dict.fromkeys(
                    (match.group(1).strip(), match.group(2).strip())
                    for match in _FORBIDDEN_PREMISE_MARKER_RE.finditer(audit_output)
                    if match.group(1).strip() and match.group(2).strip()
                )
            )
            if forbidden_premises:
                return self._rejected(
                    candidate,
                    "need_relative_circular_premise:"
                    + ",".join(
                        declaration_name
                        for declaration_name, _target_name in forbidden_premises
                    ),
                    compile_output=compile_output,
                    audit_output=audit_output,
                )
            declaration_records, audit_error = self._parse_audit(
                fq_declarations,
                audit_output,
            )
            if audit_error:
                return self._rejected(
                    candidate,
                    audit_error,
                    compile_output=compile_output,
                    audit_output=audit_output,
                )
            # Fail-closed backstop, checked after the precise per-declaration
            # audit: reject any constant Lean elaborated under the bundle
            # namespace whose axiom closure escaped the allowlist but which the
            # name parser never listed (e.g. a declaration hidden by a
            # partial-width `end`).  For parser-visible declarations the
            # per-declaration `unexpected_axioms` diagnostic above fires first.
            namespace_forbidden_axioms = tuple(
                dict.fromkeys(
                    (match.group(1).strip(), match.group(2).strip())
                    for match in (
                        _NAMESPACE_FORBIDDEN_AXIOM_MARKER_RE.finditer(audit_output)
                    )
                    if match.group(1).strip() and match.group(2).strip()
                )
            )
            if namespace_forbidden_axioms:
                return self._rejected(
                    candidate,
                    "namespace_forbidden_axiom:"
                    + ",".join(
                        f"{declaration_name}:{axiom_name}"
                        for declaration_name, axiom_name in namespace_forbidden_axioms
                    ),
                    compile_output=compile_output,
                    audit_output=audit_output,
                )
            artifact = artifact_path.read_bytes()
            verification_output = f"{compile_output}\n{audit_output}".strip()
            receipt = TheoryVerificationReceipt(
                accepted=True,
                bundle_id=candidate.bundle_id,
                module_name=candidate.module_name,
                source_hash=candidate.source_hash,
                declarations=tuple(declaration_records),
                lean_toolchain=self._lean_toolchain(),
                mathlib_revision=self._mathlib_revision(cancellation_event),
                verification_output_hash=content_hash(
                    verification_output,
                    length=64,
                ),
                compiled_artifact_hash=content_hash(artifact, length=64),
                diagnostic="verified",
            )
            result = TheoryVerificationResult(
                receipt=receipt,
                compiled_artifact=artifact,
                compile_output=compile_output,
                audit_output=audit_output,
            )
            return replace(
                result,
                publication_seal=self.__publication_seal(candidate, result),
            )

    def validates_publication(
        self,
        candidate: TheoryBundleCandidate,
        verification: TheoryVerificationResult,
    ) -> bool:
        """Return whether this exact verifier issued the accepted result."""

        return bool(
            verification.accepted
            and verification.publication_seal
            and hmac.compare_digest(
                verification.publication_seal,
                self.__publication_seal(candidate, verification),
            )
        )

    def __publication_seal(
        self,
        candidate: TheoryBundleCandidate,
        verification: TheoryVerificationResult,
    ) -> str:
        payload = json.dumps(
            {
                "candidate": candidate.to_dict(include_source=True),
                "receipt": verification.receipt.to_dict(),
                "artifact_hash": hashlib.sha256(
                    verification.compiled_artifact
                ).hexdigest(),
                "compile_output_hash": hashlib.sha256(
                    verification.compile_output.encode("utf-8")
                ).hexdigest(),
                "audit_output_hash": hashlib.sha256(
                    verification.audit_output.encode("utf-8")
                ).hexdigest(),
            },
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        return hmac.new(
            self.__publication_secret,
            payload,
            hashlib.sha256,
        ).hexdigest()

    def _dependency_error(self, candidate: TheoryBundleCandidate) -> str:
        available = {bundle.bundle_id: bundle for bundle in self.store.iter_bundles()}
        missing = [
            bundle_id
            for bundle_id in candidate.dependency_bundle_ids
            if bundle_id not in available
        ]
        if missing:
            return "missing_dependency_bundles:" + ",".join(missing)
        dependency_modules = {
            available[bundle_id].module_name
            for bundle_id in candidate.dependency_bundle_ids
        }
        if not dependency_modules.issubset(set(candidate.imports)):
            return "dependency_import_mismatch"
        undeclared_theory_imports = sorted(
            module
            for module in candidate.imports
            if module.startswith("MiniTheory.")
            and module not in dependency_modules
        )
        if undeclared_theory_imports:
            return "undeclared_theory_dependencies:" + ",".join(
                undeclared_theory_imports
            )
        return ""

    def _materialize_dependencies(
        self,
        candidate: TheoryBundleCandidate,
        *,
        stage_modules: Path,
    ) -> str:
        if not candidate.dependency_bundle_ids:
            return ""
        available = {bundle.bundle_id: bundle for bundle in self.store.iter_bundles()}
        pending = list(candidate.dependency_bundle_ids)
        visited: set[str] = set()
        while pending:
            bundle_id = pending.pop()
            if bundle_id in visited:
                continue
            bundle = available.get(bundle_id)
            if bundle is None:
                return f"missing_dependency_bundle_artifact:{bundle_id}"
            source_artifact = self.store.artifact_path(bundle)
            if not source_artifact.is_file():
                return f"missing_dependency_bundle_artifact:{bundle_id}"
            target_artifact = stage_modules.joinpath(
                *bundle.module_name.split(".")
            ).with_suffix(".olean")
            target_artifact.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_artifact, target_artifact)
            visited.add(bundle_id)
            pending.extend(bundle.dependency_bundle_ids)
        return ""

    def _lean_environment(
        self,
        cancellation_event: Optional[threading.Event] = None,
    ) -> tuple[Path, str] | str:
        if not self.lean_project_dir.is_dir():
            return "lean_project_missing"
        env = os.environ.copy()
        env.update(self.environment)
        lean_run = self._run(
            ["lake", "env", "which", "lean"],
            env=env,
            cancellation_event=cancellation_event,
        )
        path_run = self._run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            env=env,
            cancellation_event=cancellation_event,
        )
        lean_path = Path(lean_run.stdout.strip())
        if lean_run.returncode != 0 or not lean_path.is_file():
            return "lean_executable_unavailable"
        if path_run.returncode != 0 or not path_run.stdout.strip():
            return "lean_path_unavailable"
        return lean_path, path_run.stdout.strip()

    def _run(
        self,
        command: Sequence[str],
        *,
        env: Mapping[str, str],
        cancellation_event: Optional[threading.Event] = None,
        cwd: Optional[Path] = None,
    ) -> subprocess.CompletedProcess[str]:
        try:
            process = subprocess.Popen(
                list(command),
                cwd=cwd or self.lean_project_dir,
                env=sanitized_subprocess_environment(env),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
        except OSError as exc:
            return subprocess.CompletedProcess(
                list(command),
                127,
                stdout="",
                stderr=f"{type(exc).__name__}: {exc}",
            )
        deadline = time.monotonic() + self.timeout_s
        while True:
            cancelled = bool(cancellation_event and cancellation_event.is_set())
            remaining = deadline - time.monotonic()
            if cancelled or remaining <= 0:
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except (OSError, ProcessLookupError):
                    pass
                try:
                    stdout, stderr = process.communicate(timeout=1.0)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except (OSError, ProcessLookupError):
                        pass
                    stdout, stderr = process.communicate()
                reason = "cancelled" if cancelled else f"timeout after {self.timeout_s}s"
                return subprocess.CompletedProcess(
                    list(command),
                    130 if cancelled else 124,
                    stdout=stdout or "",
                    stderr=f"{reason}\n{stderr or ''}",
                )
            try:
                stdout, stderr = process.communicate(timeout=min(0.1, remaining))
            except subprocess.TimeoutExpired:
                continue
            return subprocess.CompletedProcess(
                list(command),
                process.returncode,
                stdout=stdout or "",
                stderr=stderr or "",
            )

    @staticmethod
    def _combined_output(run: subprocess.CompletedProcess[str]) -> str:
        return "\n".join(
            part.strip() for part in (run.stdout, run.stderr) if str(part or "").strip()
        )

    @staticmethod
    def _candidate_declarations(
        candidate: TheoryBundleCandidate,
    ) -> tuple[tuple[str, str], ...]:
        # Track the active namespace segments as a FLAT stack.  Lean closes a
        # scope by matching `end NAME` against the *trailing* open namespace
        # segments and pops exactly those, one `end` at a time — so
        # `namespace Inner.Deep` followed by `end Deep` pops only `Deep` and
        # leaves `Inner` open.  Modelling `namespace A.B` as a single fixed
        # width popped whole on any `end` desynchronises from Lean and can
        # mis-name (and thereby drop from the audit) a later declaration;
        # see the namespace axiom backstop for the fail-closed guarantee.
        namespaces: list[str] = []
        declarations: list[tuple[str, str]] = []
        for line in _mask_noncode(candidate.source).splitlines():
            namespace_match = _NAMESPACE_RE.match(line)
            if namespace_match is not None:
                namespaces.extend(namespace_match.group(1).split("."))
                continue
            if _SECTION_RE.match(line) is not None:
                continue
            if _MUTUAL_RE.match(line) is not None:
                continue
            end_match = _END_RE.match(line)
            if end_match is not None:
                end_name = end_match.group("name")
                if end_name:
                    end_segments = end_name.split(".")
                    # Only pop when the `end` names the trailing open
                    # namespace; a named `section`/`mutual` end (whose label
                    # is not a namespace) leaves the namespace stack intact.
                    width = len(end_segments)
                    if namespaces[-width:] == end_segments:
                        del namespaces[-width:]
                # An anonymous `end` closes a `section`/`mutual`, which never
                # contributes namespace segments; nothing to pop.
                continue
            declaration_match = _DECL_RE.match(line)
            if declaration_match is None:
                continue
            name = declaration_match.group("name")
            # Lean names a declaration by joining every active namespace with
            # the (possibly dotted) declared name.  A dotted name must NOT be
            # taken verbatim: `theorem Nat.add_comm` inside the bundle
            # namespace declares `<bundle>.Nat.add_comm`, and auditing the
            # bare name would resolve to a colliding global constant instead
            # of the bundle's own declaration.
            fq_name = ".".join((*namespaces, name))
            declarations.append((declaration_match.group("kind"), fq_name))
        return tuple(dict.fromkeys(declarations))

    @staticmethod
    def _namespace_escape_error(
        declarations: Sequence[tuple[str, str]],
    ) -> str:
        """Reject `_root_.`-anchored names that escape the bundle namespace.

        A leading `_root_` segment makes Lean install the declaration at the
        global root, outside the bundle sandbox, so the namespaced audit
        target could never resolve to it.  Matching `_root_` in ANY segment
        position is deliberately stricter than Lean's leading-only escape
        semantics: a mid-name `_root_` segment has no legitimate use in
        generated theory and rejecting it fails closed.
        """

        escaping = tuple(
            fq_name
            for _kind, fq_name in declarations
            if "_root_" in fq_name.split(".")
        )
        if escaping:
            return "namespace_escaping_declaration:" + ",".join(escaping)
        return ""

    @staticmethod
    def _audit_source(
        module_name: str,
        declarations: Sequence[tuple[str, str]],
        *,
        forbidden_target_statements: Sequence[str] = (),
        namespace: str = "",
    ) -> str:
        lines = [
            f"import {module_name}",
            "",
        ]
        forbidden_names: list[str] = []
        for index, statement in enumerate(forbidden_target_statements):
            name = f"miniTheoryForbiddenTarget{index}"
            forbidden_names.append(name)
            lines.append(f"private def {name} : Prop := ({statement})")
        lines.extend([
            "",
            "open Lean Meta Elab Command",
            "",
            "private def miniTheoryPushEvidence",
            "    (known : Array Expr) (candidate : Expr) : MetaM (Array Expr) := do",
            "  let candidateType ← inferType candidate",
            "  let candidateIsProp ← isProp candidateType",
            "  for prior in known do",
            "    let duplicate ←",
            "      if candidateIsProp then",
            "        isDefEq candidateType (← inferType prior)",
            "      else",
            "        isDefEq candidate prior",
            "    if duplicate then",
            "      return known",
            "  return known.push candidate",
            "",
            "private def miniTheoryEvidenceClosure",
            "    (seeds : Array Expr) (maxEvidence : Nat := 4096) :",
            "    MetaM (Array Expr × Bool) := do",
            "  let mut known := seeds",
            "  known ← miniTheoryPushEvidence known (mkConst ``True.intro)",
            "  let mut cursor := 0",
            "  while cursor < known.size do",
            "    if cursor >= maxEvidence then",
            "      return (known, true)",
            "    let evidence := known[cursor]!",
            "    cursor := cursor + 1",
            "    let evidenceType ← whnf (← inferType evidence)",
            "    match evidenceType with",
            "    | .forallE _ domain _ _ =>",
            "        for candidate in known do",
            "          if ← isDefEq (← inferType candidate) domain then",
            "            let application := mkApp evidence candidate",
            "            if ← isProp (← inferType application) then",
            "              known ← miniTheoryPushEvidence known application",
            "        try",
            "          let nonempty ← synthInstance",
            "            (mkApp (mkConst ``Nonempty) domain)",
            "          let argument ← mkAppM ``Classical.choice #[nonempty]",
            "          let application := mkApp evidence argument",
            "          if ← isProp (← inferType application) then",
            "            known ← miniTheoryPushEvidence known application",
            "        catch _ => pure ()",
            "    | _ => pure ()",
            "    for function in known do",
            "      let functionType ← whnf (← inferType function)",
            "      match functionType with",
            "      | .forallE _ domain _ _ =>",
            "          if ← isDefEq evidenceType domain then",
            "            let application := mkApp function evidence",
            "            if ← isProp (← inferType application) then",
            "              known ← miniTheoryPushEvidence known application",
            "      | _ => pure ()",
            "    let .const declName _ := evidenceType.getAppFn | continue",
            "    let some structureInfo := getStructureInfo? (← getEnv) declName",
            "      | continue",
            "    for fieldName in structureInfo.fieldNames do",
            "      try",
            "        let projection ← mkAppM fieldName #[evidence]",
            "        known ← miniTheoryPushEvidence known projection",
            "      catch _ => pure ()",
            "  return (known, false)",
            "",
            "private def miniTheoryClosureContains",
            "    (known : Array Expr) (forbidden : Expr) : MetaM Bool := do",
            "  for evidence in known do",
            "    let evidenceType ← inferType evidence",
            "    if (← isProp evidenceType) && (← isDefEq evidenceType forbidden) then",
            "      return true",
            "  return false",
            "",
            "private def miniTheoryStateTypes (xs : Array Expr) : MetaM (Array Expr) := do",
            "  xs.mapM fun x => do whnf (← inferType x)",
            "",
            "private def miniTheorySameState",
            "    (left right : Array Expr) : MetaM Bool := do",
            "  if left.size != right.size then",
            "    return false",
            "  let mut matched := Array.replicate right.size false",
            "  for lhs in left do",
            "    let mut found := false",
            "    for j in [0:right.size] do",
            "      if matched[j]! then",
            "        continue",
            "      if ← isDefEq lhs right[j]! then",
            "        matched := matched.set! j true",
            "        found := true",
            "        break",
            "    if !found then",
            "      return false",
            "  return true",
            "",
            "private partial def miniTheoryCollectDataTerms",
            "    (expression : Expr) (known : Array Expr := #[])",
            "    (remainingWork : Nat := 4096) : MetaM (Array Expr × Bool) := do",
            "  if remainingWork == 0 then",
            "    return (known, true)",
            "  let expression ← whnf expression",
            "  let mut known := known",
            "  for argument in expression.getAppArgs do",
            "    try",
            "      let argumentType ← inferType argument",
            "      let normalizedType ← whnf argumentType",
            "      if !(← isProp argumentType) then",
            "        match normalizedType with",
            "        | .sort _ => pure ()",
            "        | _ => known ← miniTheoryPushEvidence known argument",
            "      let (expanded, exhausted) ← miniTheoryCollectDataTerms",
            "        argument known (remainingWork - 1)",
            "      if exhausted then",
            "        return (expanded, true)",
            "      known := expanded",
            "    catch _ =>",
            "      return (known, true)",
            "  return (known, false)",
            "",
            "private partial def miniTheoryPremisesDeriveForbidden",
            "    (xs : Array Expr) (forbidden : Expr)",
            "    (visited : Array (Array Expr) := #[])",
            "    (remainingWork : Nat := 4096) : MetaM Bool := do",
            "  if remainingWork == 0 then",
            "    return true",
            "  let stateTypes ← miniTheoryStateTypes xs",
            "  for prior in visited do",
            "    if ← miniTheorySameState stateTypes prior then",
            "      return true",
            "  let visited := visited.push stateTypes",
            "  let mut baseline : Array Expr := #[]",
            "  let mut withPremises : Array Expr := #[]",
            "  let (targetData, targetDataExhausted) ←",
            "    miniTheoryCollectDataTerms forbidden",
            "  if targetDataExhausted then",
            "    return true",
            "  for targetDatum in targetData do",
            "    baseline ← miniTheoryPushEvidence baseline targetDatum",
            "    withPremises ← miniTheoryPushEvidence withPremises targetDatum",
            "  for x in xs do",
            "    let xType ← inferType x",
            "    let (binderData, binderDataExhausted) ←",
            "      miniTheoryCollectDataTerms xType",
            "    if binderDataExhausted then",
            "      return true",
            "    for datum in binderData do",
            "      baseline ← miniTheoryPushEvidence baseline datum",
            "      withPremises ← miniTheoryPushEvidence withPremises datum",
            "    withPremises := withPremises.push x",
            "    if !(← isProp xType) then",
            "      baseline := baseline.push x",
            "  let (baselineClosure, baselineExhausted) ←",
            "    miniTheoryEvidenceClosure baseline",
            "  if baselineExhausted then",
            "    return true",
            "  if ← miniTheoryClosureContains baselineClosure forbidden then",
            "    return false",
            "  let (premiseClosure, premiseExhausted) ←",
            "    miniTheoryEvidenceClosure withPremises",
            "  if premiseExhausted then",
            "    return true",
            "  if ← miniTheoryClosureContains premiseClosure forbidden then",
            "    return true",
            "  for premise in xs do",
            "    let premiseType ← whnf (← inferType premise)",
            "    if !(← isProp premiseType) then",
            "      continue",
            "    let .const declName levels := premiseType.getAppFn | continue",
            "    let some (.inductInfo info) := (← getEnv).find? declName",
            "      | continue",
            "    if info.ctors.isEmpty then",
            "      return true",
            "    let premiseArgs := premiseType.getAppArgs",
            "    let surrounding := xs.filter fun candidate => candidate != premise",
            "    let mut allConstructorsDerive := true",
            "    for ctorName in info.ctors do",
            "      let ctorInfo ← getConstInfoCtor ctorName",
            "      if premiseArgs.size < ctorInfo.numParams then",
            "        allConstructorsDerive := false",
            "        continue",
            "      let ctorType ← instantiateForall",
            "        (ctorInfo.type.instantiateLevelParams ctorInfo.levelParams levels)",
            "        (premiseArgs.extract 0 ctorInfo.numParams)",
            "      let ctorDerives ← forallTelescopeReducing ctorType fun ctorXs ctorResult => do",
            "        if ← isDefEq ctorResult premiseType then",
            "          return ← miniTheoryPremisesDeriveForbidden",
            "            (surrounding.append ctorXs) forbidden visited (remainingWork - 1)",
            "        let mut generalizedPremise := premiseType",
            "        let mut generalizedResult := ctorResult",
            "        for fvarId in (← getLCtx).getFVarIds do",
            "          if generalizedPremise.containsFVar fvarId then",
            "            let fvar := mkFVar fvarId",
            "            let replacement ← mkFreshExprMVar (← inferType fvar)",
            "            generalizedPremise := generalizedPremise.replaceFVar fvar replacement",
            "            generalizedResult := generalizedResult.replaceFVar fvar replacement",
            "        if !(← isDefEq generalizedResult generalizedPremise) then",
            "          return true",
            "        return false",
            "      if !ctorDerives then",
            "        allConstructorsDerive := false",
            "    if allConstructorsDerive then",
            "      return true",
            "  return false",
            "",
            "private def miniTheoryHasCircularPremise (declName : Name) : MetaM Bool := do",
            "  let info ← getConstInfo declName",
            "  forallTelescopeReducing info.type fun xs body => do",
            "    miniTheoryPremisesDeriveForbidden xs body",
            "",
            "elab \"#mini_theory_audit_circular\" n:ident : command => do",
            "  let declName ← resolveGlobalConstNoOverload n",
            "  let circular ← liftTermElabM do miniTheoryHasCircularPremise declName",
            "  if circular then",
            '    logInfo m!"MINI_THEORY_CIRCULAR_PREMISE:{declName}"',
            "",
            "private partial def miniTheoryProofContainsForbidden",
            "    (proof forbidden : Expr) (theoremArgs : Array FVarId)",
            "    (remainingWork : Nat := 65536) :",
            "    MetaM Bool := do",
            "  if remainingWork == 0 then",
            "    return true",
            "  let proof := proof.cleanupAnnotations",
            "  try",
            "    let proofType ← inferType proof",
            "    if (← isProp proofType) && (← isDefEq proofType forbidden) then",
            "      return theoremArgs.any proof.containsFVar",
            "  catch _ =>",
            "    return true",
            "  match proof with",
            "  | .app fn arg =>",
            "      if ← miniTheoryProofContainsForbidden fn forbidden theoremArgs (remainingWork - 1) then",
            "        return true",
            "      miniTheoryProofContainsForbidden arg forbidden theoremArgs (remainingWork - 1)",
            "  | .lam .. =>",
            "      lambdaTelescope proof fun _ body =>",
            "        miniTheoryProofContainsForbidden body forbidden theoremArgs",
            "          (remainingWork - 1)",
            "  | .letE _ _ value body _ =>",
            "      miniTheoryProofContainsForbidden",
            "        (body.instantiate1 value) forbidden theoremArgs (remainingWork - 1)",
            "  | .mdata _ body =>",
            "      miniTheoryProofContainsForbidden body forbidden theoremArgs (remainingWork - 1)",
            "  | .proj _ _ body =>",
            "      miniTheoryProofContainsForbidden body forbidden theoremArgs (remainingWork - 1)",
            "  | _ => return false",
            "",
            "private def miniTheoryHasForbiddenPremise (declName forbiddenName : Name) : MetaM Bool := do",
            "  let info ← getConstInfo declName",
            "  let forbiddenInfo ← getConstInfo forbiddenName",
            "  let some forbiddenValue := forbiddenInfo.value? | return false",
            "  let some proofValue := info.value? | return true",
            "  let proofUsesForbidden ← lambdaTelescope proofValue fun xs proofBody => do",
            "    let mut premiseIds : Array FVarId := #[]",
            "    for x in xs do",
            "      if ← isProp (← inferType x) then",
            "        premiseIds := premiseIds.push x.fvarId!",
            "    miniTheoryProofContainsForbidden proofBody forbiddenValue",
            "      premiseIds",
            "  if proofUsesForbidden then",
            "    return true",
            "  forallTelescopeReducing info.type fun xs _body =>",
            "    miniTheoryPremisesDeriveForbidden xs forbiddenValue",
            "",
            "elab \"#mini_theory_audit_forbidden\" n:ident t:ident : command => do",
            "  let declName ← resolveGlobalConstNoOverload n",
            "  let targetName ← resolveGlobalConstNoOverload t",
            "  let forbidden ← liftTermElabM do",
            "    miniTheoryHasForbiddenPremise declName targetName",
            "  if forbidden then",
            '    logInfo m!"MINI_THEORY_FORBIDDEN_PREMISE:{declName}:{targetName}"',
            "",
            # Fail-closed backstop independent of the Python name parser: walk
            # every constant Lean actually elaborated under the bundle
            # namespace and flag any whose transitive axiom closure escapes the
            # allowlist.  This catches declarations the parser mis-namespaced
            # or dropped (e.g. via a partial-width `end`) and therefore never
            # audited per-declaration.
            "elab \"#mini_theory_audit_namespace_axioms\" n:ident : command => do",
            "  let env ← getEnv",
            "  let nsName := n.getId",
            "  let allowed : List Name := ["
            + ", ".join(f"`{axiom_name}" for axiom_name in sorted(_ALLOWED_AXIOMS))
            + "]",
            "  for (declName, _) in env.constants.toList do",
            "    if nsName.isPrefixOf declName && declName != nsName then",
            "      let axs ← liftCoreM <| collectAxioms declName",
            "      for ax in axs do",
            "        if !(allowed.contains ax) then",
            '          logInfo m!"MINI_THEORY_NS_FORBIDDEN_AXIOM:{declName}:{ax}"',
            "",
        ])
        for kind, name in declarations:
            lines.extend(
                (
                    "set_option pp.universes true in",
                    f"#check {name}",
                    f"#print axioms {name}",
                    *(
                        (f"#mini_theory_audit_circular {name}",)
                        if kind in {"theorem", "lemma"}
                        else ()
                    ),
                    *(
                        tuple(
                            f"#mini_theory_audit_forbidden {name} {target_name}"
                            for target_name in forbidden_names
                        )
                        if kind in {"theorem", "lemma"}
                        else ()
                    ),
                    "",
                )
            )
        namespace_probe = str(namespace or "").strip()
        if namespace_probe:
            lines.append(
                f"#mini_theory_audit_namespace_axioms {namespace_probe}"
            )
            lines.append("")
        return "\n".join(lines)

    @staticmethod
    def _parse_audit(
        declarations: Sequence[tuple[str, str]],
        output: str,
    ) -> tuple[list[TheoryDeclaration], str]:
        records: list[TheoryDeclaration] = []
        for kind, fq_name in declarations:
            type_text = ""
            type_match = re.search(
                rf"(?ms)^{re.escape(fq_name)}(?P<type>.*?)(?=^'{re.escape(fq_name)}'\s+(?:depends|does)\b)",
                str(output or ""),
            )
            if type_match is not None:
                rendered = " ".join(type_match.group("type").split()).strip()
                if rendered.startswith(":"):
                    rendered = rendered[1:].strip()
                type_text = rendered
            if not type_text:
                return [], f"missing_declaration_type:{fq_name}"
            axioms = TheoryBundleVerifier._parse_axioms(output, fq_name)
            if axioms is None:
                return [], f"missing_axiom_report:{fq_name}"
            unexpected = sorted(set(axioms) - _ALLOWED_AXIOMS)
            if unexpected:
                return [], f"unexpected_axioms:{fq_name}:{','.join(unexpected)}"
            records.append(
                TheoryDeclaration(
                    fq_name=fq_name,
                    declaration_kind=kind,
                    type_text=type_text,
                    referenced_constants=tuple(
                        dict.fromkeys(
                            token
                            for token in re.findall(
                                r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+",
                                type_text,
                            )
                            if token != fq_name
                        )
                    ),
                    axioms=tuple(axioms),
                )
            )
        return records, ""

    @staticmethod
    def _parse_axioms(output: str, fq_name: str) -> Optional[list[str]]:
        for match in _PRINT_AXIOMS_DEPENDS_RE.finditer(output):
            if match.group(1).strip() == fq_name:
                return [
                    item.strip()
                    for item in match.group(2).split(",")
                    if item.strip()
                ]
        for match in _PRINT_AXIOMS_NONE_RE.finditer(output):
            if match.group(1).strip() == fq_name:
                return []
        return None

    def _lean_toolchain(self) -> str:
        path = self.lean_project_dir / "lean-toolchain"
        try:
            return path.read_text(encoding="utf-8").strip()
        except OSError:
            return ""

    def _mathlib_revision(
        self,
        cancellation_event: Optional[threading.Event] = None,
    ) -> str:
        if cancellation_event is not None and cancellation_event.is_set():
            return ""
        return dependency_environment_fingerprint(self.lean_project_dir)

    @staticmethod
    def _rejected(
        candidate: TheoryBundleCandidate,
        diagnostic: str,
        *,
        compile_output: str = "",
        audit_output: str = "",
    ) -> TheoryVerificationResult:
        combined = f"{compile_output}\n{audit_output}".strip()
        return TheoryVerificationResult(
            receipt=TheoryVerificationReceipt(
                accepted=False,
                bundle_id=candidate.bundle_id,
                module_name=candidate.module_name,
                source_hash=candidate.source_hash,
                verification_output_hash=content_hash(combined, length=64),
                diagnostic=str(diagnostic or "rejected"),
            ),
            compile_output=compile_output,
            audit_output=audit_output,
        )
