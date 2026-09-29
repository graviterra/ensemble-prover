"""Prepare independent Lean targets without admitting unfinished dependencies.

The compiler supplies command boundaries and structural declaration contracts.
Input probes may contain unfinished proofs; this permission is local to this
module and never changes proof acceptance or exported-artifact verification.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

from .answer_input import find_answer_template
from .lean_input_io import read_source_bytes
from .nl_lean import _lean_string
from .proof_presentation import _CONTRACT_PROBE
from .sync_subprocess import run_process_group
from .theorem_project import (
    GENERIC_ADAPTER_ID,
    LeanTheoremDeclaration,
    TheoremProjectRequest,
    _mask_noncode,
    _active_command_scope_closers,
    _resolve_theorem_project,
    infer_lake_project,
    merge_imports,
    scan_lean_theorems,
    scan_lean_imports,
    select_lean_theorem,
    theorem_type_probe_source,
    validate_theorem_project_source,
)


class PreparationError(ValueError):
    """The compiler could not establish a faithful prepared input."""


@dataclass(frozen=True)
class PreparedLeanTarget:
    source_path: Path
    source_sha256: str
    theorem_name: str
    project_path: Path
    prepared_source: str = ""
    prepared_sha256: str = ""
    prepared_path: Path | None = None
    omitted_declarations: tuple[str, ...] = ()
    compatibility_adjustments: tuple[dict[str, Any], ...] = ()
    prepared_environment: dict[str, Any] = field(default_factory=dict)
    error: str = ""

    @property
    def ready(self) -> bool:
        return not self.error and self.prepared_path is not None

    def to_record(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "source_path": str(self.source_path),
            "source_sha256": self.source_sha256,
            "theorem_name": self.theorem_name,
            "name": self.theorem_name,
            "project_path": str(self.project_path),
            "prepared_path": str(self.prepared_path) if self.prepared_path else "",
            "prepared_sha256": self.prepared_sha256,
            "omitted_declarations": list(self.omitted_declarations),
            "compatibility_adjustments": list(self.compatibility_adjustments),
            "prepared_environment": self.prepared_environment,
            "status": "ready" if self.ready else "blocked",
            "error": self.error,
        }


@dataclass
class _CompilerReceipt:
    records: dict[str, dict[str, Any]] = field(default_factory=dict)
    targets: dict[str, str] = field(default_factory=dict)
    commands: list[dict[str, Any]] = field(default_factory=list)


def _hash(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def _diagnostics(output: Any) -> str:
    # A receipt can dwarf preceding compiler errors; keep diagnostics visible
    # without echoing enormous structural expressions as the error message.
    lines = [
        line
        for line in str(output or "").splitlines()
        if "PREPARED_CONTRACT_" not in line
    ]
    return "\n".join(lines)[-8000:]


def _run_lean(
    command: Sequence[str],
    *,
    project: Path,
    timeout_s: float,
    environment: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    try:
        return run_process_group(
            command, cwd=project, timeout=timeout_s, env=environment
        )
    except subprocess.TimeoutExpired as exc:
        raise PreparationError(
            f"Lean input preparation exceeded its {timeout_s:g}s compiler timeout"
        ) from exc
    except OSError as exc:
        raise PreparationError(f"could not start Lean input compiler: {exc}") from exc


def _build_imports(
    source: str,
    *,
    directory: Path,
    project: Path,
    source_dirs: Sequence[Path],
    timeout_s: float,
) -> tuple[tuple[Path, ...], dict[str, Any]]:
    # Even without local build targets, Lake initializes its manifest when an
    # environment is first used. Do that before capturing project provenance.
    initialized = _run_lean(
        ["lake", "env", "lean", "--version"], project=project, timeout_s=timeout_s
    )
    if initialized.returncode:
        raise PreparationError(
            "Lean project initialization failed:\n" + _diagnostics(initialized.stdout)
        )
    # A metadata-only declaration supports private/answer-first inputs. The
    # actual mathematical source is compiled and audited separately.
    metadata_text = (
        "".join(f"import {name}\n" for name in scan_lean_imports(source))
        + "theorem prepared_import_metadata : True := by trivial\n"
    )
    directory.mkdir(parents=True, exist_ok=True)
    metadata_source = directory / f"ImportMetadata_{_hash(metadata_text)[:20]}.lean"
    metadata_source.write_text(metadata_text, encoding="utf-8")
    request = TheoremProjectRequest(
        metadata_source,
        "prepared_import_metadata",
        project,
        source_dirs=tuple(source_dirs),
    )
    metadata = _resolve_theorem_project(request, adapter_id=GENERIC_ADAPTER_ID)
    for build_project, modules in [
        (project, metadata.project_imports),
        *metadata.support_project_builds.items(),
    ]:
        if modules:
            built = _run_lean(
                ["lake", "build", *modules],
                project=Path(build_project),
                timeout_s=timeout_s,
            )
            if built.returncode:
                raise PreparationError(
                    "supporting Lean project build failed:\n"
                    + _diagnostics(built.stdout)
                )
    # Bind the post-build manifests and compiled supporting modules.
    metadata = _resolve_theorem_project(request, adapter_id=GENERIC_ADAPTER_ID)
    validate_theorem_project_source(metadata)
    return tuple(metadata.module_search_paths), dict(metadata.input_spec)


def validate_prepared_environment(record: Mapping[str, Any]) -> None:
    """Reject import, toolchain, or supporting-project drift before dispatch."""
    saved = record.get("prepared_environment")
    if not isinstance(saved, Mapping) or not saved.get("input_spec_hash"):
        raise PreparationError("prepared input has no compiler environment provenance")
    metadata_path = Path(str(saved.get("lean_file") or ""))
    if _hash(read_source_bytes(metadata_path).decode("utf-8")) != saved.get(
        "source_sha256"
    ):
        raise PreparationError("prepared input environment metadata changed")
    request = TheoremProjectRequest(
        metadata_path,
        str(saved["theorem_name"]),
        Path(str(saved["project_path"])),
        source_dirs=tuple(
            Path(str(row["path"])) for row in saved.get("source_dirs", ())
        ),
    )
    current = _resolve_theorem_project(request, adapter_id=GENERIC_ADAPTER_ID)
    validate_theorem_project_source(current)
    if dict(current.input_spec) != dict(saved):
        raise PreparationError(
            "prepared Lean import or project environment changed; prepare the input again"
        )


# Share only structural serialization, never the export acceptance policy.
# Importing Lean into the input itself could change name/typeclass resolution.
_CONTRACT_SERIALIZER = _CONTRACT_PROBE.split(
    "  let mut rows : Array Lean.Json := #[]", 1
)[0].replace("run_meta do", "run_cmd Lean.Elab.Command.liftTermElabM do")


def _inspector_source(
    source: str, module: str, targets: Sequence[str], marker: str
) -> str:
    names = "#[" + ", ".join(_lean_string(x) for x in targets) + "]"
    body = (
        _CONTRACT_SERIALIZER
        + r"""
  let some moduleIdx := env.getModuleIdx? (Lean.Name.mkSimple "__MODULE__")
    | Lean.throwError "prepared input module is unavailable"
  let mut rows : Array Lean.Json := #[]
  for (name, ci) in env.constants.toList do
    if env.getModuleIdxFor? name != some moduleIdx then continue
    let axioms ← Lean.collectAxioms name
    let ranges ← Lean.findDeclarationRanges? name
    let originReads := match ci.value? with
      | none => #[]
      | some value => value.getUsedConstants.filter fun dependency =>
          [`Lean.getMainModule, `Lean.MonadLog.getFileName,
           `Lean.MonadFileMap.getFileMap, `Lean.Core.Context.fileName].contains dependency
    let mut typeSorry := ci.type.hasSorry
    for dependency in ci.type.getUsedConstants do
      if (← Lean.collectAxioms dependency).contains ``sorryAx then
        typeSorry := true
    rows := rows.push <| Lean.Json.mkObj [
      ("key", Lean.toJson (reprStr name)),
      ("name", Lean.toJson name.toString),
      ("contract", contract ci),
      ("sourceLine", Lean.toJson (ranges.map (·.selectionRange.pos.line))),
      ("sourceColumn", Lean.toJson (ranges.map (·.selectionRange.pos.column))),
      ("sourceOriginReads", Lean.toJson (originReads.map (·.toString))),
      ("unfinished", Lean.toJson (axioms.contains ``sorryAx)),
      ("typeSorry", Lean.toJson typeSorry)]
  let mut targets : Array Lean.Json := #[]
  for requested in (__TARGETS__ : Array String) do
    let stx ← match Lean.Parser.runParserCategory env `term ("@_root_." ++ requested) with
      | .ok stx => pure stx
      | .error error => Lean.throwError error
    let term ← Lean.Elab.Term.withoutErrToSorry do Lean.Elab.Term.elabTerm stx none
    let some name := term.getAppFn.constName?
      | Lean.throwError "target is not a named declaration"
    targets := targets.push <| Lean.Json.mkObj [
      ("name", Lean.toJson requested), ("key", Lean.toJson (reprStr name))]
  let source := __SOURCE__
  let input := Lean.Parser.mkInputContext source "prepared-input.lean"
  let (_, firstState, firstMessages) ← Lean.Parser.parseHeader input
  let mut state := firstState
  let mut messages := firstMessages
  let mut spans : Array Lean.Json := #[]
  repeat
    let (command, nextState, nextMessages) := Lean.Parser.parseCommand input
      { env := ← Lean.getEnv, options := ← Lean.getOptions,
        currNamespace := ← Lean.getCurrNamespace, openDecls := ← Lean.getOpenDecls } state messages
    state := nextState
    messages := nextMessages
    if messages.hasErrors then
      for message in messages.toList do
        Lean.logError (← message.toString)
      Lean.throwError "input command parsing failed"
    if command.isOfKind ``Lean.Parser.Command.eoi then break
    let some start := command.getPos? | Lean.throwError "missing command start"
    let some stop := command.getTailPos? | Lean.throwError "missing command end"
    spans := spans.push <| Lean.Json.mkObj [
      ("start", Lean.toJson start.byteIdx), ("end", Lean.toJson stop.byteIdx),
      ("kind", Lean.toJson command.getKind.toString),
      ("sourceRelativeTerm", Lean.toJson (command.findStack? (fun _ => true)
        (fun node => node.isOfKind ``Lean.includeStr)).isSome),
      ("bodyKind", Lean.toJson command[1].getKind.toString)]
    -- Replay parser context only. Constants have already been compiled and
    -- must not be redeclared in the inspector's environment.
    if [``Lean.Parser.Command.notation, ``Lean.Parser.Command.mixfix].contains command.getKind then
      -- Notation quotation can mention section variables absent from this
      -- parser-only replay. Its original elaboration was already checked;
      -- no expression from this replay is used in a declaration contract.
      Lean.Elab.Command.withScope (fun scope => { scope with opts := scope.opts.setBool `quotPrecheck false }) do
        Lean.Elab.Command.elabCommand command
    else if [``Lean.Parser.Command.open, ``Lean.Parser.Command.namespace,
        ``Lean.Parser.Command.section, ``Lean.Parser.Command.end].contains command.getKind then
      Lean.Elab.Command.elabCommand command
  let receipt := Lean.Json.mkObj [
    ("records", Lean.Json.arr rows), ("targets", Lean.Json.arr targets),
    ("commands", Lean.Json.arr spans)]
  Lean.logInfo m!"__MARKER__{receipt.compress}"
"""
    )
    contracts, parser = body.split("  let source := __SOURCE__", 1)
    heading, contract_body = contracts.split(
        "run_cmd Lean.Elab.Command.liftTermElabM do", 1
    )
    body = (
        heading
        + "run_cmd do\n  let (rows, targets) ← Lean.Elab.Command.liftTermElabM do\n"
        + "\n".join("  " + line for line in contract_body.strip("\n").splitlines())
        + "\n    pure (rows, targets)\n  let source := __SOURCE__"
        + parser
    )
    replacements = {
        "__MODULE__": module,
        "__TARGETS__": names,
        "__MARKER__": marker,
        "__SOURCE__": _lean_string(source),
    }
    body = re.sub(
        "|".join(re.escape(key) for key in replacements),
        lambda match: replacements[match.group()],
        body,
    )
    return f"import Lean\nimport {module}\n" + body


def _probe(
    source: str,
    *,
    directory: Path,
    project: Path,
    timeout_s: float,
    targets: Sequence[str],
    extra_paths: Sequence[Path] = (),
    max_heartbeats: int | None = None,
) -> _CompilerReceipt:
    # Keep the module name identical across original/candidate checks. Private
    # names and generated constants are part of the structural contract.
    module = "PreparedInput_" + hashlib.sha256(str(directory).encode()).hexdigest()[:24]
    while module in scan_lean_imports(source):
        module += "_"
    path = directory / f"{module}.lean"
    path.write_text(source, encoding="utf-8")
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(
        [
            str(directory),
            *(str(p) for p in extra_paths),
            environment.get("LEAN_PATH", ""),
        ]
    ).rstrip(os.pathsep)
    options = [] if max_heartbeats is None else [f"-DmaxHeartbeats={max_heartbeats}"]
    compiled = _run_lean(
        [
            "lake",
            "env",
            "lean",
            *options,
            f"--root={directory}",
            "-o",
            str(path.with_suffix(".olean")),
            str(path),
        ],
        project=project,
        timeout_s=timeout_s,
        environment=environment,
    )
    if compiled.returncode != 0:
        raise PreparationError(
            "Lean input compilation failed:\n" + _diagnostics(compiled.stdout)
        )
    marker = "PREPARED_CONTRACT_" + uuid.uuid4().hex + ":"
    inspector = directory / "InspectPreparedInput.lean"
    inspector.write_text(
        _inspector_source(source, module, targets, marker), encoding="utf-8"
    )
    inspected = _run_lean(
        ["lake", "env", "lean", *options, str(inspector)],
        project=project,
        timeout_s=timeout_s,
        environment=environment,
    )
    if inspected.returncode != 0:
        raise PreparationError(
            "Lean input contract inspection failed:\n" + _diagnostics(inspected.stdout)
        )
    payloads = [
        line.split(marker, 1)[1]
        for line in str(inspected.stdout or "").split("\n")
        if marker in line
    ]
    if len(payloads) != 1:
        raise PreparationError("missing or ambiguous Lean input contract receipt")
    receipt = json.loads(payloads[0])
    records = {row["key"]: row for row in receipt["records"]}
    if len(records) != len(receipt["records"]):
        raise PreparationError("duplicate Lean declaration contract")
    raw = source.encode("utf-8")
    spans = []
    for span in receipt["commands"]:
        start, end = span["start"], span["end"]
        if not 0 <= start <= end <= len(raw):
            raise PreparationError("Lean command span outside input source")
        spans.append(
            {
                **span,
                "start": len(raw[:start].decode("utf-8")),
                "end": len(raw[:end].decode("utf-8")),
            }
        )
    return _CompilerReceipt(
        records, {r["name"]: r["key"] for r in receipt["targets"]}, spans
    )


_COMPAT_OPTION = "backward.isDefEq.respectTransparency"
_COMPAT_LINE = re.compile(
    r"(?m)^[ \t]*set_option[ \t]+backward\.isDefEq\.respectTransparency[ \t]+false[ \t]*(?:\r?\n|$)"
)


def _option_compatibility(
    source: str, error: PreparationError
) -> tuple[str, tuple[dict[str, Any], ...]]:
    diagnostic = str(error)
    if not re.search(
        r"unknown option[^\n]*backward\.isDefEq\.respectTransparency",
        diagnostic,
        re.IGNORECASE,
    ):
        raise error
    # Quoted Lean identifiers may span lines and contain command-looking text.
    # This compatibility exception applies only to actual command text.
    masked = _mask_noncode(source, mask_quoted_identifiers=True)
    spans = [
        m.span()
        for m in _COMPAT_LINE.finditer(source)
        if masked[m.start() : m.end()].strip() == m.group().strip()
    ]
    if not spans:
        raise error
    adjusted = source
    for start, end in reversed(spans):
        adjusted = (
            adjusted[:start]
            + "".join("\n" if c == "\n" else " " for c in adjusted[start:end])
            + adjusted[end:]
        )
    return adjusted, (
        {
            "kind": "unsupported_option",
            "option": _COMPAT_OPTION,
            "value": False,
            "source_spans": [list(x) for x in spans],
            "reason": "compiler reported unknown option",
        },
    )


def _plain_omission_span(
    source: str, declaration: LeanTheoremDeclaration, commands: Sequence[dict[str, Any]]
) -> tuple[int, int]:
    containing = [
        c for c in commands if c["start"] <= declaration.keyword_start < c["end"]
    ]
    if len(containing) != 1:
        raise PreparationError(
            "unfinished declaration has no unique compiler command boundary: "
            + declaration.canonical_name
        )
    command = containing[0]
    plain = (
        command["kind"] == "Lean.Parser.Command.declaration"
        and command["bodyKind"] == "Lean.Parser.Command.theorem"
    ) or command["kind"] == "lemma"
    prefix = _mask_noncode(source[command["start"] : declaration.keyword_start]).strip()
    visibility_only = prefix in {"", "private", "public"}
    if (
        not plain
        or not visibility_only
        or declaration.command_prefix.strip() not in {"", "private", "public"}
        or declaration.scoped_prefix
    ):
        raise PreparationError(
            "cannot independently omit an attributed or wrapped unfinished declaration: "
            + declaration.canonical_name
        )
    if command["end"] < declaration.header_end:
        raise PreparationError(
            "unfinished theorem header crosses its compiler boundary"
        )
    return command["start"], command["end"]


def _candidate(
    source: str,
    target: LeanTheoremDeclaration,
    omissions: Sequence[tuple[LeanTheoremDeclaration, tuple[int, int]]],
    imports: Sequence[str],
    *,
    answer_template: bool = False,
) -> str:
    edited = source
    for _decl, (start, end) in sorted(
        omissions, key=lambda item: item[1][0], reverse=True
    ):
        edited = (
            edited[:start]
            + "".join("\n" if c == "\n" else " " for c in edited[start:end])
            + edited[end:]
        )
    selected = select_lean_theorem(scan_lean_theorems(edited), target.canonical_name)
    if answer_template:
        # A designated answer hole carries a source-location label in Lean's
        # structural expression. Retain the original header's exact position;
        # adding even a warningAsError wrapper changes that expression.
        header = edited[: selected.header_end]
        if not header.rstrip().endswith(":="):
            header += " :="
        closers = _active_command_scope_closers(edited, selected.declaration_start)
        return header + " by\n  sorry\n" + "\n".join(closers) + "\n"
    prepared = theorem_type_probe_source(edited, selected, imports)
    if selected.docstring:
        header = (
            selected.command_prefix
            + edited[selected.keyword_start : selected.header_end]
        ).strip()
        pos = prepared.rfind(header)
        if pos < 0:
            raise PreparationError(
                "selected theorem header was lost during preparation"
            )
        prepared = prepared[:pos] + selected.docstring + "\n" + prepared[pos:]
    return prepared


def _check_contracts(
    before: _CompilerReceipt,
    after: _CompilerReceipt,
    target: str,
    *,
    answer_template: bool = False,
) -> None:
    key = before.targets.get(target)
    if not key or after.targets.get(target) != key or key not in after.records:
        raise PreparationError("prepared theorem identity differs from the original")
    for name, record in after.records.items():
        if (
            name not in before.records
            or record["contract"] != before.records[name]["contract"]
        ):
            raise PreparationError(
                "preparation changed retained declaration contract: " + record["name"]
            )
        if record["typeSorry"] and not (name == key and answer_template):
            raise PreparationError(
                "unfinished dependency in declaration type: " + record["name"]
            )
        if name != key and record["unfinished"]:
            raise PreparationError(
                "retained declaration depends on an unfinished proof: " + record["name"]
            )


def _unmatched_theorems(
    source: str,
    declarations: Sequence[LeanTheoremDeclaration],
    baseline: _CompilerReceipt,
) -> list[str]:
    """Expose compiler-discovered targets outside the shared scanner grammar."""
    missing = []
    for command in baseline.commands:
        if (
            command["bodyKind"] != "Lean.Parser.Command.theorem"
            and command["kind"] != "lemma"
        ):
            continue
        if any(
            command["start"] <= d.keyword_start < command["end"] for d in declarations
        ):
            continue
        for row in baseline.records.values():
            if (
                not row["unfinished"]
                or row["contract"]["kind"] != "theorem"
                or not row["sourceLine"]
            ):
                continue
            position = (
                sum(
                    len(line) + 1
                    for line in source.split("\n")[
                        : row["sourceLine"] - 1
                    ]
                )
                + row["sourceColumn"]
            )
            if command["start"] <= position < command["end"]:
                missing.append(row["name"])
    return list(dict.fromkeys(missing))


def prepare_lean_file(
    source_path: Path,
    project_path: Path | None,
    scratch_dir: Path,
    theorem_name: str | None = None,
    imports: Sequence[str] = (),
    *,
    source_dirs: Sequence[Path] = (),
    timeout_s: float = 120.0,
    max_heartbeats: int | None = None,
) -> list[PreparedLeanTarget]:
    """Compile a source and isolate unfinished targets with exact contracts.

    Source-wide failures raise PreparationError. Individual dependency or
    context conflicts produce blocked result rows, leaving siblings runnable.
    """
    source_path = Path(source_path).expanduser().resolve(strict=True)
    project = (
        Path(project_path).expanduser().resolve(strict=True)
        if project_path
        else infer_lake_project(source_path)
    )
    if project is None:
        raise PreparationError("no Lake project found; provide --project-path")
    original = read_source_bytes(source_path).decode("utf-8")
    source_hash = _hash(original)
    source = merge_imports(original, imports)
    declarations = scan_lean_theorems(source)
    requested = (
        select_lean_theorem(declarations, theorem_name) if theorem_name else None
    )
    public_names = [d.canonical_name for d in declarations if not d.private]
    scratch_dir = Path(scratch_dir).expanduser().resolve()
    scratch_dir.mkdir(parents=True, exist_ok=True)
    results = []
    adjustments: tuple[dict[str, Any], ...] = ()
    with tempfile.TemporaryDirectory(prefix="lean-input-", dir=scratch_dir) as work:
        directory = Path(work)
        extra_paths, environment_receipt = _build_imports(
            source,
            directory=scratch_dir / "metadata",
            project=project,
            source_dirs=source_dirs,
            timeout_s=timeout_s,
        )
        try:
            baseline = _probe(
                source,
                directory=directory,
                project=project,
                timeout_s=timeout_s,
                targets=public_names,
                extra_paths=extra_paths,
                max_heartbeats=max_heartbeats,
            )
        except PreparationError as exc:
            source, adjustments = _option_compatibility(source, exc)
            declarations = scan_lean_theorems(source)
            baseline = _probe(
                source,
                directory=directory,
                project=project,
                timeout_s=timeout_s,
                targets=public_names,
                extra_paths=extra_paths,
                max_heartbeats=max_heartbeats,
            )
        for row in baseline.records.values():
            if row.get("sourceOriginReads"):
                raise PreparationError(
                    "independent preparation does not support source/module-origin-dependent "
                    "elaboration in "
                    + row["name"]
                    + ": "
                    + ", ".join(row["sourceOriginReads"])
                    + "; provide a location-independent theorem entrypoint"
                )
        for command in baseline.commands:
            executable_quotation = command["kind"] in {
                "Lean.Parser.Command.macro",
                "Lean.Parser.Command.macro_rules",
                "Lean.Parser.Command.elab",
                "Lean.Parser.Command.elab_rules",
            }
            if command.get("sourceRelativeTerm") and (
                executable_quotation
                or re.search(
                    r"(?<![\w'.`])include_str(?![\w'])",
                    _mask_noncode(
                        source[command["start"] : command["end"]],
                        mask_quoted_identifiers=True,
                    ),
                )
            ):
                raise PreparationError(
                    "independent preparation does not support source-relative include_str; "
                    "provide a location-independent theorem entrypoint"
                )
        # Private names contain a compiler-owned module prefix and cannot be
        # looked up through the public source spelling. Declaration ranges
        # bind them to their original source name without suffix guessing.
        for declaration in declarations:
            if not declaration.private:
                continue
            line = source.count("\n", 0, declaration.name_start) + 1
            column = len(source[: declaration.name_start].rsplit("\n", 1)[-1])
            matches = [
                key
                for key, row in baseline.records.items()
                if row["sourceLine"] == line
                and row["sourceColumn"] == column
                and row["contract"]["kind"] == "theorem"
            ]
            if len(matches) != 1:
                raise PreparationError(
                    "private theorem has no unique compiler source identity: "
                    + declaration.canonical_name
                )
            baseline.targets[declaration.canonical_name] = matches[0]
        unfinished = [
            d
            for d in declarations
            if baseline.records[baseline.targets[d.canonical_name]]["unfinished"]
        ]
        targets = (
            [select_lean_theorem(declarations, requested.canonical_name)]
            if requested
            else unfinished
        )
        for target in targets:
            base = dict(
                source_path=source_path,
                source_sha256=source_hash,
                theorem_name=target.canonical_name,
                project_path=project,
                compatibility_adjustments=adjustments,
                prepared_environment=environment_receipt,
            )
            try:
                if target.private:
                    raise PreparationError(
                        "private theorem targets are not independently addressable"
                    )
                answer_template = find_answer_template(source, target.canonical_name)
                if (
                    baseline.records[baseline.targets[target.canonical_name]][
                        "typeSorry"
                    ]
                    and not answer_template
                ):
                    raise PreparationError(
                        "target type depends on sorry/admit; a proof placeholder cannot supply a mathematical statement"
                    )
                omissions = [
                    (d, _plain_omission_span(source, d, baseline.commands))
                    for d in unfinished
                    if d.keyword_start < target.keyword_start
                ]
                prepared = _candidate(
                    source,
                    target,
                    omissions,
                    imports,
                    answer_template=answer_template is not None,
                )
                checked = _probe(
                    prepared,
                    directory=directory,
                    project=project,
                    timeout_s=timeout_s,
                    targets=[target.canonical_name],
                    extra_paths=extra_paths,
                    max_heartbeats=max_heartbeats,
                )
                _check_contracts(
                    baseline,
                    checked,
                    target.canonical_name,
                    answer_template=answer_template is not None,
                )
                prepared_hash = _hash(prepared)
                slug = (
                    re.sub(r"[^A-Za-z0-9_-]+", "_", target.canonical_name).strip("_")
                    or "target"
                )
                destination = (
                    scratch_dir / "targets" / f"{slug[:80]}_{prepared_hash[:16]}.lean"
                )
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(prepared, encoding="utf-8")
                results.append(
                    PreparedLeanTarget(
                        **base,
                        prepared_source=prepared,
                        prepared_sha256=prepared_hash,
                        prepared_path=destination,
                        omitted_declarations=tuple(
                            d.canonical_name for d, _ in omissions
                        ),
                    )
                )
            except (PreparationError, ValueError) as exc:
                results.append(PreparedLeanTarget(**base, error=str(exc)))
        if not requested:
            for name in _unmatched_theorems(source, declarations, baseline):
                results.append(
                    PreparedLeanTarget(
                        source_path=source_path,
                        source_sha256=source_hash,
                        theorem_name=name,
                        project_path=project,
                        compatibility_adjustments=adjustments,
                        prepared_environment=environment_receipt,
                        error="compiler discovered an unfinished theorem outside the supported declaration syntax; it was not queued",
                    )
                )
    if _hash(read_source_bytes(source_path).decode("utf-8")) != source_hash:
        raise PreparationError("Lean source changed while preparing targets")
    if results:
        validate_prepared_environment(results[0].to_record())
    return results
