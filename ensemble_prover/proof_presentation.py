"""Optional, kernel-checked presentation of already verified proof exports.

Source analysis proposes edits only. A fresh Lean replay must preserve every
retained declaration's type and every non-theorem declaration's implementation.
The original artifact is the fallback on every optional-pass failure.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
import uuid
from collections import Counter, deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Sequence

from .export_dependency_graph import _strip_comments_and_strings
from .subprocess_environment import sanitized_subprocess_environment
from .theorem_project import scan_lean_theorems

MAX_PRESENTATION_SECONDS = 60.0
MAX_SOURCE_BYTES = 4_000_000
MAX_PROBE_BYTES = 32_000_000


@dataclass(frozen=True)
class EditableDeclaration:
    name: str
    source_name: str
    start: int
    end: int
    header_end: int
    simple_signature: bool


@dataclass
class PresentationResult:
    content: str
    status: str = "unchanged"
    reason: str = "no_changes"
    removed: list[str] = field(default_factory=list)
    rewritten: list[str] = field(default_factory=list)
    original_path: str = ""
    axioms: list[str] | None = None

    def report(self, original: str) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": self.status,
            "reason": self.reason,
            "original_sha256": _digest(original),
            "presented_sha256": _digest(self.content),
            "original_bytes": len(original.encode()),
            "presented_bytes": len(self.content.encode()),
            "original_path": self.original_path,
            "removed_declarations": self.removed,
            "rewritten_declarations": self.rewritten,
            "presented_axioms": self.axioms,
        }


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _check_deadline(deadline: float | None) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise TimeoutError("presentation time allowance exhausted")


def _editable_declarations(
    content: str, command_spans: Sequence[dict[str, Any]] | None = None,
    *, deadline: float | None = None,
) -> list[EditableDeclaration]:
    """Only standalone, undecorated tactic theorems are editing candidates.

    Definitions, attributes, scoped commands, and equation-style declarations
    stay byte-for-byte intact. The source scanner is not a proof authority.
    """
    _check_deadline(deadline)
    masked = _strip_comments_and_strings(content)
    commands = {span["start"]: span for span in command_spans or ()}
    result = []
    for decl in scan_lean_theorems(content):
        _check_deadline(deadline)
        start = decl.keyword_start
        if (decl.private or decl.public or decl.universe_suffix or decl.scoped_prefix
                or decl.command_prefix.strip()
                or (start and content[start - 1] != "\n")):
            continue
        # A preceding attribute/scoped command may have escaped the header
        # parser. Preserve it and its declaration conservatively.
        previous = masked[:start].rstrip().rsplit("\n", 1)[-1].strip()
        if previous.endswith(" in") or previous.startswith("@["):
            continue
        if content[decl.header_end - 2:decl.header_end] != ":=":
            continue
        body = masked[decl.header_end:]
        if re.match(r"\s*by\b", body) is None:
            continue
        first_end = masked.find("\n", decl.header_end)
        if first_end < 0:
            first_end = len(content)
        end = first_end
        body_indent = None
        cursor = first_end + 1
        while cursor < len(content):
            next_end = masked.find("\n", cursor)
            if next_end < 0:
                next_end = len(content)
            line = masked[cursor:next_end]
            if line.strip():
                indent = len(line) - len(line.lstrip())
                if indent == 0 or (body_indent is not None and indent < body_indent):
                    break
                if body_indent is None:
                    body_indent = indent
                end = next_end
            cursor = next_end + 1
        if command_spans is not None:
            # Only Lean's parser authorizes deletion. Heuristic spans above
            # serve the inexpensive preflight, never the published edit.
            command = commands.get(start)
            if command is None:
                continue
            plain_theorem = (command["kind"] == "Lean.Parser.Command.declaration"
                             and command["bodyKind"] == "Lean.Parser.Command.theorem")
            # Mathlib's lemma macro has its own top-level parser kind.
            plain_lemma = command["kind"] == "lemma"
            if not (plain_theorem or plain_lemma):
                continue
            end = command["end"]
            if end < decl.header_end or end > len(content):
                raise ValueError("invalid presentation command span")
        header_tail = masked[decl.name_end:decl.header_end - 2].lstrip()
        result.append(EditableDeclaration(
            decl.canonical_name, decl.source_name, start, end, decl.header_end,
            header_tail.startswith(":"),
        ))
    return result


def _prune_unused(
    content: str, root: str, *, deadline: float | None = None,
    command_spans: Sequence[dict[str, Any]] | None = None,
) -> tuple[str, list[str]]:
    """Remove an unused helper chain with one source scan and a work queue."""
    _check_deadline(deadline)
    masked = _strip_comments_and_strings(content)
    declarations = _editable_declarations(content, command_spans, deadline=deadline)
    tokens = re.compile(r"[\w']+")
    totals = Counter(tokens.findall(masked))
    candidates = {}
    own_counts = {}
    collisions = Counter(d.source_name.rsplit(".", 1)[-1] for d in declarations)
    for decl in declarations:
        _check_deadline(deadline)
        short = decl.source_name.rsplit(".", 1)[-1]
        if decl.name == root or collisions[short] != 1 or tokens.fullmatch(short) is None:
            continue
        candidates[short] = decl
        own_counts[short] = Counter(tokens.findall(masked[decl.start:decl.end]))
    queue = deque(name for name in candidates if totals[name] == own_counts[name][name])
    removed = []
    while queue:
        _check_deadline(deadline)
        name = queue.popleft()
        decl = candidates.pop(name, None)
        if decl is None:
            continue
        removed.append(decl)
        for token, count in own_counts[name].items():
            totals[token] -= count
            if token in candidates and totals[token] == own_counts[token][token]:
                queue.append(token)
    for decl in sorted(removed, key=lambda d: d.start, reverse=True):
        content = content[:decl.start] + content[decl.end:]
    return content, [d.name for d in sorted(removed, key=lambda d: d.start)]


def _needs_readable_type(content: str, decl: EditableDeclaration) -> bool:
    header = content[decl.start:decl.header_end]
    return decl.simple_signature and (len(header) > 1000 or bool(
        re.search(r"@[A-Za-z_][\w.]*|\.\{", header)
    ))


def _rewrite_types(content: str, records: dict[str, Any]) -> tuple[str, list[str]]:
    rewritten = []
    for decl in reversed(_editable_declarations(content)):
        if not _needs_readable_type(content, decl):
            continue
        pretty = str(records.get(decl.name, {}).get("pretty", "")).strip()
        if not pretty:
            continue
        keyword = content[decl.start:].split(None, 1)[0]
        header = f"{keyword} {decl.source_name} : {pretty} :="
        if len(header) >= decl.header_end - decl.start:
            continue
        content = content[:decl.start] + header + content[decl.header_end:]
        rewritten.append(decl.name)
    return content, list(reversed(rewritten))


def _same_contract(before: dict[str, Any], after: dict[str, Any],
                   removed: Sequence[str], root: str) -> bool:
    if root not in before or root not in after:
        return False
    if set(after) - set(before):
        return False
    for name, record in before.items():
        if name not in after:
            generated_auxiliary = record.get("has_source_range") is False and any(
                re.fullmatch(re.escape(parent) + r"\._(?:simp|proof)_[0-9_]+", name)
                for parent in removed
            )
            if (name == root or record["contract"]["kind"] != "theorem"
                    or (name not in removed and not generated_auxiliary)):
                return False
        elif record["contract"] != after[name]["contract"]:
            return False
    return True


# Filled by the local Lean probe: structural expressions, not pretty-printed
# claims, constitute the comparison record. Pretty output only proposes edits.
_CONTRACT_PROBE = r'''
set_option maxRecDepth 100000 in
run_meta do
  let env ← Lean.getEnv
  let contract := fun (ci : Lean.ConstantInfo) =>
    let base := [("name", Lean.toJson (reprStr ci.name)),
                 ("levels", Lean.toJson (reprStr ci.levelParams)),
                 ("type", Lean.toJson (reprStr ci.type))]
    let extra : List (String × Lean.Json) := match ci with
      | .thmInfo _ => [("kind", Lean.toJson "theorem")]
      | .axiomInfo v => [("kind", Lean.toJson "axiom"), ("unsafe", Lean.toJson v.isUnsafe)]
      | .defnInfo v =>
        let hints := match v.hints with
          | .opaque => Lean.Json.arr #[Lean.toJson "opaque"]
          | .abbrev => Lean.Json.arr #[Lean.toJson "abbrev"]
          | .regular height => Lean.Json.arr #[Lean.toJson "regular", Lean.toJson height.toNat]
        let safety := match v.safety with
          | .unsafe => "unsafe" | .safe => "safe" | .partial => "partial"
        [("kind", Lean.toJson "definition"), ("value", Lean.toJson (reprStr v.value)),
         ("hints", hints), ("safety", Lean.toJson safety), ("all", Lean.toJson (reprStr v.all))]
      | .opaqueInfo v =>
        [("kind", Lean.toJson "opaque"), ("value", Lean.toJson (reprStr v.value)),
         ("unsafe", Lean.toJson v.isUnsafe), ("all", Lean.toJson (reprStr v.all))]
      | .quotInfo v =>
        let kind := match v.kind with
          | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
        [("kind", Lean.toJson "quotient"), ("quotKind", Lean.toJson kind)]
      | .inductInfo v =>
        [("kind", Lean.toJson "inductive"), ("numParams", Lean.toJson v.numParams),
         ("numIndices", Lean.toJson v.numIndices), ("all", Lean.toJson (reprStr v.all)),
         ("ctors", Lean.toJson (reprStr v.ctors)), ("numNested", Lean.toJson v.numNested),
         ("isRec", Lean.toJson v.isRec), ("unsafe", Lean.toJson v.isUnsafe),
         ("isReflexive", Lean.toJson v.isReflexive)]
      | .ctorInfo v =>
        [("kind", Lean.toJson "constructor"), ("induct", Lean.toJson (reprStr v.induct)),
         ("cidx", Lean.toJson v.cidx), ("numParams", Lean.toJson v.numParams),
         ("numFields", Lean.toJson v.numFields), ("unsafe", Lean.toJson v.isUnsafe)]
      | .recInfo v =>
        let rules := v.rules.map fun r => Lean.Json.mkObj [
          ("ctor", Lean.toJson (reprStr r.ctor)), ("nfields", Lean.toJson r.nfields),
          ("rhs", Lean.toJson (reprStr r.rhs))]
        [("kind", Lean.toJson "recursor"), ("all", Lean.toJson (reprStr v.all)),
         ("numParams", Lean.toJson v.numParams), ("numIndices", Lean.toJson v.numIndices),
         ("numMotives", Lean.toJson v.numMotives), ("numMinors", Lean.toJson v.numMinors),
         ("rules", Lean.toJson rules), ("k", Lean.toJson v.k), ("unsafe", Lean.toJson v.isUnsafe)]
    Lean.Json.mkObj (base ++ extra)
  let mut rows : Array Lean.Json := #[]
  for (name, _) in env.constants.map₂.toList do
    let ci ← Lean.getConstInfo name
    let pretty ← Lean.withOptions (fun o => o
      |>.setBool `pp.fullNames true |>.setBool `pp.explicit false
      |>.setBool `pp.universes false |>.setBool `pp.proofs false
      |>.setBool `pp.piBinderTypes true |>.setBool `pp.funBinderTypes true
      |>.set `pp.width (100 : Nat) |>.set `pp.maxSteps (1000000 : Nat)) do
        Lean.Meta.ppExpr ci.type
    rows := rows.push (Lean.Json.mkObj [
      ("name", Lean.Json.str name.toString),
      ("contract", contract ci),
      ("has_source_range", Lean.toJson (← Lean.findDeclarationRanges? name).isSome),
      ("pretty", Lean.Json.str pretty.pretty)])
  let source := (← Lean.getFileMap).source
  let input := Lean.Parser.mkInputContext source "presentation-command-spans.lean"
  let (_, firstState, firstMessages) ← Lean.Parser.parseHeader input
  let mut state := firstState
  let mut messages := firstMessages
  let mut spans : Array Lean.Json := #[]
  repeat
    let (command, nextState, nextMessages) := Lean.Parser.parseCommand input
      { env := ← Lean.getEnv, options := ← Lean.getOptions,
        currNamespace := .anonymous, openDecls := [] } state messages
    state := nextState
    messages := nextMessages
    if messages.hasErrors then
      Lean.throwError "presentation command parsing failed"
    if command.isOfKind ``Lean.Parser.Command.eoi then break
    let some start := command.getPos? | Lean.throwError "missing command start"
    let some stop := command.getTailPos? | Lean.throwError "missing command end"
    spans := spans.push <| Lean.Json.mkObj [
      ("start", Lean.toJson start.byteIdx), ("end", Lean.toJson stop.byteIdx),
      ("kind", Lean.toJson command.getKind.toString),
      ("bodyKind", Lean.toJson command[1].getKind.toString)]
  let receipt := Lean.Json.mkObj [("records", Lean.Json.arr rows), ("commands", Lean.Json.arr spans)]
  Lean.logInfo m!"__PRESENTATION_MARKER__{receipt.compress}"
'''


def _probe(content: str, path: Path, *, project: Path, timeout_s: float,
           extra_lean_paths: Sequence[Path],
           command_spans: list[dict[str, Any]] | None = None,
           audit_root: str = "", audit_axioms: list[str] | None = None) -> dict[str, Any]:
    from .extract_solved import (
        _axiom_audit_verdict, _export_lean_env, _export_lean_verdict,
        _parse_print_axioms, is_valid_lean_qualified_name,
    )

    if audit_root and not is_valid_lean_qualified_name(audit_root):
        raise ValueError("invalid presentation audit root")
    nonce = "PRESENTATION_" + uuid.uuid4().hex
    marker = nonce + ":"
    audit_begin, audit_end = nonce + "_AXIOMS_BEGIN", nonce + "_AXIOMS_END"
    audit = (
        f'\nrun_meta Lean.logInfo "{audit_begin}"\n'
        f'#print axioms _root_.{audit_root}\n'
        f'run_meta Lean.logInfo "{audit_end}"\n'
    ) if audit_root else ""
    path.write_text(content + "\n" + _CONTRACT_PROBE.replace(
        "__PRESENTATION_MARKER__", marker) + audit, encoding="utf-8")
    proc = subprocess.run(
        ["lake", "env", "lean", str(path.resolve())], cwd=project,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=timeout_s, check=False,
        env=sanitized_subprocess_environment(_export_lean_env(extra_lean_paths)),
    )
    output = str(proc.stdout or "")
    if len(output.encode()) > MAX_PROBE_BYTES:
        raise ValueError("presentation probe output exceeded limit")
    if not _export_lean_verdict(proc.returncode, output)[0]:
        raise ValueError("presentation Lean replay failed: " + output[-1500:])
    if audit_root:
        # Contract JSON can contain String values resembling #print output.
        # Only the fresh, nonce-delimited directive is audit evidence.
        if output.count(audit_begin) != 1 or output.count(audit_end) != 1:
            raise ValueError("presentation axiom receipt missing or ambiguous")
        audit_output = output.split(audit_begin, 1)[1]
        if audit_end not in audit_output:
            raise ValueError("presentation axiom receipt out of order")
        audit_output = audit_output.split(audit_end, 1)[0]
        axioms = _parse_print_axioms(audit_output, audit_root)
        if not _axiom_audit_verdict(axioms)[0]:
            raise ValueError("presentation candidate failed axiom audit")
        if audit_axioms is not None:
            audit_axioms.extend(axioms or [])
    payloads = [line.split(marker, 1)[1] for line in output.splitlines() if marker in line]
    if len(payloads) != 1:
        raise ValueError("presentation contract receipt missing or ambiguous")
    receipt = json.loads(payloads[0])
    rows = receipt["records"]
    if command_spans is not None:
        raw = content.encode("utf-8")
        spans = [span for span in receipt["commands"] if span["end"] <= len(raw)]
        offsets = sorted({offset for span in spans for offset in (span["start"], span["end"])})
        char_offsets = {}
        previous = chars = 0
        for offset in offsets:
            if offset < 0 or offset > len(raw):
                raise ValueError("presentation command offset out of bounds")
            chars += len(raw[previous:offset].decode("utf-8"))
            char_offsets[offset] = chars
            previous = offset
        command_spans.extend({**span, "start": char_offsets[span["start"]],
                              "end": char_offsets[span["end"]]} for span in spans)
    records = {row["name"]: row for row in rows}
    if len(records) != len(rows):
        raise ValueError("duplicate presentation contract declarations")
    return records


def present_export(content: str, root: str, *, scratch_dir: Path,
                   project: Path, timeout_s: float = MAX_PRESENTATION_SECONDS,
                   extra_lean_paths: Sequence[Path] = ()) -> PresentationResult:
    """Propose, replay, compare, and audit; never turn cleanup failure into loss."""
    root = root.removeprefix("_root_.")
    fallback = PresentationResult(content)
    deadline = time.monotonic() + min(MAX_PRESENTATION_SECONDS, max(0.0, timeout_s))

    def remaining() -> float:
        seconds = deadline - time.monotonic()
        if seconds < 1.0:
            raise TimeoutError("presentation time allowance exhausted")
        return seconds

    try:
        if len(content.encode()) > MAX_SOURCE_BYTES:
            fallback.reason = "source_size_limit"
            return fallback
        remaining()
        pruned, removed = _prune_unused(content, root, deadline=deadline)
        readable = any(_needs_readable_type(pruned, d) for d in _editable_declarations(pruned))
        if not removed and not readable:
            return fallback
        with tempfile.TemporaryDirectory(prefix=".presentation-check-", dir=scratch_dir) as tmp:
            # Both replays use the same module path: private declaration names
            # must not differ merely because the temporary filename changed.
            path = Path(tmp) / "Proof.lean"
            commands: list[dict[str, Any]] = []
            before = _probe(content, path, project=project, timeout_s=remaining(),
                            extra_lean_paths=extra_lean_paths, command_spans=commands)
            if not commands:
                raise ValueError("presentation command receipt missing")
            pruned, removed = _prune_unused(content, root, deadline=deadline, command_spans=commands)
            candidate, rewritten = _rewrite_types(pruned, before)
            choices = [(candidate, rewritten)]
            if rewritten and removed:
                choices.append((pruned, []))
            for candidate, rewritten in choices:
                if candidate == content:
                    continue
                try:
                    candidate_axioms: list[str] = []
                    after = _probe(candidate, path, project=project, timeout_s=remaining(),
                                   extra_lean_paths=extra_lean_paths, audit_root=root,
                                   audit_axioms=candidate_axioms)
                    if not _same_contract(before, after, removed, root):
                        raise ValueError("presentation changed the declaration contract")
                    return PresentationResult(candidate, "applied", "checked", removed, rewritten,
                                              axioms=candidate_axioms)
                except Exception as exc:
                    fallback.status = "fallback"
                    fallback.reason = f"{type(exc).__name__}: {exc}"[:2000]
    except Exception as exc:
        fallback.status = "fallback"
        fallback.reason = f"{type(exc).__name__}: {exc}"[:2000]
    return fallback


def _atomic_text(path: Path, text: str) -> None:
    fd, name = tempfile.mkstemp(prefix=".presentation-", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
        os.chmod(name, 0o664)
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def archive_original(out_path: Path, original: str, result: PresentationResult) -> None:
    """Keep the original before allowing changed bytes to be installed."""
    if result.status != "applied":
        return
    archive = out_path.parent / ".presentation" / (_digest(original) + ".lean")
    archive.parent.mkdir(parents=True, exist_ok=True)
    _atomic_text(archive, original)
    result.original_path = str(archive.relative_to(out_path.parent))


def write_report(out_path: Path, original: str, result: PresentationResult) -> None:
    _atomic_text(out_path.with_suffix(".presentation.json"),
                 json.dumps(result.report(original), indent=2, ensure_ascii=False) + "\n")
