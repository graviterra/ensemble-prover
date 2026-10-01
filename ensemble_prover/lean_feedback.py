"""Conditional Lean feedback, deliberately separate from proof authority."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Callable, Optional, Sequence
import uuid

from .lean_parser import LeanParseResult, parse_lean_output

if TYPE_CHECKING:
    from .lean_runner import LeanRunner


@dataclass(frozen=True)
class FeedbackLeanResult:
    """A check under explicitly assumed helper signatures, never a certificate.

    There is deliberately no ``ok`` field or proof/axiom receipt, so generic
    authoritative result consumers cannot mistake this for ``LeanResult``.
    """

    accepted: bool
    output: str
    file_path: str
    returncode: int = 1
    parsed: Optional[LeanParseResult] = field(default=None, repr=False)
    generated_goal_start_line: int = 0
    generated_lemma_line_spans: tuple[tuple[int, int], ...] = ()


def _feedback_audit_blocks(identity: str) -> tuple[str, str, str]:
    """Freeze helper assumptions with Lean names before checking the proof."""
    baseline = f"ensemble_feedback_baseline_{identity}"
    context = f"ensemble_feedback_assumptions_{identity}"
    capture = f"ensemble_feedback_capture_{identity}"
    audit = f"ensemble_feedback_audit_{identity}"
    names_type = (
        "Lean.mkApp (Lean.mkConst ``List [Lean.Level.zero]) (Lean.mkConst ``Lean.Name)"
    )
    before = f"""
unsafe def _root_.{capture} : Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]
  let names := env.constants.map₂.toList.filterMap fun (name, info) =>
    match info with
    | .axiomInfo _ =>
      if env.isImportedConst name || forbidden.contains name then none else some name
    | _ => none
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {{
    name := `{context}, levelParams := [], type := {names_type},
    value := Lean.toExpr names, hints := .opaque, safety := .safe
  }}
unsafe def _root_.{audit} : Lean.Elab.Command.CommandElabM Unit := do
  let baseline ← Lean.Elab.Command.liftTermElabM <|
    Lean.Meta.evalExpr (List Lean.Name) ({names_type}) (Lean.mkConst `{baseline})
  let context ← Lean.Elab.Command.liftTermElabM <|
    Lean.Meta.evalExpr (List Lean.Name) ({names_type}) (Lean.mkConst `{context})
  let known := baseline.foldl (fun set name => set.insert name) ({{}} : Lean.NameSet)
  let allowed := [`propext, `Classical.choice, `Quot.sound] ++ context
  for (name, _) in (← Lean.getEnv).constants.map₂.toList do
    unless known.contains name do
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          Lean.throwError m!"unapproved axiom in conditional feedback: {{axiomName}}"
  Lean.logInfo "ENSEMBLE_CONDITIONAL_FEEDBACK_{identity}"
"""
    snapshot = f"""
run_cmd do
  let names := (← Lean.getEnv).constants.map₂.toList.map (·.1)
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {{
    name := `{baseline}, levelParams := [], type := {names_type},
    value := Lean.toExpr names, hints := .opaque, safety := .safe
  }}
"""
    return (
        before + snapshot,
        f"\nrun_cmd _root_.{capture}\n",
        f"\nrun_cmd _root_.{audit}\n",
    )


async def check_feedback(
    runner: LeanRunner,
    statement: str,
    proof_code: str,
    lemmas: Sequence[str],
    *,
    candidate_lemmas: Sequence[str] = (),
    preamble_override: str | None = None,
    timeout_s: Optional[float] = None,
    fast_fail_timeout_s: Optional[float] = None,
    max_heartbeats: Optional[int] = None,
    check_kind: str = "feedback",
    warning_as_error: bool = False,
    dispatch_observer: Optional[Callable[[], None]] = None,
) -> FeedbackLeanResult:
    # Local import keeps the public result type available from lean_runner.
    from .config import _append_imports_to_preamble
    from .lean_runner import (
        _check_meta_escape_violation,
        _check_source_boundary_file,
        _free_universe_decl,
        _name_anonymous_check_roots,
    )
    from .theorem_project import decode_theorem_target_context

    del check_kind  # A caller cannot relabel this execution as authoritative.
    deadline = runner._execution_deadline(timeout_s)
    if max_heartbeats is None:
        configured_heartbeats = getattr(runner, "default_max_heartbeats", None)
        if isinstance(configured_heartbeats, int) and configured_heartbeats > 0:
            max_heartbeats = configured_heartbeats
    helpers = "\n".join(str(item) for item in lemmas)
    candidate_helpers = "\n".join(str(item) for item in candidate_lemmas)
    identity = uuid.uuid4().hex
    goal_name = f"_root_.ensemble_feedback_goal_{identity}"
    preamble = _append_imports_to_preamble(
        runner._resolve_preamble(preamble_override, proof_code=proof_code), ["Lean"]
    )
    violation = _check_meta_escape_violation(
        statement, proof_code, helpers, candidate_helpers
    )
    if violation:
        output = "error: conditional feedback: forbidden meta-programming construct"
        return FeedbackLeanResult(
            False, output, "", parsed=parse_lean_output(output, 1)
        )
    await runner.ensure_project_imports_built()
    await runner._ensure_extra_imports_built(
        runner._required_extra_imports_for_proof(proof_code)
    )
    boundary = _check_source_boundary_file(
        preamble,
        statement,
        proof_code,
        helpers,
        goal_name=goal_name,
        max_heartbeats=max_heartbeats,
        allow_feedback_axioms=True,
        candidate_lemmas=candidate_helpers,
    )
    path, execution, write_error = await runner._execute_generated_file(
        mode="conditional_feedback_source_boundary",
        goal_name=f"feedback_boundary_{identity}",
        content=boundary,
        timeout_s=timeout_s,
        warning_as_error=False,
        operation_deadline=deadline,
    )
    if execution is None or execution.returncode != 0:
        output = str(
            execution.output
            if execution is not None
            else write_error or "feedback boundary unavailable"
        )
        code = execution.returncode if execution is not None else 1
        return FeedbackLeanResult(
            False, output, str(path or ""), code, parse_lean_output(output, code)
        )

    # Anonymous examples otherwise disappear from the environment and evade
    # the final dependency audit. Preserve their syntax under named roots,
    # using the same transformation as the authoritative checker.
    helpers = "\n".join(
        _name_anonymous_check_roots(str(block), block_index=index)[0]
        for index, block in enumerate(lemmas)
    )
    candidate_helpers = "\n".join(
        _name_anonymous_check_roots(str(block), block_index=len(lemmas) + index)[0]
        for index, block in enumerate(candidate_lemmas)
    )
    preamble, target_prefix, target_omit = decode_theorem_target_context(preamble)
    universes = _free_universe_decl(
        "\n".join((statement, proof_code, helpers, candidate_helpers)),
        declared_in=preamble,
    )
    before, after_helpers, after_goal = _feedback_audit_blocks(identity)
    heartbeat = (
        f"set_option maxHeartbeats {max_heartbeats}\n"
        if isinstance(max_heartbeats, int) and max_heartbeats > 0
        else ""
    )
    before_helpers = f"{preamble}\n\n{universes}\n{heartbeat}{before}\n"
    line = before_helpers.count("\n") + 1
    spans = []
    for helper in lemmas:
        end = line + str(helper).count("\n")
        spans.append((line, end))
        line = end + 1
    prefix = f"{before_helpers}{helpers}\n{after_helpers}\n"
    line = prefix.count("\n") + 1
    for helper in candidate_lemmas:
        end = line + str(helper).count("\n")
        spans.append((line, end))
        line = end + 1
    prefix += candidate_helpers + "\n\n"
    goal = f"opaque {goal_name} : {statement} := {proof_code}\n"
    if target_omit:
        goal = f"omit {' '.join(target_omit)} in\n{goal}"
    if target_prefix:
        goal = f"{target_prefix}\n{goal}"
    goal_line = prefix.count("\n") + 1
    path, execution, write_error = await runner._execute_generated_file(
        mode="conditional_feedback",
        goal_name=f"feedback_{identity}",
        content=prefix + goal + after_goal,
        timeout_s=timeout_s,
        fast_fail_timeout_s=fast_fail_timeout_s,
        warning_as_error=warning_as_error,
        dispatch_observer=dispatch_observer,
        operation_deadline=deadline,
    )
    output = str(
        execution.output
        if execution is not None
        else write_error or "feedback execution unavailable"
    )
    code = execution.returncode if execution is not None else 1
    parsed = parse_lean_output(output, code, goal_start_line=goal_line)
    accepted = (
        code == 0
        and parsed.ok
        and f"ENSEMBLE_CONDITIONAL_FEEDBACK_{identity}" in output
    )
    return FeedbackLeanResult(
        accepted, output, str(path or ""), code, parsed, goal_line, tuple(spans)
    )
