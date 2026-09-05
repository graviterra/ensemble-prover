"""Lean admission for generated NL statements and mathematical definitions.

The supplied preamble (including its syntax extensions) is trusted caller code.
Generated declarations are restricted to mathematical declarations without
tactics, attributes, compiler evaluation, or filesystem inclusion. This is an
input policy, not an operating-system sandbox.
"""

from __future__ import annotations

import re
from collections.abc import Sequence

from .lean_runner import LeanRunner
from .utils import strip_lean_comments_and_string_literals

THEOREM_NAME = "nl_problem"
_CHECK_NAME = "_nlAdmissionChecked"
_FORBIDDEN = re.compile(
    r"\b(?:by|by_elab|sorry|sorryAx|admit|run_tac|unsafe|unsafeBaseIO|unsafeIO|"
    r"unsafeEIO|unsafeCast|from_lrat|include_str|include_bytes|set_option|"
    r"deriving|decreasing_by|partial)\b|\beval\s*%"
)


def check_generated_text(text: str) -> None:
    """Reject active source forms before any generated source is elaborated."""
    if not isinstance(text, str) or not text.strip():
        raise ValueError("generated Lean source must be nonempty text")
    scan = strip_lean_comments_and_string_literals(text)
    if _FORBIDDEN.search(scan):
        raise ValueError(
            "generated Lean must contain mathematical terms without tactic blocks, "
            "placeholders, compiler evaluation, filesystem inclusion, or unsafe code"
        )


def _lean_string(text: str) -> str:
    # JSON's \b and \f are not Lean escapes. Escape the actual characters once,
    # preserving both literal backslashes and every Unicode source character.
    escapes = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\r": "\\r", "\t": "\\t"}
    return (
        '"'
        + "".join(
            escapes.get(ch, f"\\u{ord(ch):04x}" if ord(ch) < 32 else ch) for ch in text
        )
        + '"'
    )


def render_candidate(
    statement: str, definitions: Sequence[str] = (), preamble: str = ""
) -> str:
    """Render exact generated source fragments with explicit separators."""
    return (
        preamble
        + "\n\n"
        + "\n\n".join(definitions)
        + f"\n\ntheorem {THEOREM_NAME} : (\n{statement}\n) := by\n  sorry\n"
    )


_GUARD = r"""
private partial def _nlAdmissionGuard (stx : Lean.Syntax) : Bool :=
  let bad := ["by", "by_elab", "sorry", "admit", "run_tac", "unsafe", "eval%",
    "from_lrat", "include_str", "include_bytes", "set_option", "deriving",
    "decreasing_by", "partial", "@["]
  match stx with
  | .atom _ value => !bad.contains value
  | .ident _ _ name _ =>
    !(["sorryAx", "unsafeBaseIO", "unsafeIO", "unsafeEIO", "unsafeCast"].contains name.toString)
  | .node _ _ args => args.all _nlAdmissionGuard
  | .missing => false
"""


def _validation_source(
    statement: str, definitions: Sequence[str], preamble: str
) -> str:
    commands = "\n".join(
        f"""
  let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command {_lean_string(definition)} with
    | .ok stx => pure stx
    | .error error => Lean.throwError error
  unless stx.isOfKind ``Lean.Parser.Command.declaration do
    Lean.throwError "expected one mathematical declaration"
  unless [``Lean.Parser.Command.definition, ``Lean.Parser.Command.abbrev,
      ``Lean.Parser.Command.structure, ``Lean.Parser.Command.inductive,
      ``Lean.Parser.Command.classInductive, ``Lean.Parser.Command.instance].contains stx[1].getKind do
    Lean.throwError "only mathematical def, abbrev, structure, inductive, class, and instance declarations are supported"
  unless _nlAdmissionGuard stx do
    Lean.throwError "generated declaration contains prohibited syntax"
  let name := if stx[1].isOfKind ``Lean.Parser.Command.instance then
    if stx[1][3].isNone then Lean.Name.anonymous else (Lean.Elab.expandDeclIdCore stx[1][3][0]).1
    else (Lean.Elab.expandDeclIdCore stx[1][1]).1
  if name == `nl_problem || name.toString.startsWith "_nlAdmission" then
    Lean.throwError "generated declaration uses a reserved name"
  let previous ← Lean.getEnv
  Lean.Elab.Command.elabCommand stx
  let current ← Lean.getEnv
  let names := current.constants.foldStage2 (fun names name _ => names.push name) (#[] : Array Lean.Name)
  for name in names do
    unless previous.contains name do
      let info ← Lean.getConstInfo name
      if info.isUnsafe || info.type.hasSorry || info.type.hasMVar || info.type.hasFVar || info.type.hasLooseBVars then
        Lean.throwError "generated declaration has unsafe code or unresolved type"
      if let some value := info.value? then
        if value.hasSorry || value.hasMVar || value.hasFVar || value.hasLooseBVars then
          Lean.throwError "generated definition has placeholders or an unresolved value"
      if (← Lean.collectAxioms name).contains `sorryAx then
        Lean.throwError "generated declaration depends on sorry"
"""
        for definition in definitions
    )
    return (
        "import Lean\n"
        + preamble
        + "\n"
        + _GUARD
        + "\nrun_cmd do\n"
        + (
            commands
            + f"""
  Lean.Elab.Command.liftTermElabM do
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term {_lean_string(statement)} with
      | .ok stx => pure stx
      | .error error => Lean.throwError error
    unless _nlAdmissionGuard stx do
      Lean.throwError "generated statement contains prohibited syntax"
    let expression ← Lean.Elab.Term.withoutErrToSorry do
      Lean.Elab.Term.elabTerm stx (some (Lean.mkSort Lean.Level.zero))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← Lean.instantiateMVars expression
    unless ← Lean.Meta.isProp expression do
      Lean.throwError "expected a proposition, not a data type or value"
    if expression.hasSorry || expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
      Lean.throwError "statement contains placeholders or unbound variables"
    for name in expression.getUsedConstants do
      if (← Lean.collectAxioms name).contains `sorryAx then
        Lean.throwError "statement depends on sorry"
def {_CHECK_NAME} : Prop := True
"""
        )
    )


async def validate_candidate(
    statement: str,
    *,
    definitions: Sequence[str],
    preamble: str,
    lean: LeanRunner,
    timeout_s: float,
) -> tuple[bool, str]:
    """Check parsed source, dependencies, and the actual rendered theorem file."""
    try:
        check_generated_text(statement)
        for definition in definitions:
            check_generated_text(definition)
    except ValueError as exc:
        return False, str(exc)
    ok, _, output = await lean.check_source_declaration_type(
        _validation_source(statement, definitions, preamble),
        _CHECK_NAME,
        timeout_s=timeout_s,
    )
    if not ok:
        return False, output
    ok, _, rendered_output = await lean.check_source_declaration_type(
        render_candidate(statement, definitions, preamble),
        THEOREM_NAME,
        timeout_s=timeout_s,
    )
    return ok, output + "\n" + rendered_output
