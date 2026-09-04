"""Answer-safe scratch Lean tool for the mini prover."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence

from .lean_parser import (
    canonical_error_type,
    diagnostic_preview,
    fallback_error_type_from_text,
)
from .lean_resource_guard import (
    DANGEROUS_NAT_POW_TOWER_REASON,
    should_block_expensive_nat_pow_probe,
)
from .lean_syntax import lean_expression_delimiters_balanced
from .mini_lean_extract import (
    _find_top_level_assign,
    _is_safe_leading_open_command,
    _scope_helper_with_open_commands,
    _strip_lean_comments_and_strings,
)
from .mini_lean_repairs import (
    rejection_supports_single_line_layout_repair,
    repair_single_line_by_tactic_block,
)
from .mini_deadline_transaction import DeadlineMutationTransaction
from .proof_dossier import (
    ProofDossier,
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
)
from .proof_graph import (
    graph_statement_is_executable,
    helper_decl_body,
    helper_decl_kind,
    helper_decl_name,
    helper_decl_statement,
)
from .theorem_project import scan_lean_imports
from .utils import extract_code_fences, has_sorry_or_admit


TRY_LEAN_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "try_lean",
        "description": (
            "SCRATCH verifier. Run a small Lean proof body against the current "
            "goal in the answer-safe environment shown in the prompt. Use it "
            "to test a concrete proof fragment before submitting the final "
            "answer. The `code` should usually be a `by ...` proof body for "
            "the current theorem goal. For target-integrity or counterexample "
            "evidence, `code` may be one complete top-level "
            "`example : ... := by ...` scratch declaration. When the prompt "
            "explicitly says the "
            "selected graph task still needs formalization, `code` must instead "
            "be one complete theorem/lemma proposition declaration with its proof. Do not "
            "include imports, axioms, #check, or option changes; use check_lean "
            "for declaration lookups."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": (
                        "Active-turn Lean artifact to test: usually a proof body "
                        "starting with `by`; when the active prompt requires "
                        "formalization, use one complete named theorem or lemma "
                        "declaration instead."
                    ),
                },
                "purpose": {
                    "type": "string",
                    "description": "Short reason for the scratch check.",
                },
            },
            "required": ["code"],
        },
    },
}


_FORBIDDEN_SCRATCH_RE = re.compile(
    r"(?m)^\s*(#\w+|import\b|axiom\b|set_option\b|attribute\b|local\b)"
)
_EXAMPLE_DECL_RE = re.compile(r"^\s*example(?=\s|[:({\[])")
_EMBEDDED_EXAMPLE_DECL_RE = re.compile(r"(?<!\S)example(?=\s|[:({\[])")
_PRELUDE_RESERVED_TOKENS = frozenset(
    {
        "abbrev",
        "attribute",
        "axiom",
        "class",
        "constant",
        "def",
        "end",
        "example",
        "export",
        "in",
        "include",
        "inductive",
        "instance",
        "lemma",
        "local",
        "macro",
        "mutual",
        "namespace",
        "notation",
        "opaque",
        "omit",
        "open",
        "run_cmd",
        "section",
        "set_option",
        "structure",
        "syntax",
        "theorem",
        "universe",
        "variable",
    }
)
_EXTRA_EXAMPLE_COMMAND_RE = re.compile(
    r"(?<![\w'.«])"
    r"(?:#\w+|import|axiom|constant|opaque|irreducible_def|structure|class|inductive|"
    r"coinductive|mutual|theorem|lemma|def|abbrev|instance|example|"
    r"namespace|section|end|variable|variables|universe|universes|"
    r"set_option|unset_option|attribute|register_simp_attr|register_option|syntax|"
    r"macro|macro_rules|elab|elab_rules|notation|infix|prefix|postfix|"
    r"initialize|builtin_initialize|declare_syntax_cat|export|alias|"
    r"run_cmd|local|include|omit|recall|suppress_compilation|"
    r"unsuppress_compilation)"
    r"(?![\w'»])"
)


@dataclass
class TryLeanOutcome:
    ok: bool
    summary: str
    output_preview: str = ""
    error_type: str = ""
    remaining_goals: List[str] = field(default_factory=list)


def _strip_fence(src: str) -> str:
    text = str(src or "").strip()
    blocks = extract_code_fences(text)
    if blocks:
        return blocks[0].strip()
    return text


def _is_example_declaration(src: str) -> bool:
    return bool(_EXAMPLE_DECL_RE.match(str(src or "")))


def _example_has_extra_command(src: str) -> bool:
    """Whether a scratch example contains another environment command.

    Lean accepts adjacent top-level commands without line breaks, so the
    ordinary line-anchored scratch policy is insufficient here.  Masking
    comments and strings first prevents explanatory text from false-firing.
    The scan is deliberately conservative because examples are evidence only,
    never the final proof artifact.
    """

    masked = _strip_lean_comments_and_strings(src)
    leading = _EXAMPLE_DECL_RE.match(masked)
    if leading is None:
        return True
    return _EXTRA_EXAMPLE_COMMAND_RE.search(masked, leading.end()) is not None


def _isolate_example_declaration(src: str) -> str:
    """Put the entire supplied example body inside one term boundary.

    Lean commands need not start on a new line: ``by trivial axiom ...`` can
    elaborate as an example followed by an axiom.  A command blacklist cannot
    stay complete.  Instead, locate the example's top-level ``:=`` and wrap
    *all* remaining source in parentheses.  A valid proof term is unchanged
    semantically, while any adjacent command is trapped before the unmatched
    closing parenthesis and makes the whole Lean check fail.
    """

    text = str(src or "").strip()
    leading = _EXAMPLE_DECL_RE.match(text)
    if leading is None:
        return ""
    after = text[leading.end() :]
    separator_end = _find_top_level_assign(after)
    if separator_end < 0:
        return ""
    header = after[: max(0, separator_end - 2)].rstrip()
    body = after[separator_end:].strip()
    if not body or not lean_expression_delimiters_balanced(body):
        return ""
    return f"example{header} := (\n{body}\n)"


def _normalize_redundant_example_prelude(
    src: str,
    *,
    preamble: str,
) -> tuple[str, bool]:
    """Normalize a safe import/open prelude before one scratch ``example``.

    Models sometimes serialize the answer-safe environment together with the
    requested example, even though the tool already supplies that environment.
    Redundant imports are accepted only when the frozen tool preamble already
    imports that exact module and are never executed.  Safe ``open`` commands
    are retained as command-local scopes around the example, so normalization
    cannot silently change unqualified name resolution.  Any other prefix or
    any second command after the example remains fail-closed.
    """

    text = str(src or "").strip()
    match = _EMBEDDED_EXAMPLE_DECL_RE.search(text)
    if match is None or match.start() <= 0:
        return text, False
    prefix = text[: match.start()].strip()
    tokens = prefix.split()
    if not tokens:
        return text, False
    available_imports = set(scan_lean_imports(preamble))
    cursor = 0
    commands = 0
    open_commands: list[str] = []
    while cursor < len(tokens):
        command = tokens[cursor]
        if command not in {"import", "open"}:
            return text, False
        commands += 1
        cursor += 1

        if command == "import":
            # The observed malformed call repeated one already-frozen import.
            # Restrict recovery to that exact semantic no-op; dropping a new
            # or malformed module could otherwise turn invalid source valid.
            if cursor >= len(tokens) or tokens[cursor] not in available_imports:
                return text, False
            cursor += 1
            if cursor < len(tokens) and tokens[cursor] not in {"import", "open"}:
                return text, False
            continue

        command_tokens = ["open"]
        while cursor < len(tokens) and tokens[cursor] not in {"import", "open"}:
            token = tokens[cursor]
            if token in _PRELUDE_RESERVED_TOKENS:
                return text, False
            command_tokens.append(token)
            cursor += 1
        open_command = " ".join(command_tokens)
        if not _is_safe_leading_open_command(open_command):
            return text, False
        open_commands.append(open_command)
    if commands <= 0:
        return text, False
    example = text[match.start() :].strip()
    if _example_has_extra_command(example):
        return text, False
    isolated_example = _isolate_example_declaration(example)
    if not isolated_example:
        return text, False
    return (
        _scope_helper_with_open_commands(isolated_example, open_commands),
        True,
    )


def _compact(
    text: Any,
    limit: int = 700,
    *,
    redact_solution_refs: bool = True,
    lean_diagnostic: bool = False,
) -> str:
    sanitizer = (
        _prompt_safe_lean_diagnostic_text
        if lean_diagnostic
        else _prompt_safe_inline_text
    )
    return sanitizer(
        str(text or ""),
        limit=limit,
        redact_solution_refs=redact_solution_refs,
    )


def _summarize_result(
    result: Any,
    *,
    redact_solution_refs: bool = True,
    suppress_helper_warnings: bool = False,
    submitted_code_line_span: Optional[tuple[int, int]] = None,
) -> TryLeanOutcome:
    ok = bool(getattr(result, "ok", False))
    if ok:
        return TryLeanOutcome(ok=True, summary="Lean accepted the scratch proof.")

    raw = str(getattr(result, "output", "") or "")
    parsed = getattr(result, "parsed", None)
    try:
        error_type = canonical_error_type(parsed) if parsed is not None else ""
    except Exception:
        error_type = ""
    if not error_type:
        error_type = fallback_error_type_from_text(raw) or "lean_rejected"

    diagnostics: List[str] = []
    diagnostic_source_note = ""
    if parsed is not None:
        raw_diagnostics = list(getattr(parsed, "diagnostics", []) or [])
        error_diagnostics = [
            diag
            for diag in raw_diagnostics
            if str(getattr(diag, "severity", "") or "").lower() == "error"
        ]
        # Warnings such as unused binders are useful only after the actual
        # rejection is visible.  Reserve the diagnostic budget for every
        # available error first and admit at most one warning alongside them.
        # When the scratch check carried context helpers, that lone warning is
        # almost always emitted by one of those (previously-accepted) helper
        # declarations — NOT by the model's proof body this turn — and the model
        # cannot act on it. Surfacing it makes the model mis-attribute the
        # warning to its own goal (observed: it hallucinated "residual state from
        # a previous apply" from a helper's `Apply builder ... A ↔ B` warning and
        # burned turns), so drop warnings entirely alongside a real error here.
        if error_diagnostics:
            warning_budget = 0 if suppress_helper_warnings else 1
            warning_diagnostics = [
                diag
                for diag in raw_diagnostics
                if str(getattr(diag, "severity", "") or "").lower()
                == "warning"
            ][:warning_budget]
            raw_diagnostics = [*error_diagnostics, *warning_diagnostics]

            goal_start_line = getattr(result, "generated_goal_start_line", 0)
            if isinstance(goal_start_line, int) and goal_start_line > 0:
                error_lines = [
                    line
                    for diag in error_diagnostics
                    if isinstance((line := getattr(diag, "line", None)), int)
                    and line > 0
                ]
                submitted_start = 0
                submitted_end = -1
                if submitted_code_line_span is not None:
                    submitted_start, submitted_end = submitted_code_line_span

                def is_submitted_line(line: int) -> bool:
                    return submitted_start > 0 and submitted_start <= line <= submitted_end

                has_context_error = any(
                    line < goal_start_line and not is_submitted_line(line)
                    for line in error_lines
                )
                has_goal_error = any(
                    line >= goal_start_line or is_submitted_line(line)
                    for line in error_lines
                )
                if has_context_error and has_goal_error:
                    diagnostic_source_note = (
                        "Source ownership: diagnostics span the supplied "
                        "context and the submitted scratch goal. The context "
                        "failed first, so later goal elaboration may rely on "
                        "Lean error recovery and cannot verify the proof; the "
                        "goal diagnostics are still errors in the submitted "
                        "scratch block."
                    )
                elif has_context_error:
                    diagnostic_source_note = (
                        "Source ownership: the supplied context failed before "
                        "the submitted scratch goal. This check cannot verify "
                        "the submitted proof: Lean may continue elaboration "
                        "using error recovery. Any `sorryAx` reported after "
                        "this failure is not proof evidence."
                    )
                elif has_goal_error:
                    diagnostic_source_note = (
                        "Source ownership: this diagnostic is inside the "
                        "submitted scratch goal or its audit block, not an "
                        "ignorable harness diagnostic; the proof was not accepted."
                    )

        def diagnostic_rank(item: tuple[int, Any]) -> tuple[int, int]:
            index, diag = item
            severity = str(getattr(diag, "severity", "") or "").lower()
            message = str(
                getattr(diag, "message", "")
                or getattr(diag, "summary", "")
                or ""
            ).lower()
            if severity == "error" or "error:" in message:
                return (0, index)
            if severity == "warning" or "warning:" in message:
                return (1, index)
            return (2, index)

        seen_diagnostics: set[str] = set()
        for _index, diag in sorted(
            enumerate(raw_diagnostics),
            key=diagnostic_rank,
        ):
            msg = diagnostic_preview(
                str(getattr(diag, "message", "") or ""),
                canonical_error=error_type,
            )
            if not msg:
                msg = str(getattr(diag, "summary", "") or "")
            loc = ""
            line = getattr(diag, "line", None)
            col = getattr(diag, "col", None)
            if line is not None and col is not None:
                loc = f"line {line}, col {col}: "
            diagnostics.append(
                _compact(
                    f"{loc}{msg}",
                    260,
                    redact_solution_refs=redact_solution_refs,
                    lean_diagnostic=True,
                )
            )
            if diagnostics[-1] in seen_diagnostics:
                diagnostics.pop()
                continue
            seen_diagnostics.add(diagnostics[-1])
            if len(diagnostics) >= 3:
                break

    mismatch_details: List[str] = []
    if parsed is not None and (
        error_type == "type_mismatch"
        or bool(getattr(parsed, "type_mismatch", False))
        or bool(getattr(parsed, "actual_type", None))
        or bool(getattr(parsed, "expected_type", None))
    ):
        actual_type = _compact(
            getattr(parsed, "actual_type", "") or "",
            320,
            redact_solution_refs=redact_solution_refs,
            lean_diagnostic=True,
        )
        expected_type = _compact(
            getattr(parsed, "expected_type", "") or "",
            320,
            redact_solution_refs=redact_solution_refs,
            lean_diagnostic=True,
        )
        if actual_type:
            mismatch_details.append(f"actual `{actual_type}`")
        if expected_type:
            mismatch_details.append(f"expected `{expected_type}`")

    remaining: List[str] = []
    if parsed is not None:
        for goal in list(getattr(parsed, "remaining_goals", []) or [])[:2]:
            target = _compact(
                getattr(goal, "target", ""),
                360,
                redact_solution_refs=redact_solution_refs,
                lean_diagnostic=True,
            )
            if target:
                remaining.append(target)

    parts = [f"Lean rejected the scratch proof ({error_type})."]
    if diagnostic_source_note:
        parts.append(diagnostic_source_note)
    if diagnostics:
        parts.append("Diagnostics: " + " | ".join(diagnostics))
    if mismatch_details:
        parts.append("Type mismatch: " + "; ".join(mismatch_details) + ".")
    if remaining:
        parts.append("Remaining goals: " + " | ".join(remaining))
    if not diagnostics and not remaining:
        parts.append(
            _compact(
                raw,
                500,
                redact_solution_refs=redact_solution_refs,
                lean_diagnostic=True,
            )
        )
    return TryLeanOutcome(
        ok=False,
        summary=" ".join(part for part in parts if part),
        output_preview=_compact(
            raw,
            900,
            redact_solution_refs=redact_solution_refs,
            lean_diagnostic=True,
        ),
        error_type=error_type,
        remaining_goals=remaining,
    )


async def _run_try_lean_tool_impl(
    lean: Any,
    *,
    goal_statement: str,
    preamble: str,
    args: Dict[str, Any],
    context_lemmas: Optional[Sequence[str]] = None,
    dossier: Optional[ProofDossier] = None,
    turn_index: int = 0,
    tool_call_index: int = 0,
    # None: wait for the live scratch check. A 120s asyncio knife cancelled
    # and detached the wrapper, discarded a late success, and left later
    # verify parked behind that leaked lock. Kernel heartbeats remain the
    # step bound; ``lean.check(timeout_s=None)`` uses the runner config.
    timeout_s: Optional[float] = None,
    # Plumb a maxHeartbeats budget so `tsum` elaboration in ℚ has enough
    # kernel-step budget. Matches the production --lean-max-heartbeats
    # default — otherwise the LLM's scratch tests would fail at a lower
    # budget than the real verification, tricking the model into thinking
    # its proof is wrong when the real check would have succeeded.
    # None preserves Lean's built-in default (200k).
    max_heartbeats: Optional[int] = 1600000,
    redact_solution_refs: bool = True,
    allow_declarations: bool = False,
    require_declaration: bool = False,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    accepted_code_out: Optional[Dict[str, str]] = None,
) -> str:
    """Run one answer-safe scratch proof check and return model-facing text."""
    code = _strip_fence(str(args.get("code", "") or ""))
    code, redundant_prelude_normalized = _normalize_redundant_example_prelude(
        code,
        preamble=preamble,
    )
    purpose = _compact(
        args.get("purpose", ""),
        160,
        redact_solution_refs=redact_solution_refs,
    )

    def deadline_elapsed() -> bool:
        try:
            return bool(deadline_exhausted and deadline_exhausted())
        except Exception:
            return True

    def record_preflight_error(message: str) -> str:
        if dossier is not None:
            dossier.record_scratch(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                ok=False,
                summary=message,
                code=code,
                goal_statement=goal_statement,
            )
        return message

    if not code:
        return record_preflight_error("try_lean error: empty `code`.")
    if _FORBIDDEN_SCRATCH_RE.search(code):
        return record_preflight_error(
            "try_lean error: scratch code may contain proof bodies and helper "
            "terms only; do not use imports, axioms, #commands, attributes, or "
            "top-level option changes."
        )
    decl_kind = helper_decl_kind(code)
    decl_name = helper_decl_name(code)
    declaration_mode = bool(decl_kind and decl_name)
    example_mode = bool(redundant_prelude_normalized or _is_example_declaration(code))
    if (
        example_mode
        and not redundant_prelude_normalized
        and _example_has_extra_command(code)
    ):
        return record_preflight_error(
            "try_lean error: scratch evidence must contain exactly one "
            "top-level `example` and no additional Lean commands."
        )
    if require_declaration and not declaration_mode:
        return record_preflight_error(
            "try_lean error: this formalization scratch target requires one "
            "complete theorem or lemma declaration, not a proof body."
        )
    if declaration_mode and not allow_declarations:
        return record_preflight_error(
            "try_lean error: this scratch target expects a proof body, not a "
            "top-level declaration."
        )
    if declaration_mode:
        if decl_kind not in {"theorem", "lemma"}:
            return record_preflight_error(
                "try_lean error: formalization declarations must be theorem or "
                "lemma propositions with complete proofs."
            )
        statement = helper_decl_statement(code)
        body = helper_decl_body(code)
        if not statement or not body:
            return record_preflight_error(
                "try_lean error: formalization declarations must include an "
                "executable statement and a complete proof body."
            )
        if not graph_statement_is_executable(statement):
            return record_preflight_error(
                "try_lean error: formalization declarations must state an "
                "executable Lean proposition, not data or prose."
            )
        if has_sorry_or_admit(body):
            return record_preflight_error(
                "try_lean error: formalization declarations must be fully proved; "
                "`sorry`/`admit` stubs are not accepted."
            )
    if example_mode and has_sorry_or_admit(code):
        return record_preflight_error(
            "try_lean error: scratch examples must be fully proved; "
            "`sorry`/`admit` stubs are not accepted."
        )
    proof_body_prefixes = ("by", "show", "calc", "exact", "refine", "fun")
    if (
        not declaration_mode
        and not example_mode
        and not code.lstrip().startswith(proof_body_prefixes)
    ):
        return record_preflight_error(
            "try_lean error: provide a proof body for the current goal, usually "
            "starting with `by`, or a complete top-level `example` scratch "
            "declaration for target-integrity evidence."
        )
    if should_block_expensive_nat_pow_probe(goal_statement=goal_statement, code=code):
        return record_preflight_error(
            "try_lean rejected by preflight: "
            f"{DANGEROUS_NAT_POW_TOWER_REASON}. Avoid `ring`, `ring_nf`, "
            "`norm_num`, `decide`, or `native_decide` here; prove symbolic "
            "power identities with lemmas such as `pow_add`, `pow_mul`, and "
            "monotonicity instead."
        )

    lemmas = list(context_lemmas or [])
    check_goal_statement = goal_statement
    check_code = code
    check_lemmas = lemmas
    if declaration_mode:
        check_goal_statement = "True"
        check_code = "by\n  trivial"
        lemmas = [*lemmas, code]
        check_lemmas = lemmas
    if example_mode:
        check_goal_statement = "True"
        check_code = "by\n  trivial"
        check_lemmas = [*lemmas, code]

    async def _check_with_compat(candidate_code: str) -> Any:
        checker = lean
        current = getattr(lean, "current_generation", None)
        if callable(current):
            try:
                live = current()
            except Exception:
                live = None
            if live is not None:
                checker = live
        try:
            return await checker.check(
                check_goal_statement,
                candidate_code,
                check_lemmas,
                preamble_override=preamble,
                timeout_s=timeout_s,
                max_heartbeats=max_heartbeats,
                check_kind="full",
            )
        except TypeError:
            pass
        try:
            return await checker.check(
                check_goal_statement,
                candidate_code,
                check_lemmas,
                preamble_override=preamble,
                timeout_s=timeout_s,
                max_heartbeats=max_heartbeats,
            )
        except TypeError:
            pass
        try:
            return await checker.check(
                check_goal_statement,
                candidate_code,
                check_lemmas,
                preamble_override=preamble,
                timeout_s=timeout_s,
            )
        except TypeError:
            pass
        return await checker.check(
            check_goal_statement,
            candidate_code,
            check_lemmas,
            preamble_override=preamble,
        )

    async def run_check() -> Any:
        return await _check_with_compat(check_code)

    from .proof_state_executor import (
        _LeanAdmissionDeferred,
        _await_serialized_lean_operation,
    )

    try:
        result = await _await_serialized_lean_operation(
            lean,
            run_check,
            timeout_s=timeout_s,
            operation_label="mini_tool_try_lean",
            release_unrecyclable_tail=True,
        )
    except _LeanAdmissionDeferred as exc:
        safe_exc_type = _prompt_safe_inline_text(
            type(exc).__name__,
            limit=120,
            redact_solution_refs=redact_solution_refs,
        )
        return f"try_lean infrastructure error: {safe_exc_type}"
    except Exception as exc:
        if deadline_elapsed():
            return (
                "try_lean cancelled: llm_turn_elapsed_budget_exhausted before "
                "this scratch error could be recorded."
            )
        safe_exc_type = _prompt_safe_inline_text(
            type(exc).__name__,
            limit=120,
            redact_solution_refs=redact_solution_refs,
        )
        summary = f"try_lean infrastructure error: {safe_exc_type}"
        if dossier is not None:
            dossier.record_scratch(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                ok=False,
                summary=summary,
                code=code,
                goal_statement=goal_statement,
            )
        return summary

    single_line_layout_repaired = False
    repaired_code = (
        None
        if declaration_mode or example_mode or bool(getattr(result, "ok", False))
        else repair_single_line_by_tactic_block(code)
    )
    if (
        repaired_code
        and rejection_supports_single_line_layout_repair(result)
        and not deadline_elapsed()
    ):
        try:
            async def run_repair_check() -> Any:
                return await _check_with_compat(repaired_code)

            repaired_result = await _await_serialized_lean_operation(
                lean,
                run_repair_check,
                timeout_s=timeout_s,
                operation_label="mini_tool_try_lean_repair",
                release_unrecyclable_tail=True,
            )
        except (_LeanAdmissionDeferred, Exception):
            repaired_result = None
        if repaired_result is not None and bool(getattr(repaired_result, "ok", False)):
            result = repaired_result
            code = repaired_code
            check_code = repaired_code
            single_line_layout_repaired = True

    if deadline_elapsed():
        return (
            "try_lean cancelled: llm_turn_elapsed_budget_exhausted before "
            "this scratch result could be recorded."
        )

    submitted_code_line_span: Optional[tuple[int, int]] = None
    if declaration_mode or example_mode:
        spans = tuple(getattr(result, "generated_lemma_line_spans", ()) or ())
        if spans and len(spans) >= len(check_lemmas):
            candidate_span = spans[len(check_lemmas) - 1]
            if (
                isinstance(candidate_span, tuple)
                and len(candidate_span) == 2
                and all(isinstance(value, int) for value in candidate_span)
            ):
                submitted_code_line_span = candidate_span

    outcome = _summarize_result(
        result,
        redact_solution_refs=redact_solution_refs,
        # Context helpers were in scope this check: drop a lone warning next to a
        # real error so a helper's warning is not mis-attributed to the goal.
        suppress_helper_warnings=bool(context_lemmas),
        submitted_code_line_span=submitted_code_line_span,
    )
    if dossier is not None:
        dossier.record_scratch(
            turn_index=turn_index,
            tool_call_index=tool_call_index,
            ok=outcome.ok,
            summary=outcome.summary,
            code=code,
            goal_statement=goal_statement,
        )
        if (
            outcome.ok
            and not example_mode
            and hasattr(dossier, "record_accepted_proof_stub")
        ):
            dossier.record_accepted_proof_stub(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                goal_statement=(
                    helper_decl_statement(code) if declaration_mode else goal_statement
                ),
                preamble=preamble,
                context_lemmas=check_lemmas,
                code=code,
            )
    if outcome.ok and isinstance(accepted_code_out, dict):
        accepted_code_out["code"] = code

    prefix = "try_lean accepted." if outcome.ok else "try_lean rejected."
    purpose_part = f" Purpose: {purpose}." if purpose else ""
    helper_part = (
        f" Named helpers supplied: {len(lemmas)}."
        if lemmas
        else " Named helpers supplied: 0."
    )
    normalization_part = (
        " Redundant prelude normalized: imports were not executed and opens "
        "were retained as local scopes."
        if redundant_prelude_normalized
        else ""
    )
    if single_line_layout_repaired:
        normalization_part += " Single-line tactic layout repaired and rechecked."
    return (
        f"{prefix}{purpose_part}{helper_part}{normalization_part}\n"
        f"{outcome.summary}"
    )


async def run_try_lean_tool(*args: Any, **kwargs: Any) -> str:
    """Run scratch validation without allowing a late dossier commit."""

    caller_accepted_code_out = kwargs.pop("accepted_code_out", None)
    accepted_code_receipt: Dict[str, str] = {}
    kwargs["accepted_code_out"] = accepted_code_receipt

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=kwargs.get("deadline_exhausted"),
        dossier=kwargs.get("dossier"),
        label="try_lean_tool",
    )
    with transaction:
        if not transaction.can_mutate():
            return (
                "try_lean cancelled: llm_turn_elapsed_budget_exhausted before "
                "this scratch check could start."
            )
        result = await _run_try_lean_tool_impl(*args, **kwargs)
        if not transaction.can_mutate():
            return (
                "try_lean cancelled: llm_turn_elapsed_budget_exhausted before "
                "this scratch result could be committed."
            )
    if transaction.enabled and not transaction.committed:
        return (
            "try_lean cancelled: "
            + (
                "llm_turn_elapsed_budget_exhausted"
                if transaction.deadline_won
                else "deadline_mutation_commit_failed"
            )
            + " before this scratch result could be committed."
        )
    if (
        isinstance(caller_accepted_code_out, dict)
        and str(accepted_code_receipt.get("code") or "").strip()
    ):
        caller_accepted_code_out["code"] = accepted_code_receipt["code"]
    return result
