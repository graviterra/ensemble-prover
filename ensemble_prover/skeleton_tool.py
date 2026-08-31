"""Verified proof-skeleton banking tool for mini prover proof-state routes."""

from __future__ import annotations

import asyncio
import json
import re
import time
from typing import Any, Callable, Dict, List, Mapping, Optional

from .lean_parser import canonical_error_type, diagnostic_preview, parse_lean_output
from .mini_deadline_transaction import (
    DeadlineMutationTransaction,
    active_deadline_transaction,
)
from .math_utils import _strip_lean_comments_and_strings
from .proof_dossier import (
    ProofDossier,
    _contains_solution_ref_for_prompt,
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
    _redact_prompt_control_text,
    _redact_split_prompt_control_text,
)
from .proof_graph import (
    helper_decl_body,
    helper_decl_kind,
    helper_decl_statement,
)
from .proof_state import (
    ProofSearchState,
    ProofStateNode,
    canonicalize_lean_statement_for_identity,
)
from .proof_state_executor import (
    _LeanAdmissionDeferred,
    _await_serialized_lean_operation,
    _closed_false_residual_goal,
    _fully_funded_operation_timeout,
    _parent_stub_validation_variants,
    _proof_state_residual_lemmas,
    _proof_state_residual_preamble,
    _proof_state_verified_helper_blocks,
    _typed_residual_operation_timeout,
    _typed_residual_request_hashes,
)
from .try_lean_tool import _FORBIDDEN_SCRATCH_RE, _strip_fence
from .utils import has_sorry_or_admit


def _combined_deadline_predicate(
    deadline_exhausted: Optional[Callable[[], bool]],
    deadline_monotonic: float,
) -> Optional[Callable[[], bool]]:
    """Combine callback and absolute boundaries without adding a timeout."""

    try:
        absolute_deadline = float(deadline_monotonic or 0.0)
    except (TypeError, ValueError):
        return lambda: True
    if deadline_exhausted is None and absolute_deadline <= 0.0:
        return None

    def elapsed() -> bool:
        try:
            if deadline_exhausted is not None:
                if not callable(deadline_exhausted) or deadline_exhausted():
                    return True
            return bool(
                absolute_deadline > 0.0
                and time.monotonic() >= absolute_deadline
            )
        except Exception:
            # A failed deadline source must not allow a late route commit.
            return True

    return elapsed


TRY_SKELETON_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "try_skeleton",
        "description": (
            "ROUTE-CONSTRUCTOR tool. Use this when you can reduce the active "
            "Lean goal to smaller subgoals but cannot prove the leaves yet. "
            "Submit a partial proof body such as `by constructor` or "
            "`by refine And.intro ?_ ?_`; Lean must elaborate the scaffold "
            "and report remaining goals. Accepted skeletons are banked only "
            "as proof-state structure: they create open obligations and an "
            "assembly route, never proof evidence. Do not use `sorry` or "
            "`admit`; leave holes as `?_` or stop after the reducing tactic so "
            "Lean exposes the residual goals."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": (
                        "Partial Lean proof body for the active goal, usually "
                        "starting with `by`. It must leave residual goals, not "
                        "close them with `sorry`."
                    ),
                },
                "purpose": {
                    "type": "string",
                    "description": "Short description of the intended reduction.",
                },
            },
            "required": ["code"],
        },
    },
}


_PROOF_BODY_PREFIXES = (
    "by",
    "calc",
    "exact",
    "fun",
    "have",
    "if",
    "let",
    "match",
    "nomatch",
    "refine",
    "show",
)
_CONCLUSIVE_TYPED_RESIDUAL_REJECTIONS = {
    "residual_lean_rejected",
    "residual_parent_statement_missing",
    "residual_proof_stub_missing",
    "residual_proof_stub_contains_admission",
}
_TOP_LEVEL_COMMAND_HEADS = {
    "abbrev",
    "add_aesop_rules",
    "alias",
    "attribute",
    "assert_not_exists",
    "assert_no_sorry",
    "axiom",
    "class",
    "coinductive",
    "compile_def",
    "compile_inductive",
    "constant",
    "def",
    "declare_aesop_rule_sets",
    "declare_aesop_exception",
    "deprecate",
    "deprecated_module",
    "deriving",
    "declare_syntax_cat",
    "elab",
    "elab_rules",
    "end",
    "erase_aesop_rules",
    "example",
    "extend_docs",
    "export",
    "guard_min_heartbeats",
    "import",
    "include",
    "inductive",
    "initialize",
    "initialize_simps_projections",
    "insert_to_additive_translation",
    "infix",
    "infixl",
    "infixr",
    "instance",
    "lemma",
    "local",
    "library_note",
    "library_note2",
    "lrat_proof",
    "macro",
    "macro_rules",
    "mk_iff_of_inductive_prop",
    "mutual",
    "namespace",
    "name_poly_vars",
    "noncomputable",
    "notation",
    "notation3",
    "opaque",
    "omit",
    "open",
    "postfix",
    "prefix",
    "proof_wanted",
    "protected",
    "register_aesop_check_option",
    "register_hint",
    "register_option",
    "register_simp_attr",
    "recall",
    "run_cmd",
    "scoped",
    "section",
    "simproc",
    "set_option",
    "dsimproc",
    "stop_at_first_error",
    "structure",
    "suppress_compilation",
    "sudo",
    "syntax",
    "theorem",
    "to_dual_insert_cast",
    "to_dual_insert_cast_fun",
    "universe",
    "unsuppress_compilation",
    "unset_option",
    "unsafe",
    "variable",
    "variables",
    "whatsnew",
    "with_weak_namespace",
}
_TOP_LEVEL_COMMAND_MODIFIERS = {
    "nonrec",
    "noncomputable",
    "partial",
    "private",
    "protected",
    "unsafe",
}
_LEAN_ASCII_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


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


def _dossier_metric(dossier: Optional[ProofDossier], key: str, amount: int = 1) -> None:
    if dossier is None:
        return
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        try:
            increment(key, amount)
            return
        except Exception:
            pass
    metrics = getattr(dossier, "tool_metrics", None)
    if isinstance(metrics, dict):
        metrics[key] = int(metrics.get(key, 0) or 0) + int(amount or 0)


def _raw_prompt_unsafe_source(text: Any, *, redact_solution_refs: bool) -> bool:
    raw = str(text or "")
    if redact_solution_refs and _contains_solution_ref_for_prompt(raw):
        return True
    redacted = _redact_split_prompt_control_text(_redact_prompt_control_text(raw))
    return redacted != raw


def _json_result(payload: Mapping[str, Any]) -> str:
    return json.dumps(dict(payload), ensure_ascii=False, sort_keys=True)


def _reject(
    *,
    dossier: Optional[ProofDossier],
    reason: str,
    message: str,
    redact_solution_refs: bool,
    extra: Optional[Mapping[str, Any]] = None,
) -> str:
    _dossier_metric(dossier, "mini_try_skeleton_rejected", 1)
    payload: Dict[str, Any] = {
        "status": "rejected",
        "reason": str(reason or "rejected"),
        "summary": _compact(
            message,
            900,
            redact_solution_refs=redact_solution_refs,
            lean_diagnostic=True,
        ),
    }
    if extra:
        payload.update(dict(extra))
    return _json_result(payload)


def _normal_target_key(text: str) -> str:
    return canonicalize_lean_statement_for_identity(str(text or ""))


def _find_parent_node(
    proof_state: ProofSearchState,
    goal_statement: str,
) -> Optional[ProofStateNode]:
    nodes = getattr(proof_state, "nodes", {}) or {}
    root = nodes.get(getattr(proof_state, "root_node_id", ""))
    target_key = _normal_target_key(goal_statement)
    if not target_key:
        return root
    if root is not None and _normal_target_key(getattr(root, "target", "")) == target_key:
        return root
    for node in nodes.values():
        if getattr(node, "status", "") != "open":
            continue
        if _normal_target_key(getattr(node, "target", "")) == target_key:
            return node
    return None


def _extract_skeleton_body(code: str, goal_statement: str) -> tuple[str, str]:
    decl_kind = helper_decl_kind(code)
    if not decl_kind:
        return code.strip(), ""
    statement = helper_decl_statement(code)
    if _normal_target_key(statement) != _normal_target_key(goal_statement):
        return "", "declaration_statement_mismatch"
    body = helper_decl_body(code)
    if not body:
        return "", "declaration_missing_body"
    return body.strip(), ""


def _line_start_ident_tokens(text: str, max_tokens: int = 8) -> List[str]:
    tokens: List[str] = []
    cursor = 0
    raw = str(text or "")
    while len(tokens) < max(0, int(max_tokens or 0)):
        while cursor < len(raw) and raw[cursor].isspace():
            cursor += 1
        match = _LEAN_ASCII_IDENT_RE.match(raw, cursor)
        if match is None:
            break
        tokens.append(match.group(0))
        cursor = match.end()
        if cursor < len(raw) and not raw[cursor].isspace():
            break
    return tokens


def _lean_ident_tokens(text: str) -> set[str]:
    stripped, lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    source = stripped if lexically_closed else str(text or "")
    return {match.group(0) for match in _LEAN_ASCII_IDENT_RE.finditer(source)}


def _lean_ident_token_sequence(text: str) -> List[str]:
    stripped, lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    source = stripped if lexically_closed else str(text or "")
    return [match.group(0) for match in _LEAN_ASCII_IDENT_RE.finditer(source)]


def _has_plain_ident_reference(text: str, name: str) -> bool:
    """Return whether ``name`` appears as a non-projection identifier."""

    target = str(name or "").strip()
    if not target:
        return False
    stripped, lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    source = stripped if lexically_closed else str(text or "")
    for match in _LEAN_ASCII_IDENT_RE.finditer(source):
        if match.group(0) != target:
            continue
        prev_char = source[match.start() - 1] if match.start() > 0 else ""
        next_char = source[match.end()] if match.end() < len(source) else ""
        if prev_char == "." or next_char == ".":
            continue
        return True
    return False


def _top_level_command_reason_from_tokens(tokens: List[str], *, start: int = 0) -> str:
    cursor = max(0, int(start or 0))
    while cursor < len(tokens):
        token = tokens[cursor]
        if token.startswith("builtin_"):
            return "top_level_command_in_skeleton"
        if token in _TOP_LEVEL_COMMAND_HEADS:
            return f"top_level_{token}_in_skeleton"
        if token in _TOP_LEVEL_COMMAND_MODIFIERS:
            modifier_start = cursor
            while cursor < len(tokens) and tokens[cursor] in _TOP_LEVEL_COMMAND_MODIFIERS:
                cursor += 1
            if cursor < len(tokens):
                next_token = tokens[cursor]
                if next_token.startswith("builtin_"):
                    return "top_level_command_in_skeleton"
                if next_token in _TOP_LEVEL_COMMAND_HEADS:
                    return f"top_level_{next_token}_in_skeleton"
            return f"top_level_{tokens[modifier_start]}_in_skeleton"
        cursor += 1
    return ""


def _where_decl_reachability_reason(proof_stub: str) -> str:
    """Reject local ``where`` declarations that are not used by the parent route."""

    stripped, lexically_closed = _strip_lean_comments_and_strings(str(proof_stub or ""))
    body = stripped if lexically_closed else str(proof_stub or "")
    if "where" in _lean_ident_token_sequence(body):
        return "where_skeleton_unsupported"
    lines = body.splitlines()
    where_index = -1
    where_indent = 0
    for idx, raw_line in enumerate(lines):
        stripped_line = raw_line.strip()
        if stripped_line == "where":
            where_index = idx
            where_indent = len(raw_line) - len(raw_line.lstrip())
            break
        if "where" in _lean_ident_tokens(stripped_line):
            return "inline_where_skeleton_unsupported"
    if where_index < 0:
        return ""

    decl_candidates: list[tuple[int, int, str]] = []
    for idx, raw_line in enumerate(lines[where_index + 1 :], start=where_index + 1):
        if not raw_line.strip():
            continue
        indent = len(raw_line) - len(raw_line.lstrip())
        if indent <= where_indent:
            continue
        stripped_line = raw_line.strip()
        if stripped_line.startswith("«"):
            return "unsupported_where_declaration_in_skeleton"
        match = _LEAN_ASCII_IDENT_RE.match(stripped_line)
        if match is None:
            first = stripped_line[0]
            if first.isalpha() or first == "_":
                return "unsupported_where_declaration_in_skeleton"
            continue
        name = match.group(0)
        rest = stripped_line[match.end() :].lstrip()
        if rest.startswith(":") or rest.startswith("|") or rest.startswith(":="):
            decl_candidates.append((idx, indent, name))
    if not decl_candidates:
        return ""

    decl_indent = min(indent for _idx, indent, _name in decl_candidates)
    decls = [
        (idx, name)
        for idx, indent, name in decl_candidates
        if indent == decl_indent and name not in _PROOF_BODY_PREFIXES
    ]
    if not decls:
        return ""

    decl_names = [name for _idx, name in decls]
    name_set = set(decl_names)
    prefix_text = "\n".join(lines[:where_index])
    reachable = {
        name
        for name in decl_names
        if _has_plain_ident_reference(prefix_text, name)
    }
    bodies: dict[str, str] = {}
    for position, (start_idx, name) in enumerate(decls):
        end_idx = decls[position + 1][0] if position + 1 < len(decls) else len(lines)
        bodies[name] = "\n".join(lines[start_idx:end_idx])

    changed = True
    while changed:
        changed = False
        for name in list(reachable):
            for dep in name_set - reachable:
                if _has_plain_ident_reference(bodies.get(name, ""), dep):
                    reachable.add(dep)
                    changed = True

    unreachable = [name for name in decl_names if name not in reachable]
    if unreachable:
        return "unreachable_where_declaration_in_skeleton"
    return ""


def _top_level_command_in_proof_body_reason(proof_stub: str) -> str:
    """Reject extra Lean commands/declarations masquerading as a proof body."""

    stripped, lexically_closed = _strip_lean_comments_and_strings(str(proof_stub or ""))
    body = stripped if lexically_closed else str(proof_stub or "")
    where_reason = _where_decl_reachability_reason(body)
    if where_reason:
        return where_reason
    body_lines = body.splitlines()
    multiline_by_body = bool(body_lines and body_lines[0].strip() == "by")
    for line_index, raw_line in enumerate(body_lines):
        line = raw_line.lstrip()
        if not line:
            continue
        if ";" in line:
            return "semicolon_skeleton_unsupported"
        command_reason = _top_level_command_reason_from_tokens(
            _lean_ident_token_sequence(line)
        )
        if command_reason:
            return command_reason
        if "#" in line:
            return "top_level_command_in_skeleton"
        if line.startswith("builtin_"):
            return "top_level_command_in_skeleton"
        if line.startswith("@["):
            return "top_level_attribute_in_skeleton"
        tokens = _line_start_ident_tokens(line)
        if not tokens:
            continue
        head = tokens[0]
        if head in _PROOF_BODY_PREFIXES:
            embedded = _top_level_command_reason_from_tokens(tokens, start=1)
            if embedded:
                return embedded
            continue
        if head.startswith("builtin_"):
            return "top_level_command_in_skeleton"
        if head in _TOP_LEVEL_COMMAND_HEADS:
            return f"top_level_{head}_in_skeleton"
        if head in _TOP_LEVEL_COMMAND_MODIFIERS:
            reason = _top_level_command_reason_from_tokens(tokens)
            if reason:
                return reason
        if multiline_by_body and line_index > 0 and raw_line == line:
            return "unindented_by_skeleton_line"
    return ""


async def _lean_check_skeleton(
    *,
    lean: Any,
    parent: ProofStateNode,
    proof_stub: str,
    timeout_s: Optional[float],
    max_heartbeats: Optional[int],
    residual_preamble: str,
    residual_helpers: List[str],
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
    settlement_margin_s: float = 1.0,
) -> tuple[Any, str, Any, str]:
    """Return one atomic typed residual receipt for the accepted stub variant."""

    extractor = getattr(lean, "extract_typed_residual_batch", None)
    if not callable(extractor):
        return None, "typed_residual_api_unavailable", None, str(proof_stub or "")
    last_reason = "typed_residual_extraction_failed"
    last_result = None
    last_candidate_stub = str(proof_stub or "")
    unresolved_candidate: tuple[str, str, Any] | None = None
    for candidate_stub in _parent_stub_validation_variants(parent.target, proof_stub):
        if not str(candidate_stub or "").strip():
            continue
        last_candidate_stub = str(candidate_stub)
        # A parent stub may have more than one valid wrapper shape. Each
        # candidate is a separate Lean operation and therefore needs its own
        # complete admission quantum. Never start the next variant merely
        # because the first variant was funded when this loop began.
        callback_deadline_elapsed = bool(
            deadline_exhausted and deadline_exhausted()
        )
        absolute_deadline_underfunded = bool(
            float(deadline_monotonic or 0.0) > 0.0
            and _fully_funded_operation_timeout(
                float(timeout_s or 0.0) + max(0.0, settlement_margin_s),
                deadline_monotonic,
            )
            <= 0.0
        )
        if callback_deadline_elapsed or absolute_deadline_underfunded:
            if unresolved_candidate is not None:
                (
                    unresolved_reason,
                    unresolved_stub,
                    unresolved_result,
                ) = unresolved_candidate
                return (
                    None,
                    unresolved_reason,
                    unresolved_result,
                    unresolved_stub,
                )
            return (
                None,
                (
                    "typed_residual_extraction_deadline_elapsed"
                    if callback_deadline_elapsed
                    else "typed_residual_extraction_underfunded"
                ),
                None,
                last_candidate_stub,
            )
        try:
            async def run_extract() -> Any:
                return await extractor(
                    parent.target,
                    candidate_stub,
                    residual_helpers,
                    preamble_override=residual_preamble,
                    timeout_s=timeout_s,
                    max_heartbeats=max_heartbeats,
                    check_kind="proof_state_skeleton_route",
                )

            result = await _await_serialized_lean_operation(
                lean,
                run_extract,
                timeout_s=float(timeout_s or 0.0),
                deadline_monotonic=deadline_monotonic,
                operation_label="try_skeleton_typed_residual",
                release_unrecyclable_tail=True,
            )
        except asyncio.CancelledError:
            raise
        except _LeanAdmissionDeferred:
            raise
        except Exception as exc:
            if isinstance(exc, _LeanAdmissionDeferred):
                raise
            # Preserve the exact candidate that reached the verifier. The
            # caller durably schedules this paid frame for verifier-only
            # replay; a transport exception is not mathematical evidence.
            return (
                None,
                f"typed_residual_extraction_exception:{type(exc).__name__}",
                None,
                last_candidate_stub,
            )
        last_result = result
        callback_deadline_elapsed = bool(
            deadline_exhausted and deadline_exhausted()
        )
        receipt = getattr(result, "receipt", None)
        if (
            not callback_deadline_elapsed
            and bool(getattr(result, "ok", False))
            and receipt is not None
        ):
            return receipt, candidate_stub, result, last_candidate_stub
        raw_output = str(getattr(result, "output", "") or "")
        returncode = int(getattr(result, "returncode", 1) or 1)
        parsed = parse_lean_output(raw_output, returncode) if raw_output else None
        error_type = canonical_error_type(parsed) if parsed is not None else ""
        # The typed API's error taxonomy is authoritative. Generic Lean-output
        # parsing can collapse a verifier timeout, missing marker, or malformed
        # receipt into ``lean_error``; treating that label as mathematical
        # evidence would reintroduce the fail-open/fail-wrong boundary this
        # receipt path is meant to close.
        last_reason = str(
            getattr(result, "error", "") or error_type or last_reason
        )
        if (
            last_reason not in _CONCLUSIVE_TYPED_RESIDUAL_REJECTIONS
            and unresolved_candidate is None
        ):
            unresolved_candidate = (
                last_reason,
                last_candidate_stub,
                last_result,
            )
        if callback_deadline_elapsed:
            if unresolved_candidate is not None:
                unresolved_reason, unresolved_stub, unresolved_result = (
                    unresolved_candidate
                )
                return (
                    None,
                    unresolved_reason,
                    unresolved_result,
                    unresolved_stub,
                )
            return (
                None,
                "typed_residual_extraction_deadline_elapsed",
                last_result,
                last_candidate_stub,
            )
    if unresolved_candidate is not None:
        unresolved_reason, unresolved_stub, unresolved_result = (
            unresolved_candidate
        )
        return None, unresolved_reason, unresolved_result, unresolved_stub
    return None, last_reason, last_result, last_candidate_stub


def _diagnostic_summary(
    result: Any,
    *,
    redact_solution_refs: bool,
) -> str:
    raw = str(getattr(result, "output", "") or "")
    parsed = getattr(result, "parsed", None)
    if parsed is None and raw:
        parsed = parse_lean_output(
            raw,
            int(getattr(result, "returncode", 1) or 1),
        )
    diagnostics: List[str] = []
    if parsed is not None:
        raw_diagnostics = list(getattr(parsed, "diagnostics", []) or [])
        indexed_diagnostics = list(enumerate(raw_diagnostics))
        indexed_diagnostics.sort(
            key=lambda item: (
                0
                if str(getattr(item[1], "severity", "") or "").lower()
                == "error"
                else 1
                if str(getattr(item[1], "severity", "") or "").lower()
                == "warning"
                else 2,
                item[0],
            )
        )
        for _index, diag in indexed_diagnostics[:3]:
            msg = diagnostic_preview(str(getattr(diag, "message", "") or ""))
            if not msg:
                msg = str(getattr(diag, "summary", "") or "")
            if msg:
                diagnostics.append(
                    _compact(
                        msg,
                        260,
                        redact_solution_refs=redact_solution_refs,
                        lean_diagnostic=True,
                    )
                )
    if diagnostics:
        return " | ".join(diagnostics)
    return _compact(
        raw,
        700,
        redact_solution_refs=redact_solution_refs,
        lean_diagnostic=True,
    )


async def _run_try_skeleton_tool_impl(
    lean: Any,
    *,
    goal_statement: str,
    preamble: str,
    args: Dict[str, Any],
    conv: Any,
    dossier: Optional[ProofDossier],
    proof_state: Optional[ProofSearchState],
    turn_index: int = 0,
    tool_call_index: int = 0,
    max_residual_goals: int = 4,
    timeout_s: Optional[float] = None,
    max_heartbeats: Optional[int] = 1600000,
    redact_solution_refs: bool = True,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
) -> str:
    """Validate and bank a partial proof skeleton as route structure only."""

    del preamble  # the proof-state residual preamble is derived from conv.
    _dossier_metric(dossier, "mini_try_skeleton_calls", 1)
    code = _strip_fence(str(args.get("code", "") or ""))
    purpose = _compact(
        args.get("purpose", ""),
        160,
        redact_solution_refs=redact_solution_refs,
    )
    if not code:
        return _reject(
            dossier=dossier,
            reason="empty_code",
            message="try_skeleton error: empty `code`.",
            redact_solution_refs=redact_solution_refs,
        )
    if dossier is None or proof_state is None:
        return _reject(
            dossier=dossier,
            reason="missing_proof_state",
            message="try_skeleton error: proof-state route banking is unavailable.",
            redact_solution_refs=redact_solution_refs,
        )
    if _FORBIDDEN_SCRATCH_RE.search(code):
        return _reject(
            dossier=dossier,
            reason="forbidden_scratch_command",
            message=(
                "try_skeleton error: skeleton code may not contain imports, "
                "axioms, #commands, attributes, local commands, or option changes."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    if has_sorry_or_admit(code):
        return _reject(
            dossier=dossier,
            reason="sorry_or_admit_masks_obligations",
            message=(
                "try_skeleton error: do not use `sorry` or `admit` in a route "
                "skeleton. Leave holes as `?_` or stop after the reducing tactic "
                "so Lean reports the residual goals to bank."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    proof_stub, extraction_error = _extract_skeleton_body(code, goal_statement)
    if extraction_error:
        return _reject(
            dossier=dossier,
            reason=extraction_error,
            message=(
                "try_skeleton error: complete declarations are allowed only when "
                "their statement exactly matches the active goal."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    top_level_command_reason = _top_level_command_in_proof_body_reason(proof_stub)
    if top_level_command_reason:
        return _reject(
            dossier=dossier,
            reason=top_level_command_reason,
            message=(
                "try_skeleton error: provide exactly one proof body for the "
                "active goal. Extra top-level Lean declarations or commands "
                "would create residual goals unrelated to the parent route."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    if not proof_stub.lstrip().startswith(_PROOF_BODY_PREFIXES):
        return _reject(
            dossier=dossier,
            reason="not_proof_body",
            message=(
                "try_skeleton error: provide a partial proof body for the active "
                "goal, usually starting with `by`, `refine`, or `calc`."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    if _raw_prompt_unsafe_source(
        proof_stub,
        redact_solution_refs=redact_solution_refs,
    ):
        return _reject(
            dossier=dossier,
            reason="prompt_unsafe_skeleton_source",
            message=(
                "try_skeleton error: skeleton code contains prompt-control or "
                "official-answer text and cannot be banked as durable route "
                "structure."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    parent = _find_parent_node(proof_state, goal_statement)
    if parent is None or getattr(parent, "status", "") in {
        "proved",
        "obsolete",
        "rejected",
        "failed",
    }:
        return _reject(
            dossier=dossier,
            reason="missing_open_parent",
            message="try_skeleton error: no open parent goal is available.",
            redact_solution_refs=redact_solution_refs,
        )
    limit = max(0, int(max_residual_goals or 0))
    if limit <= 0:
        return _reject(
            dossier=dossier,
            reason="residual_goal_budget_disabled",
            message="try_skeleton error: residual-goal banking budget is disabled.",
            redact_solution_refs=redact_solution_refs,
        )
    timeout = None if timeout_s is None else float(timeout_s)
    if timeout is not None and timeout <= 0.0:
        return _reject(
            dossier=dossier,
            reason="timeout_disabled",
            message="try_skeleton error: Lean validation timeout is disabled.",
            redact_solution_refs=redact_solution_refs,
        )

    combined_deadline = _combined_deadline_predicate(
        deadline_exhausted,
        deadline_monotonic,
    )

    def deadline_elapsed() -> bool:
        return bool(combined_deadline and combined_deadline())

    def deadline_rejection() -> str:
        return _json_result(
            {
                "status": "rejected",
                "reason": "llm_turn_elapsed_budget_exhausted",
                "summary": _compact(
                    "try_skeleton cancelled: the turn deadline expired before "
                    "this route could be banked.",
                    900,
                    redact_solution_refs=redact_solution_refs,
                    lean_diagnostic=True,
                ),
            }
        )

    def neutral_extraction_rejection(
        *,
        reason: str,
        message: str,
        validation: Any = None,
        pending_retry_banked: bool = False,
        execution_disposition: str = "",
    ) -> str:
        """Defer an unavailable attestation without charging a failure."""

        _dossier_metric(
            dossier,
            "mini_try_skeleton_typed_residual_inconclusive",
            1,
        )
        diagnostic = (
            _diagnostic_summary(
                validation,
                redact_solution_refs=redact_solution_refs,
            )
            if validation is not None
            else ""
        )
        payload: Dict[str, Any] = {
            "status": "rejected",
            "reason": str(reason or "typed_residual_extraction_inconclusive"),
            "neutral": True,
            "retryable": True,
            "pending_residual_goal_extraction": bool(pending_retry_banked),
            "summary": _compact(
                message,
                900,
                redact_solution_refs=redact_solution_refs,
                lean_diagnostic=True,
            ),
        }
        if execution_disposition:
            payload["execution_disposition"] = str(execution_disposition)
        if diagnostic:
            payload["diagnostics"] = diagnostic
        return _json_result(payload)

    residual_source = (
        f"try_skeleton_tool:{int(turn_index or 0)}:"
        f"{int(tool_call_index or 0)}"
    )
    residual_preamble = _proof_state_residual_preamble(conv)
    residual_helpers = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    residual_operation_timeout = _typed_residual_operation_timeout(
        lean,
        float(timeout or 0.0),
    )

    def bank_pending_residual_retry(candidate_stub: str) -> bool:
        """Persist the exact paid stub for verifier-only replay."""

        exact_stub = str(candidate_stub or "").strip()
        recorder = getattr(
            proof_state,
            "record_pending_residual_goal_extraction",
            None,
        )
        if not exact_stub or not callable(recorder) or deadline_elapsed():
            return False
        existing_pending = dict(
            getattr(parent, "pending_residual_goal_extraction", {}) or {}
        )
        if existing_pending:
            # ProofSearchState deliberately owns one prioritized durable retry
            # slot per parent. Never overwrite another paid route merely
            # because a later tool call also encountered infrastructure loss.
            return bool(
                str(existing_pending.get("source") or "") == residual_source
                and str(existing_pending.get("parent_proof_stub") or "")
                == exact_stub
            )
        try:
            request_hash, context_hash = _typed_residual_request_hashes(
                lean=lean,
                proof_state=proof_state,
                parent_node=parent,
                parent_proof_stub=exact_stub,
                source=residual_source,
                preamble=residual_preamble,
                lemmas=residual_helpers,
                max_goals=limit,
            )
            recorded = bool(
                recorder(
                    parent_node_id=parent.node_id,
                    source=residual_source,
                    parent_proof_stub=exact_stub,
                    max_goals=limit,
                    request_context_hash=request_hash,
                    elaboration_context_hash=context_hash,
                    origin_metadata={
                        "kind": "try_skeleton_tool",
                        "turn_index": int(turn_index or 0),
                        "tool_call_index": int(tool_call_index or 0),
                        "purpose": purpose,
                    },
                    action_metadata={"action_id": "try_skeleton"},
                )
            )
        except Exception:
            return False
        if not recorded or deadline_elapsed():
            return False
        # Keep the graph-owned executable snapshot current. The enclosing
        # DeadlineMutationTransaction restores both state and graph if the
        # turn deadline wins during this projection.
        sync = getattr(proof_state, "sync_to_graph", None)
        if callable(sync):
            try:
                sync(
                    dossier,
                    phase="try_skeleton_residual_retry_pending",
                    turn_index=int(turn_index or 0),
                )
            except Exception:
                # The live proof-state record remains authoritative and will
                # be included by the next session checkpoint/sync.
                pass
        return not deadline_elapsed()

    # The tool loop's hard turn deadline can cancel this coroutine before the
    # Lean adapter returns a timeout result. Admit the receipt extraction only
    # when its complete, operator-controlled quantum plus a small settlement
    # tail fits. Otherwise preserve the exact paid stub without starting Lean.
    settlement_margin_s = 1.0
    if (
        float(deadline_monotonic or 0.0) > 0.0
        and _fully_funded_operation_timeout(
            residual_operation_timeout + settlement_margin_s,
            deadline_monotonic,
        )
        <= 0.0
    ):
        pending_retry_banked = bank_pending_residual_retry(proof_stub)
        return neutral_extraction_rejection(
            reason="typed_residual_extraction_inconclusive",
            message=(
                "try_skeleton deferred typed-residual verification before "
                "launch because the remaining hard-turn budget could not fund "
                "the complete verifier quantum; "
                + (
                    "the exact paid stub was banked for verifier-only replay."
                    if pending_retry_banked
                    else "the attempt remains retryable."
                )
            ),
            pending_retry_banked=pending_retry_banked,
            execution_disposition="infrastructure_deferred_before_launch",
        )

    try:
        (
            receipt,
            accepted_stub_or_reason,
            validation_result,
            attempted_stub,
        ) = await _lean_check_skeleton(
            lean=lean,
            parent=parent,
            proof_stub=proof_stub,
            timeout_s=residual_operation_timeout,
            max_heartbeats=max_heartbeats,
            residual_preamble=residual_preamble,
            residual_helpers=residual_helpers,
            deadline_exhausted=combined_deadline,
            deadline_monotonic=deadline_monotonic,
            settlement_margin_s=settlement_margin_s,
        )
    except asyncio.CancelledError:
        raise
    except _LeanAdmissionDeferred:
        pending_retry_banked = bank_pending_residual_retry(proof_stub)
        return neutral_extraction_rejection(
            reason="typed_residual_extraction_inconclusive",
            message=(
                "try_skeleton deferred typed-residual verification before "
                "launch because the shared Lean capability is occupied; "
                + (
                    "the exact paid stub was banked for verifier-only replay."
                    if pending_retry_banked
                    else "the attempt remains retryable."
                )
            ),
            pending_retry_banked=pending_retry_banked,
            execution_disposition="infrastructure_deferred_before_launch",
        )
    except Exception as exc:
        if deadline_elapsed():
            return _json_result(
                {
                    "status": "rejected",
                    "reason": "llm_turn_elapsed_budget_exhausted",
                    "summary": _compact(
                        "try_skeleton cancelled: the turn deadline expired "
                        "before this validation error could be recorded.",
                        900,
                        redact_solution_refs=redact_solution_refs,
                        lean_diagnostic=True,
                    ),
                }
            )
        pending_retry_banked = bank_pending_residual_retry(proof_stub)
        return neutral_extraction_rejection(
            reason="typed_residual_extraction_inconclusive",
            message=(
                "try_skeleton could not obtain an authoritative typed-residual "
                f"receipt ({type(exc).__name__}); verifier-only replay was "
                + (
                    "banked."
                    if pending_retry_banked
                    else "not available."
                )
            ),
            pending_retry_banked=pending_retry_banked,
            execution_disposition="infrastructure_after_launch",
        )
    if receipt is None:
        failure_reason = str(
            accepted_stub_or_reason or "typed_residual_extraction_failed"
        )
        # Only Lean's explicit rejection of the submitted route (or an
        # intrinsically invalid request) is conclusive. Every receipt,
        # transport, timeout, schema, or parser failure is infrastructure and
        # must leave the route retryable without graph mutation.
        inconclusive = (
            failure_reason not in _CONCLUSIVE_TYPED_RESIDUAL_REJECTIONS
        )
        if inconclusive:
            pending_retry_banked = bank_pending_residual_retry(attempted_stub)
            return neutral_extraction_rejection(
                reason="typed_residual_extraction_inconclusive",
                message=(
                    "try_skeleton could not certify this route's typed residual "
                    "batch conclusively; "
                    + (
                        "the exact paid stub was banked for verifier-only replay."
                        if pending_retry_banked
                        else "the attempt remains retryable."
                    )
                ),
                validation=validation_result,
                pending_retry_banked=pending_retry_banked,
                execution_disposition="infrastructure_after_launch",
            )
        diagnostic = (
            _diagnostic_summary(
                validation_result,
                redact_solution_refs=redact_solution_refs,
            )
            if validation_result is not None
            else ""
        )
        message = (
            "try_skeleton rejected: Lean did not validate this as a "
            "partial proof with bankable residual goals."
        )
        if diagnostic:
            message = f"{message} Lean diagnostic: {diagnostic}"
        return _reject(
            dossier=dossier,
            reason=failure_reason,
            message=message,
            redact_solution_refs=redact_solution_refs,
            extra=({"diagnostics": diagnostic} if diagnostic else None),
        )
    typed_goals = tuple(getattr(receipt, "goals", ()) or ())
    if not typed_goals:
        return _reject(
            dossier=dossier,
            reason="skeleton_closed_goal",
            message=(
                "try_skeleton rejected: the proof closed the goal. Submit it as "
                "the final proof or check it with try_lean instead; skeletons "
                "must leave residual obligations."
            ),
            redact_solution_refs=redact_solution_refs,
        )
    goals = [
        {
            # This source was emitted with fully explicit printer options,
            # reparsed as a closed theorem type, and checked definitionally
            # equal to the original residual Expr in the same Lean command.
            # It is therefore the executable child statement; human goal
            # diagnostics are never used as a persistence boundary.
            "target": str(getattr(goal, "statement", "") or "").strip(),
            "hypotheses": [],
            "rendered_target": True,
        }
        for goal in typed_goals
        if str(getattr(goal, "statement", "") or "").strip()
    ]
    if len(goals) != len(typed_goals):
        return _reject(
            dossier=dossier,
            reason="typed_residual_statement_missing",
            message=(
                "try_skeleton rejected: Lean's typed residual receipt did not "
                "contain one executable statement for every goal slot."
            ),
            redact_solution_refs=redact_solution_refs,
            extra={
                "diagnostics": _diagnostic_summary(
                    validation_result,
                    redact_solution_refs=redact_solution_refs,
                )
            },
        )
    if len(goals) > limit:
        return _reject(
            dossier=dossier,
            reason="residual_goal_cap_exceeded",
            message=(
                f"try_skeleton rejected: scaffold left {len(goals)} residual "
                f"goals, exceeding the configured limit {limit}."
            ),
            redact_solution_refs=redact_solution_refs,
            extra={"residual_goal_count": len(goals), "residual_goal_limit": limit},
        )
    if any(_closed_false_residual_goal(goal) for goal in goals):
        return _reject(
            dossier=dossier,
            reason="closed_false_residual_goal",
            message="try_skeleton rejected: scaffold attempted to bank a closed False goal.",
            redact_solution_refs=redact_solution_refs,
        )

    if deadline_elapsed():
        return deadline_rejection()

    checkpoint_id = ""
    checkpoint = getattr(proof_state, "checkpoint", None)
    commit = getattr(proof_state, "commit", None)
    rollback = getattr(proof_state, "rollback", None)
    if callable(checkpoint) and callable(commit) and callable(rollback):
        try:
            checkpoint_id = checkpoint(dossier=dossier, label="try_skeleton_route")
        except TypeError:
            try:
                checkpoint_id = checkpoint(label="try_skeleton_route")
            except Exception:
                checkpoint_id = ""
        except Exception:
            checkpoint_id = ""
    if deadline_elapsed():
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return deadline_rejection()
    existing_group_ids = {
        str(getattr(group, "assembly_id", "") or "")
        for group in list(getattr(parent, "assembly_attempt_groups", ()) or ())
        if str(getattr(group, "assembly_id", "") or "")
    }
    spawned = proof_state.spawn_typed_residual_batch(
        receipt,
        source=residual_source,
        parent_node_id=parent.node_id,
        parent_proof_stub=str(accepted_stub_or_reason or proof_stub),
        max_goals=len(goals),
    )
    admission_status = str(getattr(spawned, "status", "") or "")
    admission_reason = str(getattr(spawned, "reason", "") or "")
    parent_after = proof_state.nodes.get(parent.node_id)
    new_groups = [
        group
        for group in list(getattr(parent_after, "assembly_attempt_groups", ()) or ())
        if str(getattr(group, "assembly_id", "") or "") not in existing_group_ids
    ]
    group_child_slots = (
        list(getattr(new_groups[-1], "child_node_ids", ()) or ())
        if new_groups
        else []
    )
    group_child_slot_count = len(group_child_slots)
    missing_child_slots = [
        child_id
        for child_id in group_child_slots
        if str(child_id or "") not in proof_state.nodes
    ]
    if admission_status == "terminal_rejected":
        # Spawn already settled pending and rolled back its inner snapshot.
        # Inspect this before the post-admission deadline check: rolling the
        # outer checkpoint would restore a retry Lean already rejected.
        if checkpoint_id and callable(commit):
            try:
                commit(checkpoint_id)
            except Exception:
                pass
        transaction = active_deadline_transaction()
        if transaction is not None:
            transaction.keep_current_state()
        clearer = getattr(
            proof_state, "clear_pending_residual_goal_extraction", None
        )
        if callable(clearer):
            clearer(str(parent.node_id or ""))
        mapped_reason = {
            "attested_residual_goal_cap_exceeded": "residual_goal_cap_exceeded",
        }.get(admission_reason, "residual_spawn_incomplete")
        return _reject(
            dossier=dossier,
            reason=mapped_reason,
            message=(
                "try_skeleton rejected: validated residual goals could not be "
                "attached completely to the proof-state graph."
            ),
            redact_solution_refs=redact_solution_refs,
            extra={
                "spawned_node_ids": list(spawned),
                "assembly_child_node_ids": list(group_child_slots),
                "residual_goal_count": len(goals),
                "admission_reason": admission_reason,
            },
        )
    if deadline_elapsed():
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return deadline_rejection()
    if (
        not new_groups
        or group_child_slot_count != len(goals)
        or missing_child_slots
    ):
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        if admission_status == "deferred":
            pending_retry_banked = bank_pending_residual_retry(
                str(accepted_stub_or_reason or proof_stub)
            )
            return neutral_extraction_rejection(
                reason="typed_residual_extraction_inconclusive",
                message=(
                    "try_skeleton could not attach this route's typed residual "
                    "batch; verifier-only replay was "
                    + (
                        "banked."
                        if pending_retry_banked
                        else "not available."
                    )
                ),
                validation=validation_result,
                pending_retry_banked=pending_retry_banked,
                execution_disposition="infrastructure_after_launch",
            )
        return _reject(
            dossier=dossier,
            reason="residual_spawn_incomplete",
            message=(
                "try_skeleton rejected: validated residual goals could not be "
                "attached completely to the proof-state graph."
            ),
            redact_solution_refs=redact_solution_refs,
            extra={
                "spawned_node_ids": list(spawned),
                "assembly_child_node_ids": list(group_child_slots),
                "residual_goal_count": len(goals),
            },
        )
    if deadline_elapsed():
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return deadline_rejection()
    try:
        sync = getattr(proof_state, "sync_to_graph", None)
        if callable(sync):
            sync(dossier, phase="try_skeleton", turn_index=int(turn_index or 0))
    except Exception:
        pass
    if deadline_elapsed():
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return deadline_rejection()
    try:
        proof_state.record_transition(
            node_id=parent.node_id,
            source="try_skeleton_tool",
            error_type="llm_skeleton_route_spawned",
            action=getattr(parent, "action", ""),
            blocker=(
                "Lean-validated proof skeleton banked as assembly route with "
                f"{len(goals)} residual obligation(s)"
            ),
            phase="try_skeleton",
            turn_index=int(turn_index or 0),
            payload={
                "spawned_node_ids": list(spawned),
                "assembly_child_node_ids": list(group_child_slots),
                "assembly_group_ids": [
                    str(getattr(group, "assembly_id", "") or "")
                    for group in new_groups
                    if str(getattr(group, "assembly_id", "") or "")
                    ],
                    "residual_goal_count": len(goals),
                    "proof_stub": str(accepted_stub_or_reason or proof_stub)[:400],
                    "purpose": purpose,
                },
            )
    except Exception:
        pass
    if deadline_elapsed():
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return deadline_rejection()
    if checkpoint_id and callable(commit):
        try:
            commit(checkpoint_id)
        except Exception:
            pass
    _dossier_metric(dossier, "mini_try_skeleton_accepted", 1)
    _dossier_metric(dossier, "mini_try_skeleton_residual_goals", len(goals))
    obligations: List[Dict[str, Any]] = []
    for node_id in spawned:
        node = proof_state.nodes.get(node_id)
        if node is None:
            continue
        obligations.append(
            {
                "node_id": node.node_id,
                "target": _compact(
                    getattr(node, "target", ""),
                    700,
                    redact_solution_refs=redact_solution_refs,
                    lean_diagnostic=True,
                ),
                "hypotheses": [
                    _compact(
                        item,
                        500,
                        redact_solution_refs=redact_solution_refs,
                        lean_diagnostic=True,
                    )
                    for item in list(getattr(node, "local_context", ()) or ())
                ],
            }
        )
    assembly_group_ids = [
        str(getattr(group, "assembly_id", "") or "")
        for group in new_groups
        if str(getattr(group, "assembly_id", "") or "")
    ]
    return _json_result(
        {
            "status": "accepted",
            "summary": (
                "try_skeleton accepted: Lean validated this as a route "
                f"constructor and banked {len(obligations)} open obligation(s). "
                "This is structure only, not proof evidence."
            ),
            "purpose": purpose,
            "proof_state_update": {
                "status": "spawned_remaining_goals",
                "source": "try_skeleton",
                "parent_node_id": parent.node_id,
                "node_ids": list(spawned),
                "assembly_child_node_ids": list(group_child_slots),
                "assembly_group_ids": assembly_group_ids,
                "residual_goal_count": len(goals),
                "evidence": False,
            },
            "obligations": obligations,
            "proof_stub_preview": _compact(
                accepted_stub_or_reason or proof_stub,
                500,
                redact_solution_refs=redact_solution_refs,
                lean_diagnostic=True,
            ),
        }
    )


async def run_try_skeleton_tool(*args: Any, **kwargs: Any) -> str:
    """Bank a route only when the entire dossier/proof-state commit is live."""

    combined_deadline = _combined_deadline_predicate(
        kwargs.get("deadline_exhausted"),
        kwargs.get("deadline_monotonic", 0.0),
    )
    transaction = DeadlineMutationTransaction(
        deadline_exhausted=combined_deadline,
        dossier=kwargs.get("dossier"),
        proof_state=kwargs.get("proof_state"),
        label="try_skeleton_tool",
    )
    with transaction:
        if not transaction.can_mutate():
            return _json_result(
                {
                    "status": "rejected",
                    "reason": "llm_turn_elapsed_budget_exhausted",
                    "summary": "try_skeleton cancelled before this route could start.",
                }
            )
        result = await _run_try_skeleton_tool_impl(*args, **kwargs)
        if not transaction.can_mutate() and not transaction.committed:
            return _json_result(
                {
                    "status": "rejected",
                    "reason": "llm_turn_elapsed_budget_exhausted",
                    "summary": "try_skeleton cancelled before this route could be committed.",
                }
            )
    if transaction.enabled and not transaction.committed:
        reason = (
            "llm_turn_elapsed_budget_exhausted"
            if transaction.deadline_won
            else "deadline_mutation_commit_failed"
        )
        return _json_result(
            {
                "status": "rejected",
                "reason": reason,
                "summary": "try_skeleton cancelled before this route could be committed.",
            }
        )
    return result
