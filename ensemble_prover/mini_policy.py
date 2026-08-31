"""Policy gates and repair-state helpers for mini-prover runs."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .lean_syntax import normalize_nat_factorial_notation
from .mini_lean_extract import (
    _extract_example_body,
    _extract_helpers_and_main,
    _extract_single_decl_body,
    _helper_is_sorry_stub,
    _helper_statement_root_equivalent,
    _is_plausible_main_proof,
    _lean_body_is_sorry_stub,
    _non_code_response_text,
    _root_equivalent_sorry_stub_helper_names_from_blocks,
    _sorry_stub_helper_names,
    _split_top_level_chunks,
    _strip_lean_comments,
    _strip_lean_comments_and_strings,
    _strip_redundant_preamble_commands,
)
from .proof_dossier import (
    prompt_safe_malformed_tool_arguments,
    _prompt_safe_helper_name,
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
    _prompt_safe_code_snippet,
    _redact_solution_refs_for_prompt,
    _redact_split_solution_refs_for_prompt,
    effective_solution_placeholder_suppression,
    helper_decl_body,
    helper_decl_name,
    official_answer_visible_to_llm,
    text_hash,
)
from .utils import extract_code_fences, parse_tool_arguments


_REPAIR_SEMANTICS_KEY = "_repair_semantics"
_REPAIR_FEEDBACK = "repair_feedback"
_REPAIR_CONTINUATION = "repair_continuation"
_REPAIR_BOUNDARY = "repair_boundary"
_REPAIR_SEMANTICS_VALUES = frozenset(
    {_REPAIR_FEEDBACK, _REPAIR_CONTINUATION, _REPAIR_BOUNDARY}
)
_GRAPH_SELECTED_WORK_SCOPE_KEY = "_graph_selected_work_scope_key"
_REPAIR_SELF_CHECK_COMPLIANT_NON_VERDICT_STATUSES = frozenset(
    {
        "try_lean_infrastructure_error",
    }
)


def _repair_self_check_non_verdict_is_compliant(status: Any) -> bool:
    """Whether try_lean was invoked but its harness returned no verdict.

    This satisfies the behavioral self-check requirement without granting any
    proof authority; the final candidate must still pass the independent Lean
    verifier.
    """

    return (
        str(status or "").strip()
        in _REPAIR_SELF_CHECK_COMPLIANT_NON_VERDICT_STATUSES
    )


def _merge_repair_self_check_non_verdict_status(
    current: Any,
    incoming: Any,
) -> str:
    """Merge non-verdict statuses without erasing a compliant invocation."""

    current_status = str(current or "").strip()
    incoming_status = str(incoming or "").strip()
    if not incoming_status:
        return current_status
    if _repair_self_check_non_verdict_is_compliant(incoming_status):
        return incoming_status
    if _repair_self_check_non_verdict_is_compliant(current_status):
        return current_status
    return incoming_status


_GENERATED_SOLUTION_REF_ALIAS_RE = re.compile(
    r"\bsolution_ref_hidden_[A-Za-z0-9_]+\b"
)
_OFFICIAL_ANSWER_REFERENCE_HIDDEN = "[official-answer reference hidden]"
_REPAIR_REJECTED_FRAGMENTS_KEY = "_repair_rejected_fragments"
_REPAIR_TRANSIENT_GOAL_TARGETS_KEY = "_repair_transient_goal_targets"
_REPAIR_PAYLOAD_CARRIED_KEY = "_repair_payload_carried"
_REPAIR_PAYLOAD_RESET_BEFORE_KEY = "_repair_payload_reset_before"
_REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY = (
    "_repair_dropped_assistant_before_feedback"
)
_REJECTED_FRAGMENT_DISPLAY_LIMIT = 600
_PROVIDER_CHAT_MESSAGE_KEYS = frozenset(
    {
        "role",
        "content",
        "tool_calls",
        "tool_call_id",
        "name",
        # Provider-authored continuation state. Reasoning providers require
        # these fields to be replayed alongside the following tool receipts;
        # they remain transport-only and are filtered by the provider adapter.
        "reasoning_content",
        "_responses_reasoning_items",
        "_responses_output_items",
        "_provider_continuation_policy_receipt",
        # Internal transport contracts survive conversation answer-safety
        # normalization and are removed only by models._sanitize_request_messages.
        # Dropping them here would silently disable atomic selected context.
        "pinned",
        "pin",
        "preserve_context",
        "_required_prompt_context",
        "_selected_proof_idea_packet",
    }
)
_PROVIDER_CONTINUATION_STATE_KEYS = (
    "reasoning_content",
    "_responses_reasoning_items",
    "_responses_output_items",
)
_PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY = (
    "_provider_continuation_policy_receipt"
)


def _provider_continuation_capture_policy(conv: Any) -> Dict[str, Any]:
    payload_present = getattr(conv, "official_answer_payload_present", None)
    return {
        "suppress_solution_placeholders": bool(
            getattr(conv, "suppress_solution_placeholders", True)
        ),
        "opaque_mode": bool(getattr(conv, "opaque_mode", True)),
        "allow_official_answer_visibility": bool(
            getattr(conv, "allow_official_answer_visibility", False)
        ),
        "official_answer_payload_present": (
            None if payload_present is None else bool(payload_present)
        ),
        "redact_solution_refs": bool(
            _conversation_should_redact_solution_refs(conv)
        ),
    }


def _provider_continuation_state_digest(
    msg: Dict[str, Any],
    policy: Dict[str, Any],
) -> str:
    state = {
        key: msg[key]
        for key in _PROVIDER_CONTINUATION_STATE_KEYS
        if key in msg
    }
    encoded = json.dumps(
        {"policy": policy, "state": state},
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _bind_provider_continuation_policy_receipt(
    msg: Dict[str, Any],
    conv: Any,
) -> None:
    """Bind opaque provider state to the policy under which it was captured."""

    if not any(key in msg for key in _PROVIDER_CONTINUATION_STATE_KEYS):
        msg.pop(_PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY, None)
        return
    policy = _provider_continuation_capture_policy(conv)
    msg[_PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY] = {
        "schema_version": 1,
        "policy": policy,
        "state_digest": _provider_continuation_state_digest(msg, policy),
    }


def _responses_output_matches_advertised_tool_calls(
    output_items: Sequence[Dict[str, Any]],
    advertised_tool_calls: Sequence[Dict[str, Any]],
) -> bool:
    """Return whether exact Responses replay preserves the visible B1 pairs."""

    output_calls = [
        (
            str(item.get("call_id") or item.get("id") or ""),
            str(item.get("name") or ""),
            str(item.get("arguments") or ""),
        )
        for item in output_items
        if isinstance(item, dict)
        and str(item.get("type") or "") == "function_call"
    ]
    advertised_calls = [
        (
            str(item.get("id") or ""),
            str((item.get("function") or {}).get("name") or ""),
            str((item.get("function") or {}).get("arguments") or ""),
        )
        for item in advertised_tool_calls
        if isinstance(item, dict)
    ]
    return bool(output_calls) and output_calls == advertised_calls


def _provider_continuation_state_is_answer_safe(msg: Dict[str, Any]) -> bool:
    """Fail closed when opaque state contains a now-hidden answer reference."""

    state = {
        key: msg[key]
        for key in _PROVIDER_CONTINUATION_STATE_KEYS
        if key in msg
    }
    if not state:
        return True
    receipt = msg.get(_PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY)
    if not isinstance(receipt, dict) or receipt.get("schema_version") != 1:
        return False
    policy = receipt.get("policy")
    if not isinstance(policy, dict) or policy.get("redact_solution_refs") is not True:
        return False
    try:
        if str(receipt.get("state_digest") or "") != (
            _provider_continuation_state_digest(msg, policy)
        ):
            return False
        serialized = json.dumps(
            state,
            ensure_ascii=False,
            sort_keys=True,
            allow_nan=False,
        )
    except (TypeError, ValueError):
        return False
    redacted = _redact_split_solution_refs_for_prompt(serialized)
    redacted = _redact_solution_refs_for_prompt(redacted)
    redacted = _GENERATED_SOLUTION_REF_ALIAS_RE.sub(
        _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
        redacted,
    )
    return redacted == serialized


def _normalise_repair_semantics(value: Any) -> str:
    semantics = str(value or "").strip()
    return semantics if semantics in _REPAIR_SEMANTICS_VALUES else ""


def _infer_repair_semantics_for_user_content(content: Any) -> str:
    text = str(content or "")
    if _is_repair_feedback_content(text):
        return _REPAIR_FEEDBACK
    if _is_controller_repair_continuation_content(text):
        return _REPAIR_CONTINUATION
    return _REPAIR_BOUNDARY


def _user_history_message(
    content: str,
    *,
    repair_semantics: Optional[str] = None,
    repair_payload: Optional[Dict[str, Sequence[str]]] = None,
    payload_reset_candidate: bool = False,
) -> Dict[str, Any]:
    semantics = _normalise_repair_semantics(repair_semantics)
    if not semantics:
        semantics = _infer_repair_semantics_for_user_content(content)
    msg: Dict[str, Any] = {
        "role": "user",
        "content": content,
        _REPAIR_SEMANTICS_KEY: semantics,
    }
    own_fragments = _rejected_fragments_from_feedback_text(content)
    own_targets = _transient_goal_targets_from_feedback_text(content)
    payload_fragments = list((repair_payload or {}).get("fragments", []) or [])
    payload_targets = list(
        (repair_payload or {}).get("transient_goal_targets", []) or []
    )
    fragments = _dedupe_repair_payload_items([*own_fragments, *payload_fragments])
    targets = _dedupe_repair_payload_items([*own_targets, *payload_targets])
    if fragments:
        msg[_REPAIR_REJECTED_FRAGMENTS_KEY] = fragments
    if targets:
        msg[_REPAIR_TRANSIENT_GOAL_TARGETS_KEY] = targets
    if (fragments or targets) and not (own_fragments or own_targets):
        msg[_REPAIR_PAYLOAD_CARRIED_KEY] = True
    if payload_reset_candidate and (own_fragments or own_targets):
        msg[_REPAIR_PAYLOAD_RESET_BEFORE_KEY] = True
    return msg


def _conversation_official_answer_visible(
    conv: Any,
    fallback: Any = None,
) -> bool:
    """Whether this conversation may expose filled official-answer symbols."""

    payload_present = getattr(conv, "official_answer_payload_present", None)
    if payload_present is None:
        payload_present = getattr(
            fallback,
            "official_answer_payload_present",
            None,
        )
    return official_answer_visible_to_llm(
        opaque_mode=bool(
            getattr(
                conv,
                "opaque_mode",
                getattr(fallback, "opaque_mode", True),
            )
        ),
        allow_official_answer_visibility=bool(
            getattr(
                conv,
                "allow_official_answer_visibility",
                getattr(fallback, "allow_official_answer_visibility", False),
            )
        ),
        official_answer_payload_present=payload_present,
    )


def _conversation_should_redact_solution_refs(conv: Any) -> bool:
    """Whether model-facing history should hide PutnamBench answer names."""

    return effective_solution_placeholder_suppression(
        suppress_solution_placeholders=getattr(
            conv,
            "suppress_solution_placeholders",
            True,
        ),
        opaque_mode=bool(getattr(conv, "opaque_mode", True)),
        allow_official_answer_visibility=bool(
            getattr(conv, "allow_official_answer_visibility", False)
        ),
        official_answer_payload_present=getattr(
            conv,
            "official_answer_payload_present",
            None,
        ),
    )


def _provider_safe_chat_message(
    msg: Dict[str, Any],
    *,
    redact_solution_refs: bool = True,
) -> Dict[str, Any]:
    safe = {
        key: value
        for key, value in dict(msg or {}).items()
        if key in _PROVIDER_CHAT_MESSAGE_KEYS
    }
    if redact_solution_refs and "content" in safe:
        # History is durable and can outlive the policy/configuration under
        # which it was authored.  Re-apply the current capability at the last
        # provider boundary so a legacy visible-answer transcript cannot leak
        # an official symbol after opaque restore.  Preserve ordinary content
        # byte-for-byte apart from the narrow answer-reference redaction.
        content = str(safe.get("content") or "")
        content = _redact_split_solution_refs_for_prompt(content)
        content = _redact_solution_refs_for_prompt(content)
        safe["content"] = _GENERATED_SOLUTION_REF_ALIAS_RE.sub(
            _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
            content,
        )
    if redact_solution_refs and not _provider_continuation_state_is_answer_safe(safe):
        # Opaque Responses/DeepSeek continuation state must be replayed exactly;
        # rewriting nested values would invalidate that protocol state. Drop the
        # whole continuation bundle and fall back to the answer-safe visible
        # assistant/tool transcript instead.
        for key in _PROVIDER_CONTINUATION_STATE_KEYS:
            safe.pop(key, None)
        safe.pop(_PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY, None)
    if "tool_call_id" in safe:
        safe["tool_call_id"] = _prompt_safe_tool_call_token(
            safe.get("tool_call_id", ""),
            redact_solution_refs=redact_solution_refs,
        )
    if "name" in safe:
        safe["name"] = _prompt_safe_tool_name_token(
            safe.get("name", ""),
            redact_solution_refs=redact_solution_refs,
        )
    tool_calls = safe.get("tool_calls")
    if isinstance(tool_calls, list):
        sanitized_calls: List[Dict[str, Any]] = []
        for tool_call in tool_calls:
            call_item = dict(tool_call or {})
            if "id" in call_item:
                call_item["id"] = _prompt_safe_tool_call_token(
                    call_item.get("id", ""),
                    redact_solution_refs=redact_solution_refs,
                )
            function = call_item.get("function")
            if isinstance(function, dict):
                function_item = dict(function)
                if "name" in function_item:
                    function_item["name"] = _prompt_safe_tool_name_token(
                        function_item.get("name", ""),
                        redact_solution_refs=redact_solution_refs,
                    )
                if "arguments" in function_item:
                    arguments = _prompt_safe_tool_arguments(
                        function_item.get("arguments", "{}"),
                        redact_solution_refs=redact_solution_refs,
                    )
                    if redact_solution_refs:
                        arguments = _GENERATED_SOLUTION_REF_ALIAS_RE.sub(
                            _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
                            arguments,
                        )
                    function_item["arguments"] = arguments
                call_item["function"] = function_item
            sanitized_calls.append(call_item)
        safe["tool_calls"] = sanitized_calls
    return safe


def _prompt_safe_tool_call_token(
    value: Any,
    *,
    redact_solution_refs: bool = True,
) -> str:
    """Return protocol-safe, prompt-safe text for replayed tool-call ids/names.

    Tool-call ids are part of the provider protocol, not just prompt text:
    every advertised assistant id must match exactly one subsequent tool
    message. A lossy prompt sanitizer can collapse long or fully-redacted
    values, so any changed/truncated value receives a stable hash suffix.
    Already-safe short tokens remain unchanged, which keeps tool names such
    as ``check_lean`` intact.
    """

    raw = str(value or "").strip()
    safe = _prompt_safe_inline_text(
        raw,
        limit=160,
        redact_solution_refs=redact_solution_refs,
    )
    safe = re.sub(r"[^A-Za-z0-9_.:-]+", "_", safe).strip("_.:-")
    if raw and safe == raw and len(raw) <= 120:
        return raw
    digest = hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:16]
    stem = safe[:96].strip("_.:-") or "tool_call"
    return f"{stem}_{digest}"


def _prompt_safe_tool_name_token(
    value: Any,
    *,
    redact_solution_refs: bool = True,
) -> str:
    """Return a provider-safe function/tool name token.

    OpenAI-style tool names are stricter than tool-call ids. Keep known
    names unchanged, but normalize unknown names to ``[A-Za-z0-9_-]`` and
    cap them with a stable suffix when redaction or truncation changed them.
    """

    raw = str(value or "").strip()
    safe = _prompt_safe_inline_text(
        raw,
        limit=96,
        redact_solution_refs=redact_solution_refs,
    )
    safe = re.sub(r"[^A-Za-z0-9_-]+", "_", safe).strip("_-")
    if raw and safe == raw and len(raw) <= 64:
        return raw
    digest = hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:12]
    stem = safe[:51].strip("_-") or "tool"
    return f"{stem}_{digest}"


def _prompt_safe_tool_arguments(
    arguments: Any,
    *,
    redact_solution_refs: bool = True,
) -> str:
    """Return prompt- and provider-safe JSON tool-call arguments."""

    raw = "" if arguments is None else str(arguments)

    def sanitize(value: Any, *, key: str = "") -> Any:
        if isinstance(value, str):
            if key in {"code", "proof", "term", "statement"}:
                # Lean is layout-sensitive.  Flattening a retained tool call
                # made the refiner's most recent checked code impossible to
                # reuse or patch.  Preserve bounded line structure while the
                # diagnostic sanitizer still redacts prompt-control text,
                # solution references, comments, and string payloads.
                source = value
                if key in {"code", "proof"}:
                    fenced = extract_code_fences(source)
                    if fenced:
                        source = str(fenced[0] or "")
                return _prompt_safe_lean_diagnostic_text(
                    source,
                    limit=2400,
                    redact_solution_refs=redact_solution_refs,
                    preserve_line_breaks=True,
                )
            return _prompt_safe_inline_text(
                value,
                limit=1200,
                redact_solution_refs=redact_solution_refs,
            )
        if isinstance(value, list):
            return [sanitize(item, key=key) for item in value[:20]]
        if isinstance(value, dict):
            sanitized: Dict[str, Any] = {}
            for raw_key, item in list(value.items())[:40]:
                safe_key = _prompt_safe_inline_text(
                    str(raw_key),
                    limit=120,
                    redact_solution_refs=redact_solution_refs,
                )
                sanitized[safe_key] = sanitize(item, key=str(raw_key))
            return sanitized
        return value

    payload, parse_error = parse_tool_arguments(arguments)
    if parse_error:
        # Redact JSON string VALUES, not the whole literal set: keeping the
        # schema-derived keys is what makes a malformed call diagnosable at
        # all (a truncated payload looks nothing like a wrong-shaped one).
        safe_raw = prompt_safe_malformed_tool_arguments(raw, limit=1600)
        return json.dumps(
            {"__malformed_arguments__": safe_raw},
            ensure_ascii=False,
        )
    try:
        return json.dumps(
            sanitize(payload),
            ensure_ascii=False,
            allow_nan=False,
        )
    except Exception:
        # Redact JSON string VALUES, not the whole literal set: keeping the
        # schema-derived keys is what makes a malformed call diagnosable at
        # all (a truncated payload looks nothing like a wrong-shaped one).
        safe_raw = prompt_safe_malformed_tool_arguments(raw, limit=1600)
        return json.dumps(
            {"__malformed_arguments__": safe_raw},
            ensure_ascii=False,
        )


def _message_repair_semantics(msg: Dict[str, Any]) -> str:
    return _normalise_repair_semantics(
        dict(msg or {}).get(_REPAIR_SEMANTICS_KEY)
    )


def _dedupe_repair_payload_items(values: Sequence[Any]) -> List[str]:
    items: List[str] = []
    for value in values or ():
        text = " ".join(str(value or "").split())
        if text and text not in items:
            items.append(text)
    return items


def _repair_payload_values_from_message(
    msg: Dict[str, Any],
    key: str,
    fallback: Sequence[str],
) -> List[str]:
    return _dedupe_repair_payload_items([
        *(
            dict(msg or {}).get(key)
            if isinstance(dict(msg or {}).get(key), list)
            else []
        ),
        *fallback,
    ])


def _repair_payload_from_current_cycle(conv: Any) -> Dict[str, List[str]]:
    return {
        "fragments": _rejected_fragments_from_latest_feedback(conv),
        "transient_goal_targets": _transient_goal_targets_from_latest_feedback(conv),
    }


def _is_history_compaction_summary(msg: Dict[str, Any]) -> bool:
    return (
        msg.get("role") == "user"
        and str(msg.get("content", "") or "").startswith("[history compaction]")
    )


def _is_repair_feedback_content(content: Any) -> bool:
    text = str(content or "")
    return (
        "Lean rejected" in text
        or _REPAIR_SELF_CHECK_MARKER in text
        or "Primary error family:" in text
        or text.startswith("Repeated Lean failure:")
    )


def _is_explicit_repair_boundary_content(content: Any) -> bool:
    text = str(content or "").lstrip()
    return (
        text.startswith("Refiner phase begins.")
        or text.startswith("[hard pivot]")
        or text.startswith("[history compaction]")
        or text.startswith("Problem (natural language):")
    )


def _is_controller_repair_continuation_content(content: Any) -> bool:
    text = str(content or "")
    return (
        (
            text.startswith("Tool budget exhausted ")
            and "Use what you have and write the proof now." in text
        )
        or text.startswith("Graph-selected proof task:")
        or text.startswith("Pre-retrieved Mathlib lemmas ranked by ")
    )


def _is_stale_selected_work_context_message(msg: Dict[str, Any]) -> bool:
    """Return true for stored scheduler-scope prompts that must be refreshed."""

    if msg.get("role") != "user":
        return False
    content = str(msg.get("content", "") or "")
    return content.startswith("Graph-selected proof task:")


def _is_repair_cycle_neutral_user_message(msg: Dict[str, Any]) -> bool:
    """Model-visible control prompts that should not reset repair state."""

    if msg.get("role") != "user":
        return False
    semantics = _message_repair_semantics(msg)
    if semantics:
        return semantics == _REPAIR_CONTINUATION
    content = str(msg.get("content", "") or "")
    return _is_controller_repair_continuation_content(content)


def _is_stale_repair_feedback_message(msg: Dict[str, Any]) -> bool:
    if msg.get("role") != "user":
        return False
    semantics = _message_repair_semantics(msg)
    if semantics:
        return semantics == _REPAIR_FEEDBACK
    content = str(msg.get("content", "") or "")
    return (
        _is_repair_feedback_content(content)
        or "Primary error family:" in content
        or content.startswith("Repeated Lean failure:")
    )


def _is_stable_handoff_message(msg: Dict[str, Any]) -> bool:
    if msg.get("role") != "user":
        return False
    content = str(msg.get("content", "") or "")
    return (
        content.startswith("Refiner phase begins.")
        or content.startswith("[prover handoff evidence]")
        or content.startswith(
            "[history compaction]\nRefiner handoff omitted prior prover tool exploration"
        )
    )


def _drop_stale_feedback_before_first_kept_attempt(
    messages: Sequence[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    first_attempt = next(
        (
            i
            for i, msg in enumerate(messages)
            if msg.get("role") == "assistant"
            and not msg.get("tool_calls")
            and str(msg.get("content", "") or "").strip()
        ),
        len(messages),
    )
    return [
        msg
        for i, msg in enumerate(messages)
        if not (
            i < first_attempt
            and (
                _is_stale_repair_feedback_message(msg)
                or _is_stale_selected_work_context_message(msg)
            )
        )
    ]


def _summarize_compacted_attempts(
    history: Sequence[Dict[str, Any]],
    attempt_indices: Sequence[int],
) -> List[str]:
    summaries: List[str] = []
    for idx in attempt_indices:
        next_attempt = next(
            (
                j
                for j in range(idx + 1, len(history))
                if history[j].get("role") == "assistant"
                and not history[j].get("tool_calls")
                and str(history[j].get("content", "") or "").strip()
            ),
            len(history),
        )
        feedback = " ".join(
            str(history[j].get("content", "") or "")
            for j in range(idx + 1, next_attempt)
            if history[j].get("role") == "user"
        )
        family_match = re.search(r"Primary error family:\s*`([^`]+)`", feedback)
        target_match = re.search(
            r"(?:Repair target:.*?|goal\s+\d+\s+target:)\s*`([^`]+)`",
            feedback,
            flags=re.DOTALL,
        )
        family = family_match.group(1) if family_match else "rejected"
        target = _compact_history_summary_text(
            target_match.group(1) if target_match else "",
            limit=180,
        )
        detail = f"- prior attempt failed with `{family}`"
        if target:
            detail += f" on `{target}`"
        summaries.append(detail + ".")
    return summaries


def _summarize_compacted_tool_evidence(
    removed: Sequence[Dict[str, Any]],
    *,
    max_items: int = 4,
) -> List[str]:
    ranked: List[Tuple[int, int, str, str]] = []
    pending_calls: Dict[str, Tuple[str, Dict[str, Any]]] = {}
    order = 0
    for msg in removed:
        if msg.get("role") == "assistant" and msg.get("tool_calls"):
            pending_calls = {}
            for tc in list(msg.get("tool_calls") or []):
                tcid = str(tc.get("id", "") or "")
                function = tc.get("function") or {}
                if not isinstance(function, dict):
                    function = {}
                name = str(function.get("name", "") or "")
                args, parse_error = parse_tool_arguments(
                    function.get("arguments", None)
                )
                if parse_error:
                    args = {}
                if tcid and name:
                    pending_calls[tcid] = (name, dict(args or {}))
        elif msg.get("role") == "tool":
            tcid = str(msg.get("tool_call_id", "") or "")
            name, args = pending_calls.pop(tcid, ("tool", {}))
            content = str(msg.get("content", "") or "")
            content_compact = content.strip()
            score = 0
            evidence_class = ""
            structured_detail = ""
            if name == "try_lean":
                if content_compact.startswith("try_lean accepted."):
                    score = 40
                    evidence_class = "accepted_proof"
                    raw_code = str(args.get("code", "") or "")
                    fenced_blocks = extract_code_fences(raw_code)
                    checked_code = (
                        str(fenced_blocks[0] or "").strip()
                        if fenced_blocks
                        else raw_code.strip()
                    )
                    code_lines = _prompt_safe_code_snippet(
                        checked_code,
                        limit=1200,
                    )
                    code = json.dumps(
                        "\n".join(code_lines),
                        ensure_ascii=False,
                    ) if code_lines else ""
                    if code:
                        if re.match(r"^\s*example(?=\s|[:({\[])", checked_code):
                            score = 31
                            evidence_class = "accepted_example"
                            structured_detail = (
                                "Lean-accepted standalone example evidence, not "
                                f"a proof of the handoff target: {code}"
                            )
                        else:
                            structured_detail = (
                                "Lean-accepted scratch proof for the handoff target; "
                                f"validated body: {code}"
                            )
                elif content_compact.startswith("try_lean rejected"):
                    score = 38
                    evidence_class = "lean_rejection"
                    error_match = re.search(
                        r"scratch proof \(([^)]+)\)",
                        content,
                        flags=re.IGNORECASE,
                    )
                    goals_match = re.search(
                        r"\bRemaining goals:\s*(.*)$",
                        content,
                        flags=re.IGNORECASE | re.DOTALL,
                    )
                    error_family = (
                        str(error_match.group(1)).strip()
                        if error_match is not None
                        else "lean_rejected"
                    )
                    residual = _compact_history_summary_text(
                        goals_match.group(1) if goals_match is not None else "",
                        limit=600,
                    )
                    structured_detail = f"error family `{error_family}`"
                    if residual:
                        structured_detail += f"; remaining goal(s): {residual}"
                    elif error_match is None:
                        diagnostic = _compact_history_summary_text(
                            content,
                            limit=300,
                        )
                        if diagnostic:
                            structured_detail += f"; diagnostic: {diagnostic}"
                else:
                    continue
            elif name == "try_skeleton":
                try:
                    payload = json.loads(content_compact)
                except Exception:
                    payload = None
                update = (
                    payload.get("proof_state_update")
                    if isinstance(payload, dict)
                    else None
                )
                status = str(
                    update.get("status", "")
                    if isinstance(update, dict)
                    else ""
                )
                if status not in {
                    "spawned_remaining_goals",
                    "closed",
                    "root_finalized",
                }:
                    continue
                score = 39
                evidence_class = "proof_state"
                raw_code = str(args.get("code", "") or "")
                fenced_blocks = extract_code_fences(raw_code)
                checked_code = (
                    str(fenced_blocks[0] or "").strip()
                    if fenced_blocks
                    else raw_code.strip()
                )
                code_lines = _prompt_safe_code_snippet(
                    checked_code,
                    limit=900,
                )
                code = json.dumps(
                    "\n".join(code_lines),
                    ensure_ascii=False,
                ) if code_lines else ""
                try:
                    residual_count = int(
                        update.get("residual_goal_count", 0) or 0
                    )
                except Exception:
                    residual_count = 0
                structured_detail = (
                    f"Lean-validated proof-state reduction `{status}`"
                    + (
                        f" with {residual_count} residual goal(s)"
                        if residual_count > 0
                        else ""
                    )
                    + (f"; validated scaffold: {code}" if code else "")
                )
            elif name == "check_lean":
                score = 30
                evidence_class = "declaration_signature"
                signatures = []
                check_blocks = re.split(
                    r"(?m)(?=^\d+\.\s+#check\s+)",
                    content,
                )
                for block in check_blocks:
                    block_lines = block.splitlines()
                    if block_lines and re.match(
                        r"^\d+\.\s+#check\s+",
                        block_lines[0],
                    ):
                        block_lines = block_lines[1:]
                    compact_line = _compact_history_summary_text(
                        "\n".join(block_lines),
                        limit=900,
                    )
                    if (
                        " : " not in compact_line
                        or compact_line.lower().startswith(("error", "warning"))
                    ):
                        continue
                    signatures.append(compact_line)
                    if len(signatures) >= 3:
                        break
                if signatures:
                    structured_detail = (
                        "relevant checked declaration signature(s): "
                        + " | ".join(signatures)
                    )
            elif name == "search_mathlib" and re.match(
                r"^\d+\s+match\(es\):", content_compact
            ):
                score = 25
                evidence_class = "retrieval"
            if score <= 0:
                continue
            preview = _compact_history_summary_text(content, limit=220)
            if structured_detail:
                preview = structured_detail
            if preview:
                if name == "search_mathlib":
                    preview = (
                        "unverified candidate(s); re-run/check before citing: "
                        f"{preview}"
                    )
                elif name == "try_lean":
                    if content_compact.startswith("try_lean accepted."):
                        preview = (
                            "historical scratch check only; re-run `try_lean` in "
                            f"the current target before using: {preview}"
                        )
                    else:
                        preview = (
                            "historical rejected scratch check; latest Lean rejection; "
                            "do not repeat without changing "
                            f"the code/route: {preview}"
                        )
                ranked.append(
                    (score, order, evidence_class or name, f"- {name}: {preview}")
                )
                order += 1
        else:
            pending_calls = {}
    # Preserve one best/latest representative per evidence class.  A global
    # top-N lets repeated accepted checks crowd the latest Lean rejection,
    # proof-state reduction, or declaration signature out of a refiner
    # handoff.  Within a class, score selects the stronger artifact and order
    # selects the most recent one.
    best_by_class: Dict[str, Tuple[int, int, str, str]] = {}
    for item in ranked:
        evidence_class = item[2]
        previous = best_by_class.get(evidence_class)
        if previous is None or (item[0], item[1]) > (previous[0], previous[1]):
            best_by_class[evidence_class] = item
    selected = sorted(
        best_by_class.values(),
        key=lambda item: (item[0], item[1]),
        reverse=True,
    )[: max(0, int(max_items or 0))]
    return [text for _score, _order, _evidence_class, text in selected]


def _compact_history_summary_text(text: str, *, limit: int) -> str:
    return _prompt_safe_inline_text(text, limit=limit)


# ---------------------------------------------------------------------------
# Decomposition-request detection (orchestration redirect for "give up" turns).
#
# Empirical analysis (2026-05-09) of 8,077 prove/refine turns across 500 failed
# runs found 12 distinct linguistic clusters where the LLM self-reports
# inability to proceed. The hardest signals (HARD tier below) match 100% of
# the time on Lean-rejected turns — zero of the regex-flagged turns ever
# passed Lean. This empirical precision justifies acting on the LLM's
# self-reported decomposition request without violating the
# "Lean = source of truth" contract: the gate runs AFTER Lean has already
# rejected, replacing the generic feedback with a cluster-specific
# directive that forces decomposition into named helpers rather than
# letting the LLM repeat the give-up shape.
#
# Cluster IDs (decoupled from regex bodies for routing):
#   helpers_insufficient — opaque helpers / additional lemmas / would-need
#   answer_opaque        — putnam_X_solution is opaque axiom
#   lemma_not_found      — specific named lemma missing from environment
#   no_sorry_allowed     — meta-commentary about the no-sorry rule
#   environment_hedge    — global proof/goal strategy-stuck hedge
#   scaffold_reject      — fail_if_success / placeholder / stub markers
# ---------------------------------------------------------------------------


# Helpers-insufficient: highest-precision target. Empirical clusters #4, #6, #12.
# The "(?:...){0,8}\s+" quantified gap allows up to 8 filler words between
# "additional/intermediate lemmas" and the trailing modal verb (e.g.
# "additional intermediate lemmas about the induced order on ℚ are needed")
# without losing precision (the noun list constrains matches).
#
# Code review fix (2026-05-09): the "X opaque helper lemma" arm previously
# allowed unconstrained ``\w+`` for X, which would have matched routine
# math sentences like "the opaque helper lemma is referenced". Constrained
# to a closed list of quantifier-style words.
_GIVEUP_HELPERS_INSUFFICIENT_QUANTIFIERS = (
    r"(?:two|three|four|five|six|seven|eight|nine|ten|several|few|some|many|"
    r"all|both|these|those|the|its|just|merely|\d+)"
)
_GIVEUP_HELPERS_INSUFFICIENT_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  (?:only\s+)?" + _GIVEUP_HELPERS_INSUFFICIENT_QUANTIFIERS + r"\s+opaque\s+helper\s+lemma"
    r"| opaque\s+(?:helper|lemma)s?\s+(?:are\s+)?(?:insufficient|don'?t\s+suffice|do\s+not\s+suffice)"
    r"| helper\s+lemmas?\s+(?:are\s+)?(?:insufficient|don'?t\s+suffice)"
    r"| (?:additional|more|further|extra|intermediate)\s+(?:intermediate\s+)?"
    r"   (?:helper|lemma|lemmas|hypothes\w+|fact|premise|axiom|construction|infrastructure)s?"
    r"   (?:\s+\S+){0,8}?\s+(?:are|is|needed|required|would|to\s+bridge|not\s+available)"
    r"| (?:a\s+)?full(?:\s+lean)?\s+(?:proof|formalization)\s+would\s+(?:need|require|construct|proceed|characterize)"
    r"| insufficient\s+(?:to|for|here|without)"
    r"| no\s+further\s+(?:lemma|axiom|hypothes\w+)s?\s+(?:are\s+)?available"
    r")"
)

# Answer-opaque: cluster #5. Routes to "derive value" framing in no-opaque mode.
_GIVEUP_ANSWER_OPAQUE_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  putnam_\w+_solution\s+is\s+(?:an?\s+)?(?:opaque|abstract|axiomati[sz]ed)"
    r"| opaque\s+(?:axiom|solution|constant)"
    r"| no\s+defining\s+(?:equation|equality)\s+for\s+that\s+constant"
    r"| (?:reduce|equate)\s+it\s+to\s+the\s+expected\s+value"
    r")"
)

# Lemma-not-found: cluster #9. Routes to search-then-decompose.
_GIVEUP_LEMMA_NOT_FOUND_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  (?:lemma|helper|theorem|hypothes\w+|premise|fact)s?\s+(?:are|is)\s+not\s+available"
    r"| no\s+such\s+(?:lemma|axiom|theorem|hypothesis|fact|tactic|definition)"
    r"| not\s+available\s+under\s+(?:a\s+)?(?:stable|discoverable)\s+name"
    r"| not\s+available\s+in\s+the\s+current\s+(?:mathlib|context|environment)"
    r"| mathlib\s+(?:does\s+not\s+(?:currently\s+)?(?:have|provide)|lacks)"
    r"| (?:missing|lacks?|need(?:s|ed)?|requires?|would\s+require)\s+"
    r"   (?:\S+\s+){0,8}?"
    r"   (?:prerequisite|hypothes\w+|assumption|premise|bridge|lemma|fact)s?"
    r")"
)

# No-sorry-allowed: cluster #8. Meta-commentary about the constraint.
_GIVEUP_NO_SORRY_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  no\s+`?sorry`?(?:\s*/\s*`?admit`?)?\s+(?:is\s+)?allowed"
    r"| sorry\s+(?:is|are)\s+(?:not|forbidden|disallowed)"
    r"| cannot\s+use\s+`?sorry`?"
    r"| can'?t\s+use\s+`?sorry`?"
    r"| (?:interface|environment|orchestrator|checker|system)\s+"
    r"   (?:rejects|forbids|disallows)\s+(?:any\s+use\s+of\s+)?`?sorry`?"
    r"| (?:rejects|forbids|disallows)\s+(?:any\s+use\s+of\s+)?`?sorry`?"
    r")"
)

# Environment-hedge: clusters #1, #3, #7, #11. Generic global
# proof/goal-level "cannot finish here".
# Code review fix (2026-05-09): the bare ``in this environment`` phrase
# matches routine prose ("we work in this context with ring axioms…")
# and was generating false positives on innocuous Lean error commentary.
# Tightened again after a live trace showed local proof-planning comments
# such as "this helper is not derivable" being misread as global give-up.
# This cluster now requires first-person inability language or an explicit
# root/proof/goal subject; local facts/helpers can still be handled by the
# more specific missing-lemma clusters when they say something is unavailable.
_GIVEUP_ENVIRONMENT_HEDGE_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  \b(?:I|we)\s+(?:cannot|can'?t|fail\s+to)\s+"
    r"    (?:finish|complete|prove|construct|produce|close|discharge|conclude|derive)"
    r"| \b(?:I\s+am|I'm|we\s+are|we're)?\s*unable\s+to\s+"
    r"    (?:prove|complete|finish|construct|produce|derive|close)\s+"
    r"    (?:the\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)"
    r"| \b(?:cannot|can'?t)\s+"
    r"    (?:finish|complete|prove|construct|produce|close|discharge|conclude|derive)\s+"
    r"    (?:the\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)"
    r"| \b(?:the\s+)?(?:overall\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)\s+"
    r"    (?:cannot|can'?t)\s+be\s+"
    r"    (?:completed|finished|proved|proven|closed|done|derived|constructed)"
    r"| \b(?:the\s+)?(?:overall\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)\s+"
    r"    (?:is|are)\s+not\s+(?:provable|derivable|solvable)"
    r"| \b(?:the\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)\s+"
    r"    (?:is|seems|appears)\s+beyond\s+(?:the\s+)?(?:scope|reach|capability)"
    r"| \b(?:I\s+give\s+up|I\s+admit\s+defeat)"
    r"| \bgive\s+up\s+on\s+(?:the\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)"
    r"| \b(?:the\s+)?(?:proof|goal|theorem|main\s+goal|root\s+goal)\s+is\s+blocked"
    r")"
)

# Scaffold-reject: clusters #2, #10. Stub/placeholder/fail_if_success markers.
# Code review fix (2026-05-09): ``skeleton`` removed — it's standard math
# vocabulary (``2-skeleton of CW complex``, ``simplicial skeleton``,
# ``skeleton category``) and matched routine topology / category-theory
# prose. The remaining tokens (``stub``, ``placeholder``, ``dummy``,
# ``no-op``) only fire as scaffold markers in the LLM's idiom, with
# ``fail_if_success`` being a hard structural indicator.
_GIVEUP_SCAFFOLD_REJECT_RE = re.compile(
    r"(?ix)"
    r"(?:"
    r"  \b(?:stub|placeholder|dummy|no-?op)\b"
    r"| fail_if_success"
    r"| dead[- ]end"
    r"| we\s+intentionally\s+produce\s+a"
    r")"
)

# Cluster routing — order matters. More specific clusters first so a turn
# matching multiple categories is routed to the most-actionable framing.
_GIVEUP_CLUSTERS: Tuple[Tuple[str, "re.Pattern[str]"], ...] = (
    ("helpers_insufficient", _GIVEUP_HELPERS_INSUFFICIENT_RE),
    ("answer_opaque", _GIVEUP_ANSWER_OPAQUE_RE),
    ("lemma_not_found", _GIVEUP_LEMMA_NOT_FOUND_RE),
    ("no_sorry_allowed", _GIVEUP_NO_SORRY_RE),
    ("scaffold_reject", _GIVEUP_SCAFFOLD_REJECT_RE),
    ("environment_hedge", _GIVEUP_ENVIRONMENT_HEDGE_RE),
)


# Structural collapse shapes: proofs that close via False.elim/absurd
# without justifying evidence, or are pure sorry/admit. Empirically these
# never pass Lean. Used as a co-condition to gate against false positives
# from aspirational mid-proof prose.
_PROOF_COLLAPSE_FALSE_ELIM_TRIVIAL_RE = re.compile(
    r"(?:False\.elim|absurd)\s*\(\s*by\s+[^()]{0,120}?\b(?:trivial|rfl|exact\s+(?:rfl|trivial|⟨⟩|\(\)))\b",
    re.IGNORECASE | re.DOTALL,
)
_PROOF_COLLAPSE_CIRCULAR_FALSE_RE = re.compile(
    r"have\s+\w*\s*:\s*False\s*:=\s*by\s+exact\s+False\.elim\b",
    re.IGNORECASE,
)
_PROOF_COLLAPSE_PURE_SORRY_RE = re.compile(
    r"^\s*by\s*(?:sorry|admit|fail_if_success)\s*$",
    re.IGNORECASE,
)
_PROOF_COLLAPSE_FAIL_IF_SUCCESS_RE = re.compile(
    r"\bfail_if_success\b",
    re.IGNORECASE,
)
_PROOF_PLACEHOLDER_RE = re.compile(
    r"\b(?:sorry|admit)\b",
    re.IGNORECASE,
)


def _proof_is_structural_collapse(proof: Optional[str]) -> bool:
    """Detect proofs whose closing move is structurally bankrupt.

    Returns True for:
      * ``False.elim (by ... trivial)`` / ``False.elim (by ... rfl)`` — appeals
        to False with a trivially-true sub-proof.
      * ``have _ : False := by exact False.elim ...`` — circular: builds False
        using False.elim.
      * Pure ``by sorry`` / ``by admit`` / ``by fail_if_success``.

    Returns False for:
      * Real ``False.elim`` use: applied to a destructured hypothesis or a
        named helper that genuinely produces ``False`` (e.g.
        ``False.elim (h.left ⟨...⟩)``).
      * Substantial proofs with real reasoning regardless of length.

    Used as the structural co-condition for the give-up gate.
    """

    code = _strip_lean_comments(str(proof or "")).strip()
    if not code:
        return False
    if _PROOF_COLLAPSE_PURE_SORRY_RE.fullmatch(code):
        return True
    if _PROOF_COLLAPSE_FAIL_IF_SUCCESS_RE.search(code):
        return True
    if _PROOF_COLLAPSE_FALSE_ELIM_TRIVIAL_RE.search(code):
        return True
    if _PROOF_COLLAPSE_CIRCULAR_FALSE_RE.search(code):
        return True
    return False


def _silent_giveup_cluster_from_proof(proof: Optional[str]) -> Optional[Dict[str, str]]:
    """Classify hard placeholder-only proofs after Lean has rejected them."""

    code = _strip_lean_comments(str(proof or "")).strip()
    if not code:
        return None
    if _PROOF_COLLAPSE_PURE_SORRY_RE.fullmatch(code) or _PROOF_PLACEHOLDER_RE.search(code):
        return {
            "cluster": "no_sorry_allowed",
            "match": "main proof is a placeholder",
        }
    if _PROOF_COLLAPSE_FAIL_IF_SUCCESS_RE.search(code):
        return {
            "cluster": "scaffold_reject",
            "match": "fail_if_success scaffold",
        }
    return None


def _classify_giveup_signal(
    llm_output: str,
    proof: Optional[str],
    *,
    require_structural_collapse: bool = True,
) -> Optional[Dict[str, str]]:
    """Classify the LLM's response as a decomposition-request, if any.

    Returns ``{"cluster": <id>, "match": <phrase>}`` when the LLM's reply
    matches a give-up cluster AND (optionally) the proof is structurally
    bankrupt. Returns None otherwise.

    The dual condition (linguistic + structural) is the precision guarantee:
    a turn that says "cannot finish" but emits a real proof attempt is
    routed to Lean as before; only when both signals fire is the turn
    redirected to decomposition. Empirical precision in mini_prover history:
    ~100% — zero linguistic-flagged turns passed Lean.

    ``require_structural_collapse=False`` is reserved for callers that have
    already confirmed Lean rejection; when the proof was already adjudicated
    failed by Lean, the structural co-condition is redundant and the gate
    can fire on linguistic signal alone (per the user's "post-Lean cascade
    redirect" design).

    Search scope is assistant prose outside fenced code blocks. Lean comments
    inside proof code are treated as proof-search breadcrumbs, not policy
    evidence. Structural placeholder-only proof bodies are still classified
    silently after Lean rejection via ``_silent_giveup_cluster_from_proof``.
    """

    # Code review fix (2026-05-09): require_structural_collapse=False
    # callers (the post-Lean cascade) want to fire on linguistic signal
    # alone — Lean rejection IS the structural failure signal. Move the
    # ``proof is None`` short-circuit AFTER the structural-collapse
    # check so a hypothetical caller passing proof=None with
    # require_structural_collapse=False can still match on llm_output.
    if require_structural_collapse:
        if proof is None or not _proof_is_structural_collapse(proof):
            return None

    text_to_check = _non_code_response_text(str(llm_output or ""))
    if not text_to_check.strip():
        if not require_structural_collapse:
            return _silent_giveup_cluster_from_proof(proof)
        return None

    for cluster_id, pattern in _GIVEUP_CLUSTERS:
        match = pattern.search(text_to_check)
        if match is not None:
            return {
                "cluster": cluster_id,
                "match": str(match.group(0))[:160].strip(),
            }
    if not require_structural_collapse:
        return _silent_giveup_cluster_from_proof(proof)
    return None


def _giveup_decomposition_nudge(
    cluster: str,
    *,
    opaque_mode: bool = False,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
    matched_phrase: str = "",
    recursion_depth: int = 0,
    max_recursion_depth: int = 3,
    role: str = "prove",
    allow_helper_decomposition: bool = True,
) -> str:
    """Compose the cluster-specific decomposition-redirect feedback text.

    Returned text replaces the generic post-Lean failure feedback when the
    give-up gate fires. These nudges no longer offer helper-only
    decomposition as the response to give-up prose. If a turn already
    externalized the hard step ("full formalization would proceed...",
    "Mathlib lacks...", etc.), the next prompt must steer back to an
    executable active-goal attempt or a genuinely different route.

    Code review fix (2026-05-09): nudge bodies are paraphrased to AVOID
    re-quoting the trigger phrasing. Prior templates contained the exact
    keywords that fire the regexes (``cannot finish in this environment``,
    ``additional intermediate lemmas would be needed``,
    ``stub/placeholder``), which would re-fire the gate when the LLM
    quoted the nudge in its next reply. Matched phrasing is rendered with
    backticks escaped to prevent markdown-injection on chat platforms.

    Answer visibility semantics:
      - ``True`` (default; the no-answer-leaderboard target variant) —
        ``putnam_X_solution`` is an opaque axiom. The LLM CANNOT query
        its value. Nudge tells the LLM to derive the value itself.
      - official visibility is prompt-visible only when ``opaque_mode`` is
        False, ``allow_official_answer_visibility`` is True, and the problem
        actually has an official answer payload.
    """

    safe_phrase = _prompt_safe_inline_text(
        matched_phrase,
        limit=120,
        preserve_backtick_contents=True,
    )
    quoted = f' (matched: "{safe_phrase}")' if safe_phrase else ""

    depth = max(0, int(recursion_depth or 0))
    cap = max(0, int(max_recursion_depth or 0))
    at_recursion_limit = cap > 0 and depth >= cap

    if at_recursion_limit:
        # Phase 2 (2026-05-09): at the recursion-depth cap, the nudge
        # MUST stop asking for further decomposition. Otherwise sub-
        # conversations chain forever (the LLM at depth N decomposes
        # into helper at depth N+1, which itself gives up at depth
        # N+2, etc.). At the cap, the only sensible directive is "make
        # the most direct attempt with the helpers you have, OR record
        # the give-up cluster for the parent search."
        base_close = (
            f"\n\nDecomposition-depth cap reached (depth {depth} / "
            f"{cap}). Do NOT request further helpers at this layer.\n"
            "Make ONE direct proof attempt at the goal using the "
            "hypotheses, preamble facts, and any verified helpers in scope. "
            "If a bridge is still missing, change strategy or prove the "
            "bridge locally; do not submit a placeholder local target, a "
            "new helper request, or a prose-only stop."
        )
        strategy_close = base_close
    else:
        decomposition_sentence = (
            "Do not answer with unproved helper requests or new helper "
            "obligations. Instead, manufacture the first needed local fact "
            "as a fully proved helper or local `have`; if the route is still "
            "too large, submit the concrete failed local `have`/`suffices` "
            "attempt and Lean diagnostic that exposed the next bridge. "
            if allow_helper_decomposition
            else (
                "This is a direct-proof sub-session: do not emit unproved "
                "helper obligations here; manufacture local theory inside the "
                "proof body with proved `have`/`suffices` steps, or expose "
                "only a concrete Lean failure from an attempted local proof. "
            )
        )
        base_close = (
            "\n\nNext-turn protocol:\n"
            "1. Submit one main proof attempt for the active goal.\n"
            "2. Use the newest Lean diagnostic to repair a concrete failing "
            "line, missing argument, or local target.\n"
            "3. If an intermediate fact remains unproved, make progress by "
            "proving it inside the attempted proof, shrinking it into the "
            "smallest Lean-checkable target, or pivoting to a different route; "
            "do not stop at prose. "
            + decomposition_sentence
            + "\n"
            "4. Existing verified helpers may support the proof, but absence "
            "of a named helper is not a proof boundary."
        )
        strategy_close = (
            "\n\nNext-turn protocol:\n"
            "1. Submit one main proof attempt for the active goal.\n"
            "2. Try a materially different strategy: cases/induction, "
            "rewriting the target, an explicit witness construction, a "
            "smaller bridge proved locally, or a different normalization of "
            "the same target. Do not invent impossible facts just to close "
            "the goal.\n"
            "3. Existing verified helpers may support the proof, but absence "
            "of a named helper is not a proof boundary.\n"
            "4. If a specific claim remains unproved, do not submit another "
            "placeholder proof around it; prove that claim in the active "
            "proof attempt or pivot."
        )

    if cluster == "helpers_insufficient":
        return (
            "Your reply admitted the existing helper set does not suffice."
            + quoted
            + " Treat that admission as a signal to repair the proof attempt "
            "around the first unproved intermediate fact, not as permission to stop "
            "proving the active goal."
            + base_close
        )
    if cluster == "answer_opaque":
        effective_visible_answer = official_answer_visible_to_llm(
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        if not effective_visible_answer:
            # opaque_mode=True (default): _solution values HIDDEN from the
            # LLM. The LLM is correctly observing the opacity. Force
            # decomposition: derive the value mathematically.
            if (
                not opaque_mode
                and allow_official_answer_visibility
                and official_answer_payload_present is not True
            ):
                hidden_reason = "not confirmed for this theorem"
                variant_sentence = "There is no confirmed official answer payload to query."
            else:
                hidden_reason = (
                    "opaque by design"
                    if opaque_mode
                    else "hidden because official-answer visibility is not enabled"
                )
                variant_sentence = (
                    "The official answer value is hidden in this run; you "
                    "cannot query the constant's value through Lean."
                )
            return (
                f"Yes — the solution constant is {hidden_reason} in this "
                "run. "
                + variant_sentence
                + quoted
                + "\n\nYou must derive the value yourself from the problem "
                "statement using ordinary mathematics, then use that value "
                "inside a proof attempt for the original goal. Note: any "
                "helper whose body or name "
                "references `putnam_X_solution` will be rejected by the "
                "answer-safety policy. Express the helper in terms of the "
                "problem's structural quantities, not the constant itself."
                + base_close
            )
        # Explicit with-answer control: the LLM sees the filled _solution
        # definitions. If it's still saying "opaque", it's misreading
        # the preamble.
        return (
            "This run exposes the filled `_solution` definitions in the "
            "preamble — re-examine it carefully, the value is shown."
            + quoted
            + " Use the shown value inside one proof attempt for the active "
            "goal; do not replace the turn with named helper stubs."
            + base_close
        )
    if cluster == "lemma_not_found":
        return (
            "Your reply treated a missing named theorem as a blocker."
            + quoted
            + " Two-step protocol:\n\n"
            "Step 1. If the exact name has not already been checked, call "
            "the Mathlib search tool once with several phrasings (look for "
            "the result type, the first argument, alternate keywords).\n"
            "Step 2. If search returns nothing usable, do not treat that as "
            "a stopping condition. Manufacture the fact as a local theorem, "
            "lemma, definition, or proved `have`; if it is too large, split "
            "it into smaller checked targets. Do not repeat absence-of-library "
            "commentary as the outcome."
            + base_close
        )
    if cluster == "no_sorry_allowed":
        return (
            "Bare `sorry` and `admit` in the main proof are rejected. "
            "Do not replace them with sorry-stub helper declarations. "
            "If the current bridge does not close, prove it locally or pivot; "
            "do not submit another non-closing proof, a new helper request, "
            "or a prose stop."
            + base_close
        )
    if cluster == "scaffold_reject":
        return (
            "Your reply contained markers Lean treats as proof failures."
            + quoted
            + " These cannot close goals.\n\nReplace the marker with an "
            "actual proof step that closes, or replace the failed route with "
            "a different proof route. Do not use `False.elim`, impossible "
            "inequalities, fake divisibility, or "
            "placeholder contradictions unless the contradiction is derived "
            "from real hypotheses Lean can check:"
            + base_close
        )
    # environment_hedge (default fallback)
    return (
        "Your reply hedged about completability rather than trying a "
        "different proof strategy."
        + quoted
        + " The attached proof closed via unjustified `False.elim` or "
        "trivial closer — Lean rejected it."
        + strategy_close
    )



def _format_invalid_helper_stub_with_main_feedback(
    *,
    stub_names: Sequence[str],
    root_equivalent_names: Optional[Sequence[str]] = None,
) -> str:
    stub_list = (
        ", ".join(f"`{_prompt_safe_helper_name(name)}`" for name in stub_names)
        or "a sorry-stub helper"
    )
    root_list = ", ".join(
        f"`{_prompt_safe_helper_name(name)}`" for name in (root_equivalent_names or ())
    )
    root_sentence = (
        " Also, the rejected helper restates the root goal; do not re-emit it. "
        "If a smaller bridge is needed, it must be fully proved inside the "
        "active proof attempt; do not leave it as a local placeholder."
        if root_list
        else ""
    )
    return (
        "Your Lean block declared sorry-stub helper(s) "
        f"{stub_list} while also submitting a main proof. Sorry stubs are not "
        "proof code. Submit one active-goal proof attempt whose helper "
        "declarations, if any, are fully proved. Do not submit intermediate "
        f"facts as local placeholders inside that proof body.{root_sentence}"
    )


def _format_root_equivalent_helper_feedback(
    root_equivalent_names: Sequence[str],
) -> str:
    rendered = ", ".join(
        f"`{_prompt_safe_helper_name(name)}`" for name in root_equivalent_names
    )
    return (
        "The helper decomposition was rejected because "
        f"{rendered or 'a proposed helper'} restated the root goal instead of "
        "making progress. Do not submit that bridge again. Put the required "
        "smaller facts inside one active-goal proof attempt only if those "
        "facts are fully proved there. Otherwise pivot the proof route; do "
        "not repackage the root as a helper request."
    )


def _format_repair_self_check_missing_feedback(
    content: Any = "",
    *,
    require_try_lean: bool = False,
    goal_statement: str = "",
    theorem_name: str = "",
    role: str = "prove",
) -> str:
    base = _repair_self_check_required_message(
        require_try_lean=require_try_lean,
        role=role,
    )
    try:
        helpers, proof = _extract_helpers_and_main(
            str(content or ""),
            theorem_name=str(theorem_name or ""),
        )
    except Exception:
        helpers, proof = [], None
    stubs = _sorry_stub_helper_names(helpers)
    root_equiv = _root_equivalent_sorry_stub_helper_names_from_blocks(
        helpers,
        goal_statement=goal_statement,
    )
    if stubs and proof is not None:
        return (
            base
            + "\n\n"
            + _format_invalid_helper_stub_with_main_feedback(
                stub_names=stubs,
                root_equivalent_names=root_equiv,
            )
        )
    if root_equiv:
        return base + "\n\n" + _format_root_equivalent_helper_feedback(root_equiv)
    return (
        base
        + "\n\n"
        "A rejected `try_lean` call does not count as a self-check. The final "
        "submitted Lean proof must exactly match a proof body that `try_lean` "
        "accepted in this turn. If no checked proof closes the active goal, "
        "do not submit a revised placeholder proof. Either try a different "
        "complete proof route, prove the needed local step inside the proof, "
        "or let the Lean diagnostic identify the next concrete repair. Do "
        "not answer this repair turn with helper stubs or a scheduler request."
    )


def _repair_content_is_helper_only_decomposition(
    content: Any,
    *,
    theorem_name: str = "",
) -> bool:
    """Return True when repair-turn content is pure sorry-stub decomposition.

    The repair self-check gate is meant to protect revised main proofs: after
    Lean rejects a proof, the next submitted proof body must have been accepted
    by ``try_lean`` in that same turn. A helper-only sorry-stub decomposition
    request is a different protocol and is deliberately handled by the no-proof
    cascade. Letting the tool loop reject it first strands valid sorry-stub
    child goals before D2's decomposition-task opener can materialize them.
    """

    try:
        helpers, proof = _extract_helpers_and_main(
            str(content or ""),
            theorem_name=str(theorem_name or ""),
        )
    except Exception:
        helpers, proof = [], None
    if proof is not None and not _lean_body_is_sorry_stub(proof):
        return False

    # Re-parse the actual fenced Lean chunks instead of trusting only the
    # helper extractor's output. A mixed reply such as ``by trivial`` followed
    # by a sorry-stub helper can otherwise look like "helpers, no proof" after
    # extraction and bypass the repair self-check before the mixed-mode policy
    # gets a chance to reject it.
    strict_candidates: List[str] = []
    blocks = extract_code_fences(str(content or ""))
    if not blocks:
        return False
    helper_header_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma)\b"
    )
    for raw_src in blocks:
        src = normalize_nat_factorial_notation(
            _strip_redundant_preamble_commands(str(raw_src or "").strip())
        )
        if not src:
            continue
        leading, chunks = _split_top_level_chunks(src)
        if _strip_lean_comments_and_strings(leading).strip():
            return False
        if not chunks:
            return False
        for chunk in chunks:
            text = str(chunk or "").strip()
            if not helper_header_re.match(text):
                return False
            name = helper_decl_name(text) or ""
            if not name or name.endswith("_solution"):
                return False
            if not helper_decl_body(text):
                return False
            if not _helper_is_sorry_stub(text):
                return False
            strict_candidates.append(text)
    helper_names = {
        helper_decl_name(str(candidate or "")) or ""
        for candidate in strict_candidates
    }
    extracted_names = {
        helper_decl_name(str(helper or "")) or ""
        for helper in helpers
    }
    if not extracted_names and theorem_name:
        extracted_names = {str(theorem_name or "")}
    return bool(strict_candidates) and extracted_names.issubset(
        helper_names
    )


def _format_no_proof_extracted_feedback(
    *,
    helpers: Sequence[str] = (),
    lemma_dag_candidate_helpers: Sequence[str] = (),
    role: str = "prove",
    banked_names: Sequence[str] = (),
) -> str:
    if helpers or lemma_dag_candidate_helpers:
        saved = ""
        if banked_names:
            saved = (
                " The controller saved the parseable helper declaration(s) "
                "as unverified proposals for later recursive planning, but "
                "this turn still needs one valid submission mode."
            )
        return (
            "I found helper declarations but no main proof. On the next turn, "
            "submit a proof attempt for the active goal. "
            "Any helper declarations must be fully proved before the final "
            "proof body; do not replace the main proof with unproved local "
            "bridge placeholders or helper stubs. When the root is too large, "
            "make the helper declaration the smallest manufactured fact and "
            f"prove it completely before relying on it.{saved}"
        )
    return (
        "I don't see a main proof in your reply. Submit one Lean proof "
        "attempt for the active goal; the next ```lean block must end with "
        "`example : <main_goal_type> := by ...` or a bare `by ...` proof "
        "attempt. If the proof needs intermediate facts, manufacture them as "
        "proved local `have`/`suffices` steps or fully proved helpers before "
        "use. Do not replace the proof attempt with named helper signatures "
        "ending in `:= by sorry`."
    )


def _drop_last_assistant_if_content(conv: Any, content: Any) -> bool:
    """Remove the just-generated assistant reply when it failed policy gates."""

    history = getattr(conv, "history", None)
    if not isinstance(history, list) or not history:
        return False
    last = history[-1]
    if not isinstance(last, dict) or last.get("role") != "assistant":
        return False
    if str(last.get("content", "") or "") != str(content or ""):
        return False
    history.pop()
    setattr(conv, _REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY, True)
    return True


# ---------------------------------------------------------------------------
# Lean failure analysis.
#
# The retry loop needs repair guidance, not a raw compiler transcript. This
# analyzer translates LeanParseResult into compact, model-facing feedback while
# leaving the full raw output in run artifacts for humans/debuggers.
# ---------------------------------------------------------------------------

_REJECTED_FRAGMENT_HEADER = "Rejected code fragment(s) you must not reuse unchanged:"
_TRANSIENT_GOAL_TARGET_HEADER = (
    "Lean's unsolved goal target(s) from the previous attempt. Do NOT "
    "repackage them as `have h : <target> := by sorry` / `exact h` "
    "helpers — that is the same failure re-dressed. Fix the specific "
    "proof step that left the goal open:"
)
_REPAIR_SELF_CHECK_MARKER = "[repair self-check required]"


# Shared filter — low-signal atoms that are not informative as transient
# goal targets (single type names, integer literals, single identifiers).
_TRANSIENT_GOAL_LOW_SIGNAL_ATOMS = {
    "Bool",
    "Empty",
    "False",
    "Int",
    "Nat",
    "PUnit",
    "Prop",
    "Rat",
    "Real",
    "Sort",
    "String",
    "True",
    "Type",
    "Unit",
    "ℕ",
    "ℤ",
    "ℚ",
    "ℝ",
    # Bare Unicode quantifiers — Lean diagnostic text occasionally
    # produces these as standalone ``⊢ ∃`` lines (truncated/malformed
    # diagnostic). They carry zero semantic content as goal targets,
    # bloat feedback messages, and cannot meaningfully match the
    # narrow gate's ``: <target> := sorry`` shape. Round-3 fix.
    "∃",
    "∀",
    # Bare Unicode True/False propositions — appear as ``⊢ ⊤`` /
    # ``⊢ ⊥`` after ``simp``-style rewrites. Same low-signal-content
    # rationale as ∃/∀. Round-4 fix.
    "⊤",
    "⊥",
    # Bare Unicode logical connectives — same rationale; can appear
    # in truncated diagnostics but never as a goal target on their own.
    "↔",
    "→",
    "∧",
    "∨",
    "¬",
}


def _normalize_fragment_text(value: Any) -> str:
    return " ".join(str(value or "").strip("`'\"“”.,;: ").split())


def _normalize_goal_target_text(value: Any) -> str:
    text = " ".join(str(value or "").strip("'\"“”.,;: ").split())
    if text.startswith("`") and text.endswith("`") and len(text) >= 2:
        text = text[1:-1].strip()
    return text


def _is_low_signal_goal_target(text: str) -> bool:
    if not text:
        return True
    if text in _TRANSIENT_GOAL_LOW_SIGNAL_ATOMS:
        return True
    if re.fullmatch(r"-?\d+", text):
        return True
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", text):
        return True
    return False


def _extract_rejected_code_fragments(analysis: Dict[str, Any]) -> List[str]:
    """Extract concrete Lean code fragments from diagnostics for repair guards.

    Returns only fragments that originated as **code the LLM submitted**
    (identifiers, type-mismatch operands, "in the application X" expressions,
    explicit unknown_identifier/unknown_constant details). Lean's transient
    unsolved-goal targets (`⊢ ...` lines, `remaining_goals[i].target`) are
    deliberately NOT collected here — they live in
    ``_extract_transient_goal_targets`` and are surfaced under a separate
    header with non-prohibitive framing. Conflating the two poisons the LLM
    by telling it to "not reuse" expressions it never submitted as code,
    which on putnam_2012_a2 (2026-05-12) caused the LLM to abandon a
    fixable type_mismatch and pivot to sorry-stub decomposition.
    """

    fragments: List[str] = []

    def add(value: Any) -> None:
        text = _normalize_fragment_text(value)
        if not text:
            return
        if text not in fragments:
            fragments.append(text)

    for diag in list(analysis.get("diagnostics") or []):
        message = str((diag or {}).get("message") or "")
        if not message:
            continue
        for match in re.finditer(
            r"\bunknown (?:identifier|constant)\s+[`'“\"]([^`'”\"\s]+)[`'”\"]?",
            message,
            flags=re.IGNORECASE,
        ):
            add(match.group(1))
        for match in re.finditer(
            r"\bunknown (?:identifier|constant)\s+([^\s`'\"“”]+)",
            message,
            flags=re.IGNORECASE,
        ):
            add(match.group(1))
        for match in re.finditer(
            r"\bin the application\s+([^\n]+)",
            message,
            flags=re.IGNORECASE,
        ):
            add(match.group(1).rstrip(".,;: "))
        multi = re.search(
            r"\bin the application\s*\n\s*([^\n]+)",
            message,
            flags=re.IGNORECASE,
        )
        if multi:
            add(multi.group(1))

        fallback = re.search(
            r"(?:Type mismatch|Application type mismatch).*?\n\s*([^\n]+)\s*\n\s*has type",
            message,
            flags=re.IGNORECASE | re.DOTALL,
        )
        if fallback:
            add(fallback.group(1))

    details = dict(analysis.get("details") or {})
    for key in ("unknown_identifier", "unknown_constant"):
        unknown = details.get(key)
        if not unknown:
            continue
        add(unknown)
    return fragments


def _extract_transient_goal_targets(analysis: Dict[str, Any]) -> List[str]:
    """Return Lean unsolved-goal targets from the failure analysis.

    These are Lean's internal proof obligation states (``⊢ X = Y`` lines in
    diagnostic text and structured ``remaining_goals[i].target`` entries),
    NOT code the LLM submitted. They are surfaced under a separate header so
    the LLM is warned specifically against goal-as-helper abuse (wrapping a
    failing goal as ``have h : <goal> := by sorry; exact h``) rather than
    being told the strings are forbidden code fragments. The downstream gate
    ``_proof_repackages_transient_goal_target`` catches sorry-helper wrapping,
    while ``_proof_reuses_rejected_fragments`` sees only rejected-code bullets.
    """

    targets: List[str] = []

    def add(value: Any) -> None:
        text = _normalize_goal_target_text(value)
        if not text or _is_low_signal_goal_target(text):
            return
        if text not in targets:
            targets.append(text)

    for diag in list(analysis.get("diagnostics") or []):
        message = str((diag or {}).get("message") or "")
        if not message:
            continue
        for match in re.finditer(r"⊢\s+([^\n]+)", message):
            add(match.group(1))

    for goal in list(analysis.get("remaining_goals") or []):
        if isinstance(goal, dict):
            add(goal.get("target"))

    return targets


def _repair_replacement_hints(
    analysis: Dict[str, Any],
    fragments: Sequence[str],
) -> List[str]:
    """Return narrow positive repair hints for mechanical Lean diagnostics."""

    return []


def _format_repair_obligation_block(analysis: Dict[str, Any]) -> List[str]:
    fragments = _extract_rejected_code_fragments(analysis)
    transient_targets = _extract_transient_goal_targets(analysis)
    hints = _repair_replacement_hints(analysis, fragments)
    if not fragments and not hints and not transient_targets:
        return []
    lines: List[str] = [""]
    if fragments:
        lines.append(_REJECTED_FRAGMENT_HEADER)
        for fragment in fragments:
            safe_fragment = _prompt_safe_inline_text(
                fragment,
                limit=_REJECTED_FRAGMENT_DISPLAY_LIMIT,
            )
            lines.append(f"- `{safe_fragment}`")
        lines.append(
            "If one of these fragments still appears unchanged, make a "
            "local edit to that failing expression before the next `try_lean`; "
            "you may keep the surrounding proof scaffold and checked steps."
        )
    if transient_targets:
        if fragments:
            lines.append("")
        lines.append(_TRANSIENT_GOAL_TARGET_HEADER)
        for target in transient_targets:
            lines.append(
                f"- `{_prompt_safe_lean_diagnostic_text(target, limit=240)}`"
            )
        lines.append(
            "These are Lean's pending goals, not code you wrote. You may "
            "still use the underlying expressions inside a real proof step; "
            "you may NOT submit one of them as a sorry-stub helper to "
            "discharge the same obligation."
        )
    if hints:
        lines.append("")
        lines.append("Concrete local replacement hint:")
        for hint in hints:
            lines.append(f"- {hint}")
    return lines


def _repair_payload_from_failure_analysis(
    analysis: Dict[str, Any],
) -> Dict[str, List[str]]:
    """Raw repair-state payload stored outside provider-visible messages."""

    return {
        "fragments": _extract_rejected_code_fragments(analysis),
        "transient_goal_targets": _extract_transient_goal_targets(analysis),
    }


def _latest_repair_feedback(conv: Any) -> str:
    for msg in reversed(list(getattr(conv, "history", []) or [])):
        if msg.get("role") != "user":
            continue
        content = str(msg.get("content", "") or "")
        semantics = _message_repair_semantics(msg)
        if semantics == _REPAIR_FEEDBACK:
            return content
        if semantics == _REPAIR_CONTINUATION:
            continue
        if semantics == _REPAIR_BOUNDARY:
            break
        if _is_repair_feedback_content(content):
            return content
        if _is_repair_cycle_neutral_user_message(msg):
            continue
        break
    return ""


def _repair_feedback_messages_in_current_cycle(conv: Any) -> List[Dict[str, Any]]:
    """Return repair-feedback user messages in the active tail cycle.

    A "repair feedback" message contains either ``"Lean rejected that proof"``
    or the ``_REPAIR_SELF_CHECK_MARKER`` token. The *current repair cycle* is the
    contiguous run of such user messages at the tail of ``conv.history`` — it
    terminates at the first non-repair user/handoff message encountered
    (walking backwards) or at the head of history. Internally generated
    model-visible control prompts, such as the tool-budget exhaustion prompt,
    are neutral: they do not create new repair feedback, but they also do not
    erase the active cycle before policy gates inspect the final proof.

    Returns the messages in **tail-first order** (most recent first). Multiple
    consecutive repair feedbacks (e.g. a self-check marker following a Lean
    rejection on the prior turn) are all part of the same cycle and their
    fragments/targets must be unioned.

    Assistant / tool / system messages are skipped: tool outputs in the middle
    of a turn do not end the cycle; only a new *user* message can.

    Structural root-cause fix for B1-B4 (2026-05-18 audit). Prior to this
    helper, repair-state was cached on ``Conversation`` attributes that
    survived history mutations (compaction at line 1080+, history reset at
    10800, branch-B asymmetric updates at 1233-1240). Deriving from history
    means there is nothing to invalidate: every reader sees the current
    source of truth, while still accumulating fragments across consecutive
    repair messages so a self-check marker does not erase the prior
    rejection's fragments.
    """

    messages: List[Dict[str, Any]] = []
    for msg in reversed(list(getattr(conv, "history", []) or [])):
        if not isinstance(msg, dict):
            continue
        role = msg.get("role")
        if role != "user":
            continue  # skip assistant / tool / system between turns
        semantics = _message_repair_semantics(msg)
        if semantics == _REPAIR_FEEDBACK:
            messages.append(msg)
            continue
        if semantics == _REPAIR_CONTINUATION:
            continue
        if semantics == _REPAIR_BOUNDARY:
            break
        content = str(msg.get("content", "") or "")
        if _is_repair_feedback_content(content):
            messages.append(msg)
            continue  # keep walking — earlier repair feedback in same cycle
        if _is_repair_cycle_neutral_user_message(msg):
            continue
        break  # non-repair user message ends the cycle
    return messages


def _repair_feedback_texts_in_current_cycle(conv: Any) -> List[str]:
    """Return active repair-feedback texts in tail-first order."""

    return [
        str(msg.get("content", "") or "")
        for msg in _repair_feedback_messages_in_current_cycle(conv)
    ]


def _repair_turn_requires_self_check(conv: Any) -> bool:
    """True iff there is at least one repair feedback in the current cycle.

    History-derived (B1-B4 fix, 2026-05-18). Replaces a cached
    ``repair_self_check_active`` attribute read that could go stale across
    history mutations.
    """

    return bool(_repair_feedback_texts_in_current_cycle(conv))


def _repair_self_check_required_message(
    *,
    require_try_lean: bool = False,
    role: str = "prove",
) -> str:
    check_sentence = (
        "you must call `try_lean` on the revised proof. "
        if require_try_lean
        else "you must run the configured Lean self-check on the revised proof. "
    )
    mode_sentence = (
        "Do not submit broad helper-stub decomposition or unproved local "
        "bridge placeholders. The revised proof must be checked, or the "
        "response should pivot to a different checked proof route rather "
        "than asking the scheduler to prove a separate prerequisite."
    )
    return (
        f"{_REPAIR_SELF_CHECK_MARKER}\n"
        "This is a Lean repair turn. Before submitting a final main proof block, "
        f"{check_sentence}"
        "Do not just describe the repair. Use the tool result to correct the "
        f"actual code, then submit the checked block. {mode_sentence}"
    )


def _parse_bullets_under_header(text: str, header: str) -> List[str]:
    """Return the back-tick-quoted bullets under a specific section header.

    Walks ``text`` line by line; once the header line is seen, collects
    bullet lines (``- `bullet content```) until a non-bullet non-empty
    line ends the section. The same content may have multiple sections
    (e.g. both rejected-fragment and transient-goal-target); each is
    parsed via its own header.
    """

    if header not in text:
        return []
    items: List[str] = []
    in_section = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped == header:
            in_section = True
            continue
        if in_section and stripped and not stripped.startswith("- "):
            in_section = False
            continue
        if not in_section or not stripped.startswith("- "):
            continue
        match = re.search(r"`([^`]+)`", stripped)
        if match:
            fragment = " ".join(match.group(1).split())
            if fragment and fragment not in items:
                items.append(fragment)
    return items


def _rejected_fragments_from_feedback_text(content: Any) -> List[str]:
    """Parse the "Rejected code fragment(s)" bullets only.

    Adversarial-review 2026-05-13 (regression-from-Fix-#1): Yesterday's
    fix merged BOTH this header and the "Lean's unsolved goal
    target(s)" header into a single banned-fragment list fed to the
    strict identifier-bounded gate
    (``_proof_reuses_rejected_fragments``). The strict gate then banned
    the goal expression itself — including the bare ``∃`` token — from
    appearing in any subsequent proof, which makes any honest proof of
    an existential goal impossible. The two sections are now parsed by
    separate functions and gated separately:

    - Rejected code fragments go through the strict
      ``_proof_reuses_rejected_fragments`` gate (substring + identifier
      boundary). These are LLM-submitted code Lean already rejected;
      any reuse is wrong.
    - Transient goal targets are parsed by
      ``_transient_goal_targets_from_feedback_text`` and fed to the
      narrow ``_proof_repackages_transient_goal_target`` gate, which
      only fires when the target appears as the type of a sorry-bodied
      declaration — the original "goal-as-helper" failure mode that
      motivated Fix #1 — without banning the goal expression in any
      other context.
    """

    return _parse_bullets_under_header(str(content or ""), _REJECTED_FRAGMENT_HEADER)


def _transient_goal_targets_from_feedback_text(content: Any) -> List[str]:
    """Parse the "Lean's unsolved goal target(s)" bullets only.

    Companion to ``_rejected_fragments_from_feedback_text``. Returns
    the open-goal target strings Lean reported as remaining; the
    downstream narrow gate (``_proof_repackages_transient_goal_target``)
    fires only when the LLM repackages one of these targets as a
    sorry-bodied declaration (``have h : <target> := by sorry``).
    """

    return _parse_bullets_under_header(
        str(content or ""), _TRANSIENT_GOAL_TARGET_HEADER
    )


def _message_has_visible_repair_payload(msg: Dict[str, Any]) -> bool:
    content = str(dict(msg or {}).get("content", "") or "")
    return bool(
        _rejected_fragments_from_feedback_text(content)
        or _transient_goal_targets_from_feedback_text(content)
    )


def _rejected_fragments_from_latest_feedback(conv: Any) -> List[str]:
    fragments: List[str] = []

    def add_many(values: Sequence[str]) -> None:
        for fragment in values:
            if fragment and fragment not in fragments:
                fragments.append(fragment)

    # History-derived (B1-B4 fix, 2026-05-18). Unions fragments across all
    # consecutive repair-feedback user messages at the tail of history. Private
    # payload metadata is authoritative when present, so compaction can keep a
    # later policy-feedback message without forgetting the Lean rejection payload
    # that made the turn a repair. Visible text parsing remains the compatibility
    # path for raw legacy history records.
    newer_own_payload_seen = False
    for msg in _repair_feedback_messages_in_current_cycle(conv):
        if newer_own_payload_seen and bool(msg.get(_REPAIR_PAYLOAD_CARRIED_KEY)):
            break
        content = str(msg.get("content", "") or "")
        add_many(
            _repair_payload_values_from_message(
                msg,
                _REPAIR_REJECTED_FRAGMENTS_KEY,
                _rejected_fragments_from_feedback_text(content),
            )
        )
        if bool(msg.get(_REPAIR_PAYLOAD_RESET_BEFORE_KEY)):
            break
        if _message_has_visible_repair_payload(msg):
            newer_own_payload_seen = True
    return fragments


_LEAN_IDENT_BOUNDARY_CHARS = r"\w'.₀₁₂₃₄₅₆₇₈₉"
_LEAN_SIMPLE_IDENT_RE = re.compile(r"^[^\s()]+$")


def _lean_ident_boundary_pattern(identifier: str) -> str:
    escaped = re.escape(str(identifier or ""))
    return rf"(?<![{_LEAN_IDENT_BOUNDARY_CHARS}]){escaped}(?![{_LEAN_IDENT_BOUNDARY_CHARS}])"


def _compact_lean_for_fragment_match(value: Any) -> str:
    text = " ".join(_strip_lean_comments_and_strings(str(value or "")).split())
    previous = None
    while previous != text:
        previous = text
        text = re.sub(
            r"\(\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*\)",
            r"\1",
            text,
        )
    text = _canonicalize_simp_bracket_lists(text)
    # B5 fix REVERTED (2026-05-18 audit, adversary C): angle brackets in Lean
    # are NOT commutative in general — they denote ``Exists.intro``,
    # ``And.intro``, positional structure literals, ``Sigma.mk``, etc., all of
    # which are order-sensitive. Canonicalizing by sort would produce false
    # positives on legitimate repair attempts where the LLM swaps witness/
    # proof or restructures a positional constructor. The original B5 claim
    # ("swapping ⟨a,b,c⟩ to ⟨c,b,a⟩ is the same proof") was semantically
    # wrong — a swapped angle-bracket IS a different Lean expression that
    # the LLM is legitimately allowed to try.
    text = re.sub(r"\s*([\[\],])\s*", r"\1", text)
    return text


def _canonicalize_simp_bracket_lists(text: str) -> str:
    """Normalize simple ``simp [a, b]`` lists for rejected-fragment matching."""

    def repl(match: re.Match[str]) -> str:
        head = " ".join(str(match.group("head") or "").split())
        body = str(match.group("body") or "")
        if any(ch in body for ch in "[]{}()"):
            return match.group(0)
        items = [
            re.sub(r"\s+", " ", item.strip())
            for item in body.split(",")
            if item.strip()
        ]
        if not items:
            return match.group(0)
        return f"{head} [" + ", ".join(sorted(items)) + "]"

    return re.sub(
        r"(?P<head>\bsimp(?:_all)?(?:\s+only)?)\s*\[(?P<body>[^\[\]]*)\]",
        repl,
        text,
    )


def _tool_call_name(tc: Any) -> str:
    if not isinstance(tc, dict):
        return ""
    return str(((tc.get("function") or {}).get("name") or "")).strip()


_REPAIR_FORMAL_VERIFIER_TOOLS = frozenset(
    {"try_lean", "certify_counterexample"}
)
_REPAIR_DISCOVERY_TOOL_CALL_QUOTA = 3


def _select_tool_calls_for_repair_budget(
    tool_calls: Sequence[Dict[str, Any]],
    budget_remaining: int,
    *,
    repair_self_check_required: bool,
    repair_self_check_seen: bool,
    repair_self_check_attempted: bool = False,
    repair_discovery_calls_used: int = 0,
) -> Tuple[List[Dict[str, Any]], int, bool]:
    """Split a repair tool budget into bounded discovery and verification.

    Returns ``(calls_to_run, dropped_count, reserved_for_try_lean)``.  The
    ``try_lean`` checks a repaired positive proof and ``certify_counterexample``
    checks the target's exact negation. Either is a valid formal resolution of
    the active repair turn.

    Discovery is a distinct, cumulative phase with a small fixed quota.  It
    may diagnose an API or theorem-name problem, but it cannot consume nearly
    the entire turn before the model exposes an executable proposition to a
    formal verifier. A rejected verifier remains useful diagnostic evidence,
    not permission to reopen unbounded discovery.
    """

    calls = [tc for tc in list(tool_calls or []) if isinstance(tc, dict)]
    budget = max(0, int(budget_remaining or 0))
    if not calls or budget <= 0:
        return [], len(calls), False

    if not (repair_self_check_required and not repair_self_check_seen):
        selected = calls[:budget]
        return selected, max(0, len(calls) - len(selected)), False

    discovery_remaining = max(
        0,
        _REPAIR_DISCOVERY_TOOL_CALL_QUOTA
        - max(0, int(repair_discovery_calls_used or 0)),
    )
    verifier_indexes = [
        idx
        for idx, tc in enumerate(calls)
        if _tool_call_name(tc) in _REPAIR_FORMAL_VERIFIER_TOOLS
    ]
    if verifier_indexes:
        first_verifier_index = verifier_indexes[0]
        # Keep only the bounded discovery prefix that precedes verification.
        # Preserve every verifier that fits the physical budget, in provider
        # order: a malformed/rejected first check is not authority to hide a
        # later accepted or infrastructure-compliant check from the same
        # response. Discovery after verification cannot influence the proof
        # already submitted and belongs to a later phase/round.
        discovery_prefix = [
            tc
            for tc in calls[:first_verifier_index]
            if _tool_call_name(tc) not in _REPAIR_FORMAL_VERIFIER_TOOLS
        ]
        verifier_calls = [
            tc
            for tc in calls[first_verifier_index:]
            if _tool_call_name(tc) in _REPAIR_FORMAL_VERIFIER_TOOLS
        ][:budget]
        discovery_capacity = min(
            discovery_remaining,
            len(discovery_prefix),
            max(0, budget - len(verifier_calls)),
        )
        selected = [
            *discovery_prefix[:discovery_capacity],
            *verifier_calls[: max(0, budget - discovery_capacity)],
        ]
        return selected, max(0, len(calls) - len(selected)), False

    # No verifier in this batch: run only the remaining discovery tranche and
    # retain one physical tool slot for the next provider response. Once the
    # cumulative discovery quota is spent, execute nothing and immediately
    # request an executable formal check.
    selected = calls[: min(discovery_remaining, max(0, budget - 1))]
    return selected, max(0, len(calls) - len(selected)), True


def _fragment_reused_in_compact_proof(fragment: str, proof_source: str) -> bool:
    fragment_text = _compact_lean_for_fragment_match(fragment)
    proof_text = _compact_lean_for_fragment_match(proof_source)
    if not fragment_text:
        return False

    parts = fragment_text.split()
    if len(parts) == 1:
        if _single_token_fragment_is_locally_bound(parts[0], proof_source):
            return False
        return bool(re.search(_lean_ident_boundary_pattern(parts[0]), proof_text))
    if len(parts) > 2:
        return fragment_text in proof_text

    fn = parts[0]
    arg = parts[1]
    if not (
        _LEAN_SIMPLE_IDENT_RE.match(fn)
        and _LEAN_SIMPLE_IDENT_RE.match(arg)
    ):
        return False

    fn_names = [fn]
    if "." in fn:
        fn_names.append(fn.rsplit(".", 1)[-1])
    fn_pattern = "|".join(_lean_ident_boundary_pattern(name) for name in fn_names)
    arg_pattern = _lean_ident_boundary_pattern(arg)
    direct_application = (
        rf"@?(?:{fn_pattern})\s+\(?{arg_pattern}\)?"
    )
    if re.search(direct_application, proof_text):
        return True
    explicit_application = (
        rf"@(?:{fn_pattern})"
        rf"(?:\s+\(?[A-Za-z_][A-Za-z0-9_'.]*\)?){{0,2}}"
        rf"\s+\(?{arg_pattern}\)?"
    )
    if re.search(explicit_application, proof_text):
        return True

    basename = fn.rsplit(".", 1)[-1]
    dot_pattern = (
        rf"(?<![{_LEAN_IDENT_BOUNDARY_CHARS}]){re.escape(arg)}"
        + r"\s*\.\s*"
        + re.escape(basename)
        + rf"(?![{_LEAN_IDENT_BOUNDARY_CHARS}])"
    )
    if re.search(dot_pattern, proof_text):
        return True

    return False


def _single_token_fragment_is_locally_bound(fragment: str, proof_text: str) -> bool:
    token = str(fragment or "").strip()
    if not token or "." in token:
        return False
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token):
        return False

    source = _strip_lean_comments_and_strings(str(proof_text or ""))
    ident = _lean_ident_boundary_pattern(token)
    uses = list(re.finditer(ident, source))
    if not uses:
        return False

    line_infos: List[Tuple[int, int, str, int]] = []
    offset = 0
    for raw_line in source.splitlines(keepends=True):
        line = raw_line.rstrip("\r\n")
        end = offset + len(line)
        indent = len(line) - len(line.lstrip())
        line_infos.append((offset, end, line, indent))
        offset += len(raw_line)
    if not line_infos:
        line_infos.append((0, len(source), source, 0))

    def line_for(pos: int) -> Tuple[int, int, str, int]:
        for start, end, line, indent in line_infos:
            if start <= pos <= end:
                return start, end, line, indent
        return line_infos[-1]

    def scope_end_after(line_start: int, line_end: int, indent: int) -> int:
        for next_start, _next_end, next_line, next_indent in line_infos:
            if next_start <= line_start:
                continue
            stripped = next_line.strip()
            if stripped.startswith("·") and next_indent <= indent:
                return next_start
            if next_indent < indent:
                return next_start
        return len(source)

    immediate_binders: List[Dict[str, int]] = []
    for pattern in [
        rf"\bintro(?:s)?\s+[^.;\n]*{ident}",
        rf"\brintro\s+[^.;\n]*{ident}",
        rf"\bcase\s+[^:=\n]*{ident}",
        rf"\bfun\s+[^=>(\n]*{ident}\s*(?:=>|↦)",
        rf"\bfix\s+[^.;\n]*{ident}",
        rf"\brcases\b[^\n;]*\bwith\b[^\n;]*{ident}",
        rf"\bobtain\b[^\n;]*{ident}[^\n;]*:=",
    ]:
        for binder in re.finditer(pattern, source):
            name_match = re.search(ident, binder.group(0))
            name_start = binder.start() + (name_match.start() if name_match else 0)
            name_end = binder.start() + (name_match.end() if name_match else 0)
            line_start, line_end, _line, indent = line_for(binder.start())
            immediate_binders.append(
                {
                    "name_start": name_start,
                    "name_end": name_end,
                    "scope_start": name_end,
                    "scope_end": scope_end_after(line_start, line_end, indent),
                }
            )
    immediate_binders.sort(key=lambda item: item["name_start"])

    delayed_binders: List[Dict[str, Any]] = []
    name = rf"(?P<name>{ident})"
    for binder in re.finditer(rf"\b(?P<kw>have|let)\s+{name}\s*(?::|:=)", source):
        name_start = binder.start("name")
        name_end = binder.end("name")
        line_start, line_end, line, indent = line_for(binder.start())
        local_rhs = line.find(":=", max(0, binder.end() - line_start))
        rhs_start = line_start + local_rhs + 2 if local_rhs >= 0 else None
        delayed_binders.append(
            {
                "name_start": name_start,
                "name_end": name_end,
                "line_start": line_start,
                "line_end": line_end,
                "indent": indent,
                "scope_end": scope_end_after(line_start, line_end, indent),
                "rhs_start": rhs_start,
                "keyword": binder.group("kw"),
            }
        )

    def is_immediate_binder_name(pos: int) -> bool:
        return any(
            binder["name_start"] <= pos < binder["name_end"]
            for binder in immediate_binders
        )

    def has_prior_immediate_binder(pos: int) -> bool:
        return any(
            binder["scope_start"] <= pos < binder["scope_end"]
            for binder in immediate_binders
        )

    def delayed_binder_status(pos: int) -> str:
        for binder in delayed_binders:
            if binder["name_start"] <= pos < binder["name_end"]:
                return "binder-name"
            if pos <= binder["name_start"]:
                continue
            line_start, _line_end, _line, indent = line_for(pos)
            if pos >= int(binder["scope_end"]):
                continue
            if binder["line_start"] <= pos <= binder["line_end"]:
                rhs_start = binder.get("rhs_start")
                if rhs_start is not None and pos >= rhs_start:
                    return "unsafe-rhs"
                return "binder-header"
            if line_start > binder["line_end"]:
                if indent > int(binder["indent"]):
                    return "unsafe-rhs"
                return "available"
        return "none"

    has_local_binding = bool(immediate_binders or delayed_binders)
    if not has_local_binding:
        return False

    for use in uses:
        pos = use.start()
        if is_immediate_binder_name(pos):
            continue
        delayed_status = delayed_binder_status(pos)
        if delayed_status in {"binder-name", "binder-header", "available"}:
            continue
        if delayed_status == "unsafe-rhs":
            return False
        if has_prior_immediate_binder(pos):
            continue
        return False
    return True


def _proof_reuses_rejected_fragments(conv: Any, proof: Optional[str]) -> List[str]:
    if not proof:
        return []
    reused: List[str] = []
    for fragment in _rejected_fragments_from_latest_feedback(conv):
        if fragment and _fragment_reused_in_compact_proof(fragment, proof):
            reused.append(fragment)
    return reused


def _transient_goal_targets_from_latest_feedback(conv: Any) -> List[str]:
    """Mirror of ``_rejected_fragments_from_latest_feedback`` for the
    transient-goal-target channel.

    History-derived (B1-B4 fix, 2026-05-18). Parses the most-recent user message
    iff it is a repair feedback. Ignores any cached ``conv.transient_goal_targets``
    attribute, which previously could go stale across history mutations.
    """

    targets: List[str] = []

    def add_many(values: Sequence[str]) -> None:
        for target in values:
            if target and target not in targets:
                targets.append(target)

    newer_own_payload_seen = False
    for msg in _repair_feedback_messages_in_current_cycle(conv):
        if newer_own_payload_seen and bool(msg.get(_REPAIR_PAYLOAD_CARRIED_KEY)):
            break
        content = str(msg.get("content", "") or "")
        add_many(
            _repair_payload_values_from_message(
                msg,
                _REPAIR_TRANSIENT_GOAL_TARGETS_KEY,
                _transient_goal_targets_from_feedback_text(content),
            )
        )
        if bool(msg.get(_REPAIR_PAYLOAD_RESET_BEFORE_KEY)):
            break
        if _message_has_visible_repair_payload(msg):
            newer_own_payload_seen = True
    return targets


def _proof_repackages_transient_goal_target(
    conv: Any, proof: Optional[str]
) -> List[str]:
    """Detect goal-as-sorry-helper repackaging — the narrow gate.

    Fires only when one of Lean's transient unsolved-goal targets
    appears as the TYPE annotation of a sorry-bodied declaration:

      ``... : <target> := by sorry``
      ``... : <target> := sorry``
      ``have h : <target> := by sorry``
      ``theorem helper_x : <target> := by sorry``

    Whitespace inside the proof is collapsed before matching so
    multi-line declarations are caught. Honest proofs that produce
    the same target through real tactics (``exact ⟨5, ..., rfl⟩``,
    ``refine ⟨_, _, _⟩``, ``constructor; ...``, etc.) do NOT contain
    the ``: <target> := <maybe by> sorry`` shape and are therefore
    unaffected — closing the regression where the previous unified
    gate banned the bare ``∃`` token (or the full existential
    target) from any subsequent proof, making honest existential
    proofs impossible.
    """

    if not proof:
        return []
    targets = list(_transient_goal_targets_from_latest_feedback(conv))
    if not targets:
        return []
    proof_text = _strip_lean_comments_and_strings(str(proof))
    # Collapse whitespace once for whitespace-tolerant matching.
    proof_collapsed = " ".join(proof_text.split())
    matched: List[str] = []
    for target in targets:
        normalized = " ".join(str(target or "").split())
        if not normalized:
            continue
        escaped = re.escape(normalized)
        # ": <target> := [by ]? [exact|refine|apply ]? [(⟨]? stub [)⟩]?"
        # — captures the sorry/admit-helper repackaging shape, including the
        # one-character bypasses agents flagged in round 4 (``(sorry)``
        # and ``⟨sorry⟩``) and the small-token bypasses
        # (``refine sorry`` / ``apply sorry``).
        wrapper_prefix = r"(?:(?:by\s+)?(?:exact|refine|apply)\s+[\(⟨{]*\s*)"
        opener = r"[\(⟨{]*\s*"
        closer = r"(?:\s*[\)⟩}]){0,8}"
        stub_atom = rf"{opener}(?:sorry|admit)\b(?:\s*:\s*{escaped})?{closer}"
        pattern = (
            rf":\s*{escaped}\s*:=\s*"
            rf"(?:"
            rf"(?:by\s+)?{opener}(?:{wrapper_prefix}){{0,8}}{stub_atom}"
            rf"|(?:by\s+)?(?:{wrapper_prefix}){{0,8}}"
            rf"show\s+{escaped}\s+from\s+{stub_atom}"
            rf"|(?:by\s+)?(?:{wrapper_prefix}){{0,8}}"
            rf"by\s+show\s+{escaped}\s+from\s+{stub_atom}"
            rf"|(?:by\s+)?(?:{wrapper_prefix}){{0,8}}"
            rf"show\s+{escaped}\s+from\s+by\s+{stub_atom}"
            rf"|(?:by\s+)?(?:{wrapper_prefix}){{0,8}}"
            rf"by\s+{stub_atom}"
            rf"|by\s+(?:skip\s*;\s*)+(?:sorry|admit)\b"
            rf"|by\s*\{{\s*(?:sorry|admit)\s*\}}"
            rf")"
        )
        if re.search(pattern, proof_collapsed):
            matched.append(target)
    return matched


def _record_repair_policy_attempt(
    dossier: Any,
    *,
    phase: str,
    turn_index: int,
    proof: str = "",
    reason: str,
    metadata: Optional[Dict[str, Any]] = None,
    node_id: Optional[str] = None,
    swallow: bool = True,
) -> None:
    if dossier is None or not hasattr(dossier, "record_attempt"):
        return
    metadata_payload = dict(metadata or {})
    verdict = (
        "proof_policy_repair_redirect"
        if bool(metadata_payload.get("policy_repair_redirect"))
        else "proof_policy_rejected"
    )
    try:
        dossier.record_attempt(
            phase=phase,
            turn_index=turn_index,
            proof=proof or "",
            verdict=verdict,
            error_type=reason,
            metadata=metadata_payload,
            node_id=node_id,
        )
    except Exception:
        if swallow:
            return
        raise


def _format_reused_fragment_feedback(
    reused: Sequence[str],
    banned: Optional[Sequence[str]] = None,
) -> str:
    def render_fragment(fragment: Any) -> str:
        return _prompt_safe_inline_text(
            str(fragment or ""),
            limit=_REJECTED_FRAGMENT_DISPLAY_LIMIT,
        )

    rendered = ", ".join(
        f"`{render_fragment(fragment)}`"
        for fragment in reused
    )
    banned_items = list(banned or reused)
    lines = [
        _REPAIR_SELF_CHECK_MARKER,
        "The repair is still too close to the rejected Lean code: the next "
        f"proof repeats these fragment(s) unchanged: {rendered}.",
        "",
        _REJECTED_FRAGMENT_HEADER,
    ]
    for fragment in banned_items:
        lines.append(f"- `{render_fragment(fragment)}`")
    lines.extend([
        "",
        "Make a local patch: change the failing subterm, tactic argument, "
        "rewrite set, or lemma application so the exact rejected expression "
        "no longer appears unchanged. Reuse the surrounding proof scaffold, "
        "introductions, case splits, helper organization, and checked steps "
        "when they still fit the goal. Then call `try_lean` on the revised "
        "proof before submitting it.",
    ])
    return "\n".join(lines)


def _bank_helpers_as_proposed(
    dossier: Any,
    helpers: Optional[Sequence[str]],
    *,
    phase: str,
    turn_index: int,
    fallback_helpers: Optional[Sequence[str]] = None,
    goal_statement: str = "",
    theorem_name: str = "",
    allow_helper_decomposition: bool = True,
) -> List[str]:
    """Bank an iterable of LLM-emitted helper sources as
    ``proposed_helpers`` on the dossier.

    Used at every ``run_conversation`` rejection site so the prover's
    decomposition signal (helper-DAG declarations) survives the
    rejection and reaches the recursive planner. Best-effort:
    individual record-rejections are silently skipped; banking is
    never allowed to break the calling rejection flow.

    Returns the list of helper names actually banked.
    """

    if not allow_helper_decomposition:
        return []
    if dossier is None:
        return []
    sources: List[str] = []
    for src in helpers or ():
        if isinstance(src, str) and src.strip():
            sources.append(src)
    if not sources:
        for src in fallback_helpers or ():
            if isinstance(src, str) and src.strip():
                sources.append(src)
    if not sources:
        return []
    banked: List[str] = []
    root_name = str(theorem_name or getattr(dossier, "theorem_name", "") or "").strip()
    root_statement = str(goal_statement or getattr(dossier, "root_statement", "") or "")
    for src in sources:
        name = helper_decl_name(str(src or "")) or ""
        if root_name and name == root_name:
            continue
        if _helper_statement_root_equivalent(
            str(src or ""),
            goal_statement=root_statement,
        ):
            continue
        try:
            proposed = dossier.record_proposed_helper(
                src,
                phase=str(phase or ""),
                turn_index=int(turn_index or 0),
            )
        except Exception:
            continue
        if proposed is not None:
            banked.append(proposed.name)
    return banked


def _format_repackaged_goal_target_feedback(
    repackaged_targets: Sequence[str],
    banned_targets: Optional[Sequence[str]] = None,
) -> str:
    """Feedback for the narrow goal-as-sorry-helper repackaging gate.

    Adversarial-review 2026-05-13: previously the narrow-gate hits
    were merged into the ``reused_rejected_fragments`` list and routed
    through ``_format_reused_fragment_feedback``. That formatter wrote
    the goal-target string under ``_REJECTED_FRAGMENT_HEADER``, which
    ``Conversation.append_user`` then parsed back into
    ``rejected_code_fragments`` on the next turn — re-poisoning the
    strict identifier-bounded gate and re-creating the regression
    Fix A was designed to close, just one turn later.

    The dedicated formatter below writes the repackaged targets under
    ``_TRANSIENT_GOAL_TARGET_HEADER`` instead, so the next turn's
    re-parse routes them to ``transient_goal_targets`` (consumed only
    by the narrow gate), never to ``rejected_code_fragments``.
    """
    rendered = ", ".join(
        f"`{_prompt_safe_lean_diagnostic_text(target, limit=240)}`"
        for target in repackaged_targets
    )
    items = list(banned_targets or repackaged_targets)
    lines = [
        _REPAIR_SELF_CHECK_MARKER,
        "You repackaged Lean's still-open goal target(s) as sorry-bodied "
        "helpers — that is the same failure re-dressed, not a repair: "
        f"{rendered}.",
        "",
        _TRANSIENT_GOAL_TARGET_HEADER,
    ]
    lines.extend(
        f"- `{_prompt_safe_lean_diagnostic_text(target, limit=240)}`"
        for target in items
    )
    lines.extend([
        "",
        "Fix the specific proof step that left the goal open, or "
        "replace the proof route with one that makes real progress. Do "
        "not wrap the same open obligation as `have h : <target> := by "
        "sorry`/`:= sorry`.",
    ])
    return "\n".join(lines)


def _normalized_repair_code(value: Any) -> str:
    text = str(value or "").strip()
    blocks = extract_code_fences(text)
    if blocks:
        text = blocks[0].strip()
    text = _strip_lean_comments(text)
    try:
        text = _strip_redundant_preamble_commands(text)
        example_body = _extract_example_body(text)
        if example_body is not None:
            text = example_body
        else:
            decl_body = _extract_single_decl_body(text)
            if decl_body is not None and _is_plausible_main_proof(decl_body):
                text = decl_body
    except Exception:
        pass
    compact = " ".join(text.split())
    compact = re.sub(r"\s*(:=|=>|←|↦)\s*", r"\1", compact)
    compact = re.sub(r"\s*([()\[\]{},:;])\s*", r"\1", compact)
    return compact


def _repair_self_check_matches_submission(
    checked_codes: Sequence[str],
    submitted: Optional[str],
    accepted_registry: Optional[Sequence[Any]] = None,
    *,
    goal_statement: str = "",
    preamble: str = "",
    context_lemmas: Sequence[str] = (),
    exact_only: bool = False,
) -> bool:
    submitted_norm = _normalized_repair_code(submitted)
    if not submitted_norm:
        return False
    registry_codes: List[str] = []
    expected_goal_hash = text_hash(goal_statement) if goal_statement else ""
    expected_preamble_hash = text_hash(preamble) if preamble else ""
    expected_context_hash = text_hash(
        "\n".join(str(item or "") for item in list(context_lemmas or ()))
    )
    for item in list(accepted_registry or ()):
        if isinstance(item, dict):
            item_goal_hash = str(item.get("goal_hash") or "")
            item_preamble_hash = str(item.get("preamble_hash") or "")
            item_context_hash = str(item.get("context_hash") or "")
            if (
                not expected_goal_hash
                or not expected_preamble_hash
                or not item_goal_hash
                or not item_preamble_hash
                or not item_context_hash
            ):
                continue
            if item_goal_hash != expected_goal_hash:
                continue
            if item_preamble_hash != expected_preamble_hash:
                continue
            if item_context_hash != expected_context_hash:
                continue
            registry_codes.append(str(item.get("normalized_code") or ""))
        else:
            item_goal_hash = str(getattr(item, "goal_hash", "") or "")
            item_preamble_hash = str(getattr(item, "preamble_hash", "") or "")
            item_context_hash = str(getattr(item, "context_hash", "") or "")
            if (
                not expected_goal_hash
                or not expected_preamble_hash
                or not item_goal_hash
                or not item_preamble_hash
                or not item_context_hash
            ):
                continue
            if item_goal_hash != expected_goal_hash:
                continue
            if item_preamble_hash != expected_preamble_hash:
                continue
            if item_context_hash != expected_context_hash:
                continue
            registry_codes.append(str(getattr(item, "normalized_code", "") or ""))
    for code in [*list(checked_codes or ()), *registry_codes]:
        checked_norm = _normalized_repair_code(code)
        if not checked_norm:
            continue
        if exact_only:
            # Durable cross-turn evidence demands the EXACT normalized proof
            # body (Sol audit 2026-07-29 F4): local-fragment containment is
            # only valid for current-turn diagnostic probes, where the model
            # demonstrably ran the verifier this turn. An old accepted
            # fragment embedded inside a newly written proof is not evidence
            # that the new proof was checked.
            if checked_norm == submitted_norm:
                return True
            continue
        if _repair_checked_code_covers_submission(
            checked_norm,
            submitted_norm,
        ):
            return True
    return False


def _repair_self_check_has_accepted_evidence(
    checked_codes: Sequence[str],
    accepted_registry: Optional[Sequence[Any]] = None,
    *,
    goal_statement: str = "",
    preamble: str = "",
    context_lemmas: Sequence[str] = (),
) -> bool:
    """Whether the current repair turn has any accepted proof stub to compare.

    A failed ``try_lean`` attempt is useful repair evidence, but it is not an
    accepted self-check. The mismatch gate is intentionally scoped to accepted
    code returned by this turn's tool loop; durable dossier registries can
    contain accepted stubs from prior turns or sibling attempts and must not
    turn a current failed self-check into a policy rejection.
    """

    _ = (accepted_registry, goal_statement, preamble, context_lemmas)
    return any(_normalized_repair_code(code) for code in list(checked_codes or ()))


def _repair_self_check_durable_submission_evidence(
    content: Any,
    *,
    dossier: Any,
    goal_statement: str,
    preamble: str,
    context_lemmas: Sequence[str] = (),
    theorem_name: str = "",
) -> bool:
    """Whether a zero-call repair submission matches durable accepted evidence.

    A model that verified its exact proof body with an accepted ``try_lean``
    on an earlier turn and re-submits it UNCHANGED has satisfied the
    behavioral self-check: the accepted stub in the dossier registry is keyed
    by normalized proof body + goal + preamble + context-helper identity, so
    any drift in what would actually be compiled invalidates the match. This
    grants no proof authority — the authoritative final Lean check still
    decides the candidate. Natural-language claims of prior verification
    never match (the comparison is on the extracted Lean proof body only).
    """

    registry_fn = getattr(dossier, "accepted_scratch_registry", None)
    if not callable(registry_fn):
        return False
    try:
        registry = list(registry_fn() or ())
    except Exception:
        return False
    if not registry:
        return False
    try:
        from .mini_lean_extract import _extract_helpers_and_main

        _helpers, proof = _extract_helpers_and_main(
            str(content or ""),
            theorem_name=str(theorem_name or ""),
            goal_statement=str(goal_statement or ""),
        )
    except Exception:
        return False
    if not proof:
        return False
    return _repair_self_check_matches_submission(
        (),
        proof,
        registry,
        goal_statement=str(goal_statement or ""),
        preamble=str(preamble or ""),
        context_lemmas=context_lemmas,
        exact_only=True,
    )


_LOCAL_REPAIR_FRAGMENT_PREFIX_RE = re.compile(
    r"^(?:have|let|suffices|obtain|rcases|cases|constructor|left|right|use)\b"
)
_COMPLETE_REPAIR_PROOF_PREFIX_RE = re.compile(
    r"^(?:by|exact|refine|show|calc|fun)\b"
)


def _repair_checked_code_is_local_fragment(checked_norm: str) -> bool:
    """Whether accepted repair evidence is a local proof fragment.

    Complete `by`/`exact` proof bodies still need exact normalized equality.
    Containment is only for local pieces that naturally live inside a larger
    submitted proof body.
    """

    text = str(checked_norm or "").strip()
    if not text:
        return False
    if _COMPLETE_REPAIR_PROOF_PREFIX_RE.match(text):
        return False
    if _LOCAL_REPAIR_FRAGMENT_PREFIX_RE.match(text):
        return True
    return ":=by" in text


def _repair_checked_code_covers_submission(
    checked_norm: str,
    submitted_norm: str,
) -> bool:
    if checked_norm == submitted_norm:
        return True
    # Accepted local fragments are legitimate repair evidence: the final
    # submission is still Lean-checked below, so the self-check policy should
    # not reject a proof merely because the model tested the failing `have` or
    # local tactic instead of byte-replaying the entire proof body.
    shorter = min(len(checked_norm), len(submitted_norm))
    if shorter < 16:
        return False
    if (
        _repair_checked_code_is_local_fragment(checked_norm)
        and checked_norm in submitted_norm
    ):
        return True
    return False


def _repair_norm_has_executable_tail(
    checked_norm: str,
    submitted_norm: str,
) -> bool:
    """Whether a final proof appends executable text after a closed proof body."""

    checked = str(checked_norm or "").strip()
    submitted = str(submitted_norm or "").strip()
    if not checked or not submitted or checked == submitted:
        return False
    if not submitted.startswith(checked):
        return False
    tail = submitted[len(checked):]
    if not tail:
        return False
    next_char = tail[:1]
    # Require a syntactic boundary so `h` does not match `h.symm` or `hello`.
    if next_char and (
        next_char.isalnum()
        or next_char == "_"
        or next_char == "."
        or next_char == "'"
    ):
        return False
    return bool(tail.strip(" \t\r\n;,.()[]{}"))


def _repair_self_check_has_terminal_continuation(
    checked_codes: Sequence[str],
    submitted: Optional[str],
) -> bool:
    """Detect final proofs that continue after an accepted complete proof body.

    A complete `by`/`exact`/`refine` scratch proof that Lean accepted has
    already closed the goal in its checked context. If the submitted proof is
    that proof plus extra executable tactics, Lean commonly reports the noisy
    downstream symptom `No goals to be solved`. This gate records the root
    invariant instead: the exact final proof body must be checked, not a closed
    prefix with an executable tail.
    """

    submitted_norm = _normalized_repair_code(submitted)
    if not submitted_norm:
        return False
    for code in list(checked_codes or ()):
        checked_norm = _normalized_repair_code(code)
        if not checked_norm or checked_norm == submitted_norm:
            continue
        if _repair_checked_code_is_local_fragment(checked_norm):
            continue
        if not _COMPLETE_REPAIR_PROOF_PREFIX_RE.match(checked_norm):
            continue
        if _repair_norm_has_executable_tail(checked_norm, submitted_norm):
            return True
    return False


def _format_self_check_mismatch_feedback() -> str:
    return (
        f"{_REPAIR_SELF_CHECK_MARKER}\n"
        "You used a Lean checking tool, but the final submitted proof does "
        "not match the proof body that was accepted by `try_lean`. Call "
        "`try_lean` on the actual revised proof you intend to submit, then "
        "submit that checked proof."
    )


def _format_self_check_terminal_continuation_feedback() -> str:
    return (
        f"{_REPAIR_SELF_CHECK_MARKER}\n"
        "The proof body accepted by `try_lean` already closed the goal, but "
        "the final submitted proof appended additional executable tactics "
        "after that closed proof. Re-run `try_lean` on the exact final proof "
        "you intend to submit, or submit the accepted proof body without the "
        "extra tail."
    )
