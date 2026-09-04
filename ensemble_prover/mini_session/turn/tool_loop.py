"""Run the bounded provider/tool loop for one conversation turn.

Each advertised tool call receives a matching tool response, including typed
errors; tool and provider budgets apply across continuations and mid-batch
drops. The loop supports provider-aware no-tool finalization and returns a typed
result instead of mutating proof acceptance state.
"""

from __future__ import annotations

import asyncio
import copy
import hashlib
import inspect
import json
import math
import re
import threading
import time
from dataclasses import dataclass, field
from typing import Any, Callable, List, Mapping, Optional, Sequence

from ...llm_deadline import llm_retry_deadline_record_from_exception
from ...llm_error_policy import classify_llm_exception
from ...llm_usage import (
    ProviderDispatchAttemptLease,
    ProviderDispatchAttemptLimitExceeded,
    call_with_optional_usage_callback,
    metered_or_plain_call,
)
from ...provider_dispatch_continuation import (
    provider_dispatch_resume_target,
)
from ...mini_lean_extract import (
    _find_forbidden_lean_command,
    _has_plausible_lean_proof_head,
    _is_plausible_lean_symbolic_atom,
    _strip_balanced_outer_proof_parentheses,
    _strip_lean_comments,
)
from ...models import (
    normalize_tool_calls,
    provider_defer_record_from_exception,
    response_output_items,
    response_reasoning_items,
    response_reasoning_text,
)
from ...pricing import base_url_matches_provider
from ...runtime_context import (
    RuntimeCapabilityRevokedError,
    mark_runtime_owned_callback,
    require_hard_timeout_capability_active,
)
from ...mini_policy import (
    _REPAIR_DISCOVERY_TOOL_CALL_QUOTA,
    _REPAIR_CONTINUATION,
    _bind_provider_continuation_policy_receipt,
    _conversation_should_redact_solution_refs,
    _final_submission_shape_instruction,
    _merge_repair_self_check_non_verdict_status,
    _provider_chat_reasoning_envelope_is_valid,
    _provider_chat_tool_calls_envelope_is_valid,
    _repair_self_check_non_verdict_is_compliant,
    _responses_output_matches_advertised_tool_calls,
    _user_history_message,
)
from ...proof_dossier import (
    _prompt_safe_inline_text,
    _prompt_safe_natural_language_text,
    canonical_dossier_statement_key,
    prompt_safe_malformed_tool_arguments,
    active_root_target_statement,
    active_root_targets_for_frame,
    active_root_disproof_certificate_is_valid,
    helper_decl_name,
)
from ...provider_tool_protocol import (
    DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC,
    DEEPSEEK_FINAL_RAW_NO_TOOLS_METRIC,
    DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
    MINI_TOOL_REASONING_EFFORT,
    MiniRequestEnvelopePolicy,
    extract_simple_xml_tool_calls,
    handle_deepseek_dsml_after_budget,
    is_deepseek_client,
    mini_bounded_visible_output_reasoning_effort,
    mini_model_output_capacity,
    mini_visible_output_reasoning_effort,
    resolve_mini_request_envelopes,
    resolve_final_no_tools_output,
    should_use_raw_final_no_tools,
    toolless_final_messages,
)
from ...utils import (
    canonical_lean_identifier,
    display_line_count,
    format_exception,
    parse_tool_arguments,
)
from ...deadline_guard import detach_task_from_loop_shutdown
from ..process_watchdog import begin_process_deadline


class SelectedProofIdeaDispatchContextError(RuntimeError):
    """A selected lifecycle anchor changed before provider dispatch."""

    mini_selected_proof_idea_context_error = True


def _openrouter_exact_continuation_message(
    *,
    client: Any,
    response_data: Any,
    calls_to_run: Sequence[Mapping[str, Any]],
) -> Optional[dict[str, Any]]:
    """Return an exact provider-authored tool turn when it is replayable.

    Structured OpenRouter reasoning is signed for the complete assistant
    message. It is only reusable when every provider call is well formed,
    uniquely identified, and will be executed in the original order.
    """

    cfg = getattr(client, "cfg", None)
    if not base_url_matches_provider(
        str(getattr(cfg, "base_url", "") or ""),
        "openrouter",
    ):
        return None
    if not isinstance(response_data, dict):
        return None
    choices = response_data.get("choices")
    if not isinstance(choices, list) or not choices:
        return None
    first = choices[0]
    raw_message = first.get("message") if isinstance(first, dict) else None
    if not isinstance(raw_message, dict):
        return None
    if str(raw_message.get("role") or "") != "assistant":
        return None
    if not _provider_chat_reasoning_envelope_is_valid(raw_message):
        return None
    raw_calls = raw_message.get("tool_calls")
    if not _provider_chat_tool_calls_envelope_is_valid(raw_message):
        return None
    assert isinstance(raw_calls, list)
    normalized_raw_calls = normalize_tool_calls(raw_calls)
    normalized_run_calls = normalize_tool_calls(list(calls_to_run))
    if (
        len(normalized_raw_calls) != len(raw_calls)
        or normalized_raw_calls != normalized_run_calls
    ):
        return None
    call_ids = [str(call.get("id") or "") for call in normalized_raw_calls]
    if any(not call_id for call_id in call_ids) or len(set(call_ids)) != len(call_ids):
        return None
    try:
        json.dumps(raw_message, ensure_ascii=False, allow_nan=False)
    except (TypeError, ValueError):
        return None
    return {
        key: copy.deepcopy(raw_message[key])
        for key in (
            "role",
            "content",
            "reasoning_content",
            "reasoning",
            "reasoning_details",
            "tool_calls",
        )
        if key in raw_message
    }

_FINALIZER_TACTIC_HEADS = frozenset(
    {
        "aesop",
        "all_goals",
        "any_goals",
        "apply",
        "assumption",
        "by_cases",
        "by_contra",
        "cases",
        "change",
        "clear",
        "exact",
        "constructor",
        "contradiction",
        "conv",
        "decide",
        "field_simp",
        "first",
        "fun_prop",
        "gcongr",
        "have",
        "induction",
        "infer_instance",
        "intro",
        "interval_cases",
        "left",
        "linarith",
        "native_decide",
        "next",
        "norm_num",
        "obtain",
        "omega",
        "positivity",
        "rcases",
        "rfl",
        "repeat",
        "rename_i",
        "revert",
        "right",
        "rintro",
        "ring",
        "rw",
        "simp",
        "simpa",
        "solve",
        "specialize",
        "split",
        "subst",
        "suffices",
        "tauto",
        "trivial",
        "unfold",
        "use",
    }
)

_FINALIZER_LEAN_IDENT_START = r"(?:[^\W\d]|_)"
_FINALIZER_LEAN_IDENT = rf"{_FINALIZER_LEAN_IDENT_START}[\w']*[!?]?"
_FINALIZER_CHATTER_HEADS = frozenset(
    {
        "another",
        "answer",
        "assistant",
        "continue",
        "conclude",
        "done",
        "finished",
        "i",
        "look",
        "maybe",
        "no",
        "none",
        "okay",
        "perhaps",
        "please",
        "proof",
        "retry",
        "search",
        "searching",
        "sure",
        "think",
        "thus",
        "the",
        "theorem",
        "this",
        "unknown",
        "unfortunately",
        "we",
        "yes",
        "you",
        "try",
    }
)
_FINALIZER_CHATTER_WORDS = frozenset(
    {"again", "following", "how", "look", "needed", "please", "result", "search"}
)


def _split_finalizer_lean_atoms(text: str) -> Optional[List[str]]:
    """Split a small Lean term without confusing nested application atoms."""

    pairs = {"(": ")", "[": "]", "{": "}", "«": "»"}
    closing = frozenset(pairs.values())
    stack: List[str] = []
    atoms: List[str] = []
    start: Optional[int] = None
    for index, token in enumerate(text):
        if token.isspace() and not stack:
            if start is not None:
                atoms.append(text[start:index])
                start = None
            continue
        if start is None:
            start = index
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or stack.pop() != token:
                return None
    if stack:
        return None
    if start is not None:
        atoms.append(text[start:])
    return atoms


def _is_structural_finalizer_lean_term(
    text: str, *, _allow_symbolic_expression: bool = False
) -> bool:
    """Recognize bankable term structure without treating prose as a proof."""

    candidate = _strip_lean_comments(str(text or "")).strip()
    if not candidate:
        return False
    if candidate == "()":
        return True
    candidate = _strip_balanced_outer_proof_parentheses(candidate)
    if not candidate:
        return False
    if candidate.startswith("⟨") and candidate.endswith("⟩"):
        return bool(candidate[1:-1].strip())
    lowered = candidate.lower()
    head = lowered.split(None, 1)[0]
    if head == "fun":
        return "=>" in candidate or "↦" in candidate
    if head == "show":
        return bool(re.search(r"\bfrom\b", candidate))
    if head == "calc":
        return ":=" in candidate
    if head == "match":
        return bool(re.search(r"\bwith\b", candidate))
    if head in {"rfl", "trivial"}:
        return candidate == head
    if head == "have":
        return False
    if head == "if":
        words = frozenset(re.findall(r"[A-Za-z]+", lowered))
        return (
            "then" in words
            and "else" in words
            and not words.intersection(_FINALIZER_CHATTER_WORDS)
        )
    if head == "let":
        return ":=" in candidate and (";" in candidate or "\n" in candidate)
    if head == "nomatch":
        return bool(re.fullmatch(r"nomatch\s+\S+", candidate))
    if head == "do":
        body = candidate[2:].strip()
        body_head = body.split(None, 1)[0].lower() if body else ""
        return "←" in body or "<-" in body or body_head in {
            "exact",
            "pure",
            "return",
        }
    if head == "by":
        body = candidate[2:].strip()
        if not body:
            return False
        if body.startswith("·"):
            for line in body.splitlines():
                line_body = line.strip().removeprefix("·").strip()
                if not line_body:
                    continue
                line_atoms = _split_finalizer_lean_atoms(line_body)
                if not line_atoms:
                    return False
                line_head = line_atoms[0].lower().rstrip("!?;")
                if line_head in _FINALIZER_CHATTER_HEADS:
                    return False
            return True
        body_atoms = _split_finalizer_lean_atoms(body)
        if not body_atoms:
            return False
        body_head = body_atoms[0]
        normalized_head = body_head.lower().rstrip("!?;")
        if normalized_head in _FINALIZER_CHATTER_HEADS:
            return False
        return bool(
            re.fullmatch(
                rf"(?:{_FINALIZER_LEAN_IDENT_START}[\w'.]*|«[^»]+»)(?:[!?])?",
                body_head,
            )
        )
    atoms = _split_finalizer_lean_atoms(candidate)
    if not atoms:
        return False
    atom_pattern = re.compile(
        rf"@?{_FINALIZER_LEAN_IDENT}"
        rf"(?:\.(?:{_FINALIZER_LEAN_IDENT}|\d+|\{{[^}}]+\}}))*|"
        r"«[^»]+»|_|\d+"
    )
    operator_pattern = re.compile(
        r"▸|∘|::|\$|\|>|<\||<;>"
    )
    for atom in atoms:
        if atom_pattern.fullmatch(atom) or operator_pattern.fullmatch(atom):
            continue
        if _allow_symbolic_expression and _is_plausible_lean_symbolic_atom(
            atom, atom_pattern
        ):
            continue
        if atom.startswith("(") and atom.endswith(")"):
            inner = atom[1:-1].strip()
            if not (
                _is_structural_finalizer_lean_term(
                    inner, _allow_symbolic_expression=True
                )
                or any(marker in inner for marker in (":", ":=", ","))
            ):
                return False
            continue
        if atom.startswith("{") and atom.endswith("}"):
            if ":=" not in atom and ":" not in atom:
                return False
            continue
        if atom.startswith("[") and atom.endswith("]"):
            continue
        return False
    normalized_head = (
        atoms[0].lstrip("@").split(".", 1)[0].lower().rstrip("!?;")
    )
    return (
        normalized_head not in _FINALIZER_CHATTER_HEADS
        and _has_plausible_lean_proof_head(atoms)
    )


def _bankable_final_proof_content(content: Any) -> bool:
    """Conservative syntax gate for a mixed-response fallback artifact.

    This does not establish proof validity; Lean remains authoritative. It
    merely avoids banking recall-oriented prose while preserving unmistakable
    proof-term shapes if the provider's follow-up finalizer is empty.
    """

    text = str(content or "").strip()
    fenced = re.fullmatch(
        r"```(?:lean\d*|lean)?\s*\n?(.*?)\n?```",
        text,
        flags=re.DOTALL | re.IGNORECASE,
    )
    if fenced is not None:
        text = fenced.group(1).strip()
    declaration = re.fullmatch(
        r"(?:theorem|lemma|example|opaque)\b.*?:=\s*(.+)",
        text,
        flags=re.DOTALL,
    )
    if declaration is not None:
        return _bankable_final_proof_content(declaration.group(1))
    if _find_forbidden_lean_command([], text) is not None:
        return False
    return _is_structural_finalizer_lean_term(text)


def _validate_selected_proof_idea_dispatch_context(
    messages: Sequence[dict],
    dossier: Any,
) -> None:
    """Re-resolve selected cognition after every other context renderer.

    Dossier/global renderers may reconcile graph state. Validation belongs
    after those renderers and directly before transport, otherwise a prompt
    can carry a once-current strategy packet against a newly changed graph.
    """

    if dossier is None:
        return
    resolver = getattr(dossier, "resolve_proof_idea_context", None)
    projector = getattr(dossier, "project_proof_idea_context", None)
    if not callable(resolver) or not callable(projector):
        return
    for message in messages:
        if not isinstance(message, dict):
            continue
        marker = message.get("_required_prompt_context")
        if not isinstance(marker, Mapping) or str(marker.get("kind") or "") != (
            "selected_work"
        ):
            continue
        expected_digest = str(marker.get("context_digest") or "").strip()
        packet = message.get("_selected_proof_idea_packet")
        if not expected_digest and not packet:
            # Execution-only legacy/root selected work has no conserved
            # cognition to revalidate.
            continue
        if not expected_digest or not isinstance(packet, Mapping):
            raise SelectedProofIdeaDispatchContextError(
                "selected proof-idea dispatch receipt is incomplete"
            )
        resolution = resolver(packet, policy="exact_selected")
        status = str(getattr(resolution, "status", "") or "").strip()
        current_digest = str(
            getattr(resolution, "context_digest", "") or ""
        ).strip()
        if status != "resolved" or current_digest != expected_digest:
            reason = str(getattr(resolution, "reason", "") or status or "changed")
            raise SelectedProofIdeaDispatchContextError(
                "selected proof-idea context changed before provider dispatch: "
                f"{status or 'unknown'}: {reason}"
            )
        # Projection performs its own graph/environment freshness and
        # answer-visibility checks. Re-render it adjacent to transport and
        # prove that the exact current atomic unit is what the marked message
        # carries. The resolution digest identifies the strategy lifecycle,
        # not presentation policy, so digest equality alone cannot detect a
        # visibility-policy change or a newly appended observation.
        projection = projector(resolution, audience="conversation")
        render = getattr(projection, "render", None)
        if not callable(render):
            # A real dossier projector returns the typed projection contract.
            # Lightweight adapters may only perform freshness validation.
            continue
        current_context = str(render() or "")
        message_content = str(message.get("content") or "")
        if current_context and current_context not in message_content:
            raise SelectedProofIdeaDispatchContextError(
                "selected proof-idea projection changed before provider "
                "dispatch"
            )


def _callable_accepts_keyword(func: Any, key: str) -> bool:
    try:
        signature = inspect.signature(func)
    except (TypeError, ValueError):
        return True
    parameters = signature.parameters
    if key in parameters:
        return True
    return any(
        parameter.kind is inspect.Parameter.VAR_KEYWORD
        for parameter in parameters.values()
    )


async def _metered_or_plain_call_compat(
    *,
    retryable_exception_no_charge: Optional[Callable[[BaseException], bool]] = None,
    **kwargs: Any,
) -> Any:
    """Call current or pre-no-charge metering shims without hard failing."""

    if retryable_exception_no_charge is not None and _callable_accepts_keyword(
        metered_or_plain_call,
        "retryable_exception_no_charge",
    ):
        kwargs["retryable_exception_no_charge"] = retryable_exception_no_charge
    if (
        "provider_dispatch_lease" in kwargs
        and kwargs.get("provider_dispatch_lease") is not None
        and not _callable_accepts_keyword(
            metered_or_plain_call,
            "provider_dispatch_lease",
        )
    ):
        lease = kwargs.get("provider_dispatch_lease")
        raise ProviderDispatchAttemptLimitExceeded(
            "legacy metering shim cannot enforce the shared provider "
            "dispatch ceiling",
            provider_dispatches_started=_nonnegative_int(
                getattr(lease, "provider_dispatches_started", 0)
            ),
            dispatch_attempt_limit=_nonnegative_int(
                getattr(lease, "max_attempts", 0)
            ),
        )
    if (
        "provider_dispatch_lease" in kwargs
        and kwargs.get("provider_dispatch_lease") is None
        and not _callable_accepts_keyword(
            metered_or_plain_call,
            "provider_dispatch_lease",
        )
    ):
        kwargs.pop("provider_dispatch_lease", None)
    return await metered_or_plain_call(**kwargs)


_INVALID_PROMPT_RE = re.compile(
    r"(?:"
    r"\binvalid[_\s-]?prompt\b"
    r"|potentially\s+violating\s+our\s+usage\s+policy"
    r"|\b(?:visible|target)[-_\s]?answer\b[\s\S]{0,160}\bpolicy\b"
    r"|\bpolicy\b[\s\S]{0,160}\b(?:visible|target)[-_\s]?answer\b"
    r"|\b(?:visible|target)[-_\s]?answer\b[\s\S]{0,160}\bviolat(?:e|es|ing)[-_\s]+(?:the[-_\s]+)?conclusion\b"
    r"|\bviolat(?:e|es|ing)[-_\s]+(?:the[-_\s]+)?conclusion\b[\s\S]{0,160}\b(?:visible|target)[-_\s]?answer\b"
    r")",
    flags=re.IGNORECASE,
)


class _TurnElapsedBudgetExhausted(Exception):
    """Raised internally when a per-turn elapsed budget cancels provider work."""


class _ProviderCumulativeWallExhausted(Exception):
    """Raised when resumed provider quanta exhaust one absolute wall lease."""


class _DetachedSyncWorkerCapacityExhausted(RuntimeError):
    """Raised when every abandonment-safe synchronous worker is occupied."""


_DETACHED_SYNC_WORKER_LIMIT = 8
_DETACHED_SYNC_WORKER_SLOTS = threading.BoundedSemaphore(
    _DETACHED_SYNC_WORKER_LIMIT
)

# Headroom granted to a retrieval searcher on top of the budget it advertises,
# so its own graceful deadline lands before the outer abandonment guard fires.
# A searcher that honours its deadline returns partial results; arming the
# identical value outside it turned those partial results into a lost search.
# This bounds nothing the searcher does -- it only stops the guard from
# stealing the last instant of a budget the searcher is already respecting.
_SEARCH_ABANDONMENT_MARGIN_S = 15.0


async def _run_sync_abandonment_safe(
    call: Callable[[], Any],
    *,
    timeout_s: Optional[float] = None,
) -> Any:
    """Run blocking work without attaching it to the loop's default executor.

    ``asyncio.to_thread`` cannot stop its underlying thread when the awaiting
    task is cancelled, and ``asyncio.run`` subsequently waits for every such
    default-executor thread during loop shutdown.  A timed-out static search
    can therefore turn a bounded Mini turn into an unbounded process-exit
    wait.  These workers are daemon threads, are capped process-wide, and
    publish their result only while the receiving loop/future is still live.

    Python cannot forcibly cancel arbitrary synchronous code.  A permanently
    stuck call occupies one bounded slot, but cannot hold loop or interpreter
    shutdown hostage and cannot create an unbounded number of worker threads.
    """

    if not _DETACHED_SYNC_WORKER_SLOTS.acquire(blocking=False):
        raise _DetachedSyncWorkerCapacityExhausted(
            "abandonment-safe synchronous worker capacity exhausted"
        )

    loop = asyncio.get_running_loop()
    future = loop.create_future()

    def publish_result(ok: bool, value: Any) -> None:
        if future.done():
            return
        if ok:
            future.set_result(value)
        else:
            future.set_exception(value)

    # The worker thread has no context, so the ownership router would adopt
    # the sole active owner (or reject as ambiguous with several) and rewrite
    # this to a no-op once a boundary closes -- leaving the future unresolved
    # and the caller awaiting forever on the ``timeout_s is None`` path. The
    # two sibling daemon bridges are marked and allowlisted for exactly this;
    # this one was not.
    marked_publish_result = mark_runtime_owned_callback(publish_result)

    def worker() -> None:
        try:
            try:
                outcome = (True, call())
            except BaseException as exc:
                outcome = (False, exc)
        finally:
            _DETACHED_SYNC_WORKER_SLOTS.release()
        if loop.is_closed():
            return
        try:
            loop.call_soon_threadsafe(marked_publish_result, *outcome)
        except RuntimeError:
            # The turn may have closed its event loop after abandoning us.
            pass

    thread = threading.Thread(
        target=worker,
        name="mini-prover-detached-sync",
        daemon=True,
    )
    try:
        thread.start()
    except BaseException:
        _DETACHED_SYNC_WORKER_SLOTS.release()
        raise
    if timeout_s is None:
        return await future
    try:
        return await asyncio.wait_for(
            future,
            timeout=max(0.001, float(timeout_s)),
        )
    except asyncio.TimeoutError as exc:
        # The daemon worker may still be unwinding, but it cannot publish into
        # the cancelled future or hold event-loop shutdown hostage.
        raise TimeoutError("synchronous tool operation timed out") from exc


_PROMPT_NEUTRALIZATIONS: tuple[tuple[re.Pattern[str], str], ...] = (
    # Provider prompt-policy filters can occasionally misread Lean/math
    # refutation vocabulary in stale repair transcripts as non-math unsafe
    # intent. These rewrites are used only after an invalid-prompt rejection.
    (re.compile(r"\bproveFalseByLinarith\b"), "linarithContradictionCertificate"),
    (re.compile(r"\bprove[-_\s]?False\b", re.IGNORECASE), "derive contradiction"),
    (re.compile(r"\bderive\s+`?False`?\b", re.IGNORECASE), "derive contradiction"),
    (re.compile(r"\bderiving\s+`?False`?\b", re.IGNORECASE), "deriving contradiction"),
    (re.compile(r"\bfalse\s+polynomial\s+identity\b", re.IGNORECASE), "failed polynomial identity"),
    (re.compile(r"\bclaimed\s+identity\s+is\s+false\b", re.IGNORECASE), "claimed identity fails the check"),
    (re.compile(r"\bproposed\s+(?:decomposition\s+)?identity\s+is\s+false\b", re.IGNORECASE), "proposed identity fails the check"),
    (re.compile(r"\bidentity\s+is\s+false\b", re.IGNORECASE), "identity fails the check"),
    (re.compile(r"\buniversal\s+statement\s+is\s+false\b", re.IGNORECASE), "universal statement fails the check"),
    (re.compile(r"\bstatement\s+as\s+written\s+would\s+be\s+false\b", re.IGNORECASE), "statement as written fails the check"),
    (re.compile(r"\bstatement\s+(?:is|was)\s+false\b", re.IGNORECASE), "statement fails the check"),
    (re.compile(r"\bclaim\s+(?:is|was)\s+false\b", re.IGNORECASE), "claim fails the check"),
    (re.compile(r"\bvisible[-_\s]?answer\s+mode\b", re.IGNORECASE), "reference-visible mode"),
    (re.compile(r"\banswer[-_\s]?visibility\b", re.IGNORECASE), "reference visibility"),
    (re.compile(r"\btarget[-_\s]?answer\s+values?\b", re.IGNORECASE), "reference values"),
    (re.compile(r"\btarget[-_\s]?answer\b", re.IGNORECASE), "reference target"),
    (re.compile(r"\bvisible[-_\s]?answer\b", re.IGNORECASE), "visible reference"),
    (re.compile(r"\bofficial\s+answer\s+targets?\b", re.IGNORECASE), "answer placeholders"),
    (re.compile(r"\bofficial\s+answer\s+values?\b", re.IGNORECASE), "reference values"),
    (re.compile(r"\bofficial\s+answer\b", re.IGNORECASE), "reference answer"),
    (re.compile(r"\bbenchmark\s+answer\s+values?\b", re.IGNORECASE), "reference values"),
    (re.compile(r"\bbenchmark\s+answer\b", re.IGNORECASE), "reference answer"),
    (re.compile(r"\bleaked\b", re.IGNORECASE), "provided"),
    (re.compile(r"\bleaks\b", re.IGNORECASE), "provides"),
    (re.compile(r"\bleak\b", re.IGNORECASE), "provide"),
    (re.compile(r"\bleaking\b", re.IGNORECASE), "providing"),
    (re.compile(r"\bhidden\s+answer\s+values?\b", re.IGNORECASE), "non-visible reference values"),
    (re.compile(r"\bhidden\s+PutnamBench\s+answer\s+values?\b", re.IGNORECASE), "reference values"),
    (re.compile(r"\bhidden\s+lemmas?\b", re.IGNORECASE), "unstated lemmas"),
    (re.compile(r"\bhidden\b", re.IGNORECASE), "non-visible"),
    (re.compile(r"\bviolating[-_\s]+the[-_\s]+conclusion\b", re.IGNORECASE), "contradicting the conclusion"),
    (re.compile(r"\bviolates[-_\s]+the[-_\s]+conclusion\b", re.IGNORECASE), "contradicts the conclusion"),
    (re.compile(r"\bviolate[-_\s]+the[-_\s]+conclusion\b", re.IGNORECASE), "contradict the conclusion"),
    (re.compile(r"\bviolating[-_\s]+conclusion\b", re.IGNORECASE), "contradicting conclusion"),
    (re.compile(r"\bviolates[-_\s]+conclusion\b", re.IGNORECASE), "contradicts conclusion"),
    (re.compile(r"\bviolate[-_\s]+conclusion\b", re.IGNORECASE), "contradict conclusion"),
    (re.compile(r"\bviolating\s+the\s+conclusion\b", re.IGNORECASE), "contradicting the conclusion"),
    (re.compile(r"\bviolates\s+the\s+conclusion\b", re.IGNORECASE), "contradicts the conclusion"),
    (re.compile(r"\bviolate\s+the\s+conclusion\b", re.IGNORECASE), "contradict the conclusion"),
    (re.compile(r"\bviolating\b", re.IGNORECASE), "contradicting"),
    (re.compile(r"\bviolates\b", re.IGNORECASE), "contradicts"),
    (re.compile(r"\bviolate\b", re.IGNORECASE), "contradict"),
)


def _active_root_tool_goal_statement(dossier: Any, conv: Any = None) -> str:
    targets = dossier
    if dossier is not None and conv is not None:
        try:
            helper_blocks = list(dossier.verified_helper_blocks())
        except Exception:
            helper_blocks = []
        targets = active_root_targets_for_frame(
            dossier,
            root_statement=str(getattr(conv, "goal_statement", "") or ""),
            preamble=str(getattr(conv, "preamble", "") or ""),
            helper_blocks=helper_blocks,
            require_helper_context_hash_match=True,
        )
    return active_root_target_statement(
        targets,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )


def _local_decl_names_for_search(dossier: Any, conv: Any) -> List[str]:
    names: List[str] = []

    def add(value: Any) -> None:
        name = str(value or "").strip()
        if name and name not in names:
            names.append(name)

    add(getattr(dossier, "theorem_name", "") if dossier is not None else "")
    add(getattr(conv, "theorem_name", "") if conv is not None else "")
    if dossier is None:
        return names
    for mapping_name in ("verified_helpers", "proposed_helpers"):
        mapping = getattr(dossier, mapping_name, {}) or {}
        if isinstance(mapping, dict):
            for name, helper in mapping.items():
                add(name)
                add(getattr(helper, "name", ""))
                add(helper_decl_name(getattr(helper, "source", "") or ""))
                if isinstance(helper, str):
                    add(helper_decl_name(helper))
    for block in list(getattr(dossier, "helpers", []) or ()):
        add(helper_decl_name(block))
    return names


@dataclass
class ToolLoopResult:
    """Typed bundle returned by ``call_llm_with_tools_one_round``."""

    content: str = ""
    tool_calls_used: int = 0
    tool_call_log: List[dict] = field(default_factory=list)
    llm_error: Optional[str] = None
    llm_failure_kind: str = ""
    llm_retryable: bool = False
    llm_terminal: bool = False
    llm_failure_reason: str = ""
    sent_messages: List[dict] = field(default_factory=list)
    elapsed_s: float = 0.0
    repair_self_check_codes: List[str] = field(default_factory=list)
    repair_self_check_required: bool = False
    repair_self_check_attempted: bool = False
    repair_self_check_accepted: bool = False
    repair_self_check_status: str = ""
    repair_self_check_missing_kind: str = ""
    repair_self_check_budget_exhausted: bool = False
    repair_self_check_helper_only_allowed: bool = False
    repair_discovery_tool_calls_used: int = 0
    repair_verification_tool_calls_used: int = 0
    llm_retry_count: int = 0
    llm_retry_deadline: dict = field(default_factory=dict)
    provider_attempts: List[dict] = field(default_factory=list)
    provider_protocol_event: str = ""
    provider_protocol_original_content: str = ""
    tool_state_updates: int = 0
    tool_state_closures: int = 0
    tool_state_update_statuses: List[str] = field(default_factory=list)
    llm_turn_elapsed_budget_exhausted: bool = False
    llm_turn_elapsed_task_unsettled: bool = False
    llm_turn_elapsed_budget_s: float = 0.0
    request_timeout_override_s: Optional[float] = None
    operation_timeout_override_s: Optional[float] = None
    provider_timeout_lease_partitioned: bool = False
    tool_repeat_detected: bool = False
    tool_repeat_action: str = ""
    tool_repeat_signature: str = ""
    proof_tool_attempts: int = 0
    consecutive_no_formal_progress: int = 0
    consecutive_search_tool_calls: int = 0
    search_cadence_violation_batches: int = 0
    search_cadence_stall_detected: bool = False
    semantic_no_progress_detected: bool = False
    semantic_no_progress_reason: str = ""
    semantic_no_progress_signature: str = ""
    semantic_diagnostic_progress_count: int = 0
    semantic_diagnostic_best_phase: int = -1
    semantic_diagnostic_best_error_kind: str = ""
    semantic_diagnostic_best_goal_count: int = -1
    semantic_diagnostic_last_reason: str = ""
    semantic_diagnostic_best_signature: str = ""
    partial_try_lean_promotions: int = 0
    accepted_try_lean_helper_names: List[str] = field(default_factory=list)
    durable_progress_tool_replay_pending: bool = False
    durable_progress_tool_replay_count: int = 0
    durable_progress_tool_replay_exhausted: bool = False
    durable_progress_tool_replay_predecessor_identity: str = ""
    durable_progress_tool_continuation_identity: str = ""
    durable_progress_tool_continuation_granted: bool = False
    final_no_tools_event: str = ""
    final_no_tools_finish_reason: str = ""
    final_no_tools_reasoning_content_chars: int = 0
    final_no_tools_used_accepted_proof: bool = False
    authoritative_falsification: bool = False
    proof_disproof_conflict: bool = False
    authoritative_falsification_target: str = ""
    authoritative_falsification_certificate_hash: str = ""
    authoritative_falsification_environment_hash: str = ""
    in_turn_tool_history_compactions: int = 0
    in_turn_tool_history_compacted_messages: int = 0
    in_turn_tool_history_compacted_tool_rounds: int = 0
    in_turn_tool_history_compacted_chars: int = 0
    provider_calls_completed: int = 0
    provider_dispatches_started: int = 0
    failed_provider_pre_generation_rejection: bool = False
    provider_call_quantum_exhausted: bool = False
    provider_finalizer_continuation_exhausted: bool = False
    provider_call_elapsed_s: float = 0.0
    provider_call_quantum_max_retries: int = 0
    provider_call_cumulative_elapsed_s: float = 0.0
    provider_call_cumulative_wall_cap_s: float = 0.0
    provider_call_cumulative_wall_exhausted: bool = False
    paid_tool_infrastructure_disposition: str = ""
    paid_tool_continuation_identity: str = ""
    paid_tool_continuation_granted: bool = False
    provider_defer: dict = field(default_factory=dict)
    # A finalizer failure and the proof artifact recovered across it are two
    # independent results. These fields retain the provider-side receipt
    # while ``llm_*`` is cleared so the caller can Lean-check the artifact.
    recovered_finalizer_error: str = ""
    recovered_finalizer_failure_kind: str = ""
    recovered_finalizer_retryable: bool = False
    recovered_finalizer_provider_call_quantum_exhausted: bool = False
    recovered_finalizer_terminal: bool = False
    recovered_finalizer_failure_reason: str = ""
    recovered_finalizer_retry_deadline: dict = field(default_factory=dict)
    recovered_finalizer_provider_attempts: List[dict] = field(default_factory=list)
    recovered_finalizer_provider_defer: dict = field(default_factory=dict)


# Soft policy admits one concrete provider exposure per scheduler quantum.
# Hard policy has a finite operation lease, so it may safely spend one initial
# exposure plus the single transport retry that the 2R lease promises. Later
# logical calls still reacquire the scheduler, and finalizer/repair calls keep
# their stricter single-exposure fence below.
_CONVERSATION_PROVIDER_DISPATCH_QUANTUM = 1
_CONVERSATION_HARD_PROVIDER_DISPATCH_QUANTUM = 2
# Final proof serialization is an exact resumable boundary. Preserve at least
# the OpenAI-compatible transport's historical retry opportunity, but spread
# it across scheduler quanta so one unavailable provider cannot monopolize a
# recursive child. This is a retry bound, not an action/proof-turn budget.
_CONVERSATION_FINALIZER_PROVIDER_QUANTUM_MAX_RETRIES = 8
# A completed slow response followed by tool results is already a
# safe scheduler boundary.  Do not buy a second potentially 1200-second
# logical response in the same action merely because transport retries have a
# separate allowance of two dispatches.
_CONVERSATION_PROVIDER_CALL_QUANTUM = 1
# 0 disables the cumulative cancel/yield knife. Soft LLM policy waits for
# each admitted provider response. Putnam 1978 A2 000415 searched Mathlib
# for 300s, then this default cancelled the next DeepSeek call in-flight
# and the scheduler terminalized the run.
_CONVERSATION_PROVIDER_WALL_QUANTUM_S = 0.0
# A scheduler yield is a fairness boundary, not a fresh wall-clock grant. One
# production-sized quantum is the cumulative lease for every resumed segment
# of the same logical turn; retry count cannot multiply it into hours. The
# floor keeps tiny test/fairness quanta useful without turning them into
# nanosecond hard cancellation deadlines.
_CONVERSATION_PROVIDER_CUMULATIVE_WALL_QUANTA = 1.0
_CONVERSATION_PROVIDER_CUMULATIVE_WALL_FLOOR_S = 30.0
_PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION = 4
_PROVIDER_SETTLEMENT_RESERVE_FRACTION = 0.10
_PROVIDER_SETTLEMENT_RESERVE_MIN_S = 5.0
_PROVIDER_SETTLEMENT_RESERVE_MAX_S = 120.0

_SEARCH_CADENCE_TOOL_NAMES = frozenset({"search_mathlib", "search_theorems"})
# The first rejected batch supplies guidance; the next provider response must
# act on it. Count batches, not calls: a provider has not seen receipts for
# earlier searches within the same response.
_SEARCH_CADENCE_VIOLATION_BATCH_CAP = 2
_FORMAL_CADENCE_TOOL_NAMES = frozenset(
    {
        "apply_decl_to_goal",
        "certify_counterexample",
        "try_lean",
        "try_skeleton",
    }
)


def _nonnegative_finite_float(value: Any, *, default: float = 0.0) -> float:
    """Parse replay timing metadata without trusting serialized state."""

    try:
        parsed = float(value or 0.0)
    except (TypeError, ValueError, OverflowError):
        parsed = float(default)
    if not math.isfinite(parsed) or parsed < 0.0:
        return max(0.0, float(default))
    return parsed


def _turn_elapsed_budget_for_provider_operation_s(
    operation_window_s: Any,
) -> float:
    """Add the outer-turn time that the tool loop reserves for settlement."""

    operation_s = _nonnegative_finite_float(operation_window_s)
    if operation_s <= 0.0:
        return 0.0
    minimum_reserve_boundary_s = (
        _PROVIDER_SETTLEMENT_RESERVE_MIN_S
        / _PROVIDER_SETTLEMENT_RESERVE_FRACTION
    )
    maximum_reserve_boundary_s = (
        _PROVIDER_SETTLEMENT_RESERVE_MAX_S
        / _PROVIDER_SETTLEMENT_RESERVE_FRACTION
    )
    if operation_s <= (
        minimum_reserve_boundary_s - _PROVIDER_SETTLEMENT_RESERVE_MIN_S
    ):
        return operation_s + _PROVIDER_SETTLEMENT_RESERVE_MIN_S
    uncapped_turn_s = operation_s / (
        1.0 - _PROVIDER_SETTLEMENT_RESERVE_FRACTION
    )
    if uncapped_turn_s < maximum_reserve_boundary_s:
        return uncapped_turn_s
    return operation_s + _PROVIDER_SETTLEMENT_RESERVE_MAX_S


def _client_hard_provider_operation_budget_s(client: Any) -> float:
    """Match the client's configured hard operation deadline."""

    cfg = getattr(client, "cfg", None)
    policy = str(
        getattr(cfg, "llm_deadline_policy", "soft") or "soft"
    ).strip().lower()
    if policy != "hard":
        return 0.0
    operation_window_s = _nonnegative_finite_float(
        getattr(cfg, "operation_timeout_s", 0.0)
    )
    if operation_window_s <= 0.0:
        operation_window_s = (
            _nonnegative_finite_float(getattr(cfg, "timeout_s", 0.0))
            * 2.0
        )
    return operation_window_s


def _client_hard_conversation_operation_budget_s(client: Any) -> float:
    """Give a conversation two effective HTTP request windows."""

    cfg = getattr(client, "cfg", None)
    policy = str(
        getattr(cfg, "llm_deadline_policy", "soft") or "soft"
    ).strip().lower()
    if policy != "hard":
        return 0.0
    operation_window_s = _nonnegative_finite_float(
        getattr(cfg, "operation_timeout_s", 0.0)
    )
    if operation_window_s <= 0.0:
        request_window_s = 0.0
        resolve_request_timeout = getattr(
            client,
            "_configured_request_timeout_s",
            None,
        )
        if callable(resolve_request_timeout):
            try:
                request_window_s = _nonnegative_finite_float(
                    resolve_request_timeout()
                )
            except Exception:
                request_window_s = 0.0
        if request_window_s <= 0.0 and not bool(
            getattr(cfg, "request_timeout_disabled", False)
        ):
            request_window_s = _nonnegative_finite_float(
                getattr(cfg, "request_timeout_s", 0.0)
            )
        if request_window_s <= 0.0:
            request_window_s = _nonnegative_finite_float(
                getattr(cfg, "timeout_s", 0.0)
            )
        operation_window_s = request_window_s * 2.0
    return operation_window_s


def _client_hard_turn_elapsed_budget_s(client: Any) -> float:
    """Return a hard turn envelope that preserves the provider operation."""

    return _turn_elapsed_budget_for_provider_operation_s(
        _client_hard_conversation_operation_budget_s(client)
    )


def _nonnegative_int(value: Any, *, default: int = 0) -> int:
    """Parse replay counters without allowing corrupt state to abort a turn."""

    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError, OverflowError):
        return max(0, int(default))


def _bounded_int(
    value: Any,
    *,
    minimum: int,
    maximum: int,
    default: int,
) -> int:
    """Parse untrusted continuation integers within an explicit range."""

    try:
        parsed = int(value)
    except (TypeError, ValueError, OverflowError):
        parsed = int(default)
    return min(int(maximum), max(int(minimum), parsed))


def _exception_nonnegative_int(exc: BaseException, attribute: str) -> int:
    """Read untrusted adapter exception metadata without masking its failure."""

    try:
        value = getattr(exc, attribute, 0)
        return _nonnegative_int(value)
    except BaseException:
        return 0


def _tool_execution_disposition(
    tool_name: str,
    result_text: str,
    *,
    runner_raised: bool = False,
    runner_deferred_before_launch: bool = False,
) -> str:
    """Separate transport/runtime failures from semantic tool receipts."""

    if runner_deferred_before_launch:
        return "infrastructure_deferred_before_launch"
    if runner_raised:
        return "infrastructure_after_launch"
    text = str(result_text or "")
    payload: Mapping[str, Any] = {}
    try:
        decoded = json.loads(text)
        if isinstance(decoded, Mapping):
            payload = decoded
    except Exception:
        pass
    explicit = str(payload.get("execution_disposition") or "").strip()
    if explicit in {
        "infrastructure_deferred_before_launch",
        "infrastructure_after_launch",
        "completed_semantic",
    }:
        return explicit
    error_kind = str(payload.get("error_kind") or "").strip().lower()
    if bool(payload.get("deferred_before_launch")) or error_kind in {
        "lean_admission_deferred",
        "lean_admission_deferred_before_launch",
    }:
        return "infrastructure_deferred_before_launch"
    lowered = text.lower()
    normalized_tool_name = str(tool_name or "").strip().lower()
    infrastructure_prefix = f"{normalized_tool_name} infrastructure error:"
    if normalized_tool_name and lowered.lstrip().startswith(
        infrastructure_prefix
    ):
        if any(
            marker in lowered
            for marker in (
                "_leanadmissiondeferred",
                "lean_admission_deferred_before_launch",
            )
        ):
            return "infrastructure_deferred_before_launch"
        return "infrastructure_after_launch"
    return "completed_semantic"


def _provider_turn_lane_identity(
    conv: Any,
    goal_statement_override: Optional[str] = None,
    *,
    repair_cycle_identity: Optional[str] = None,
    role_override: Optional[str] = None,
) -> str:
    """Bind a resumed provider lease to one exact target/repair cycle.

    ``_provider_turn_repair_cycle_identity`` is supplied by the outer action
    from selected-work and repair-ticket authority.  The target and role are
    included here again so direct callers and target changes cannot inherit a
    stale cumulative lease merely because the outer cycle marker was absent
    or accidentally retained.
    """

    target = str(
        goal_statement_override
        if goal_statement_override is not None
        else getattr(conv, "goal_statement", "")
    ).strip()
    payload = {
        "role": str(
            role_override
            if role_override is not None
            else getattr(conv, "role", "") or ""
        ).strip(),
        "target": target,
        "repair_cycle": str(
            repair_cycle_identity
            if repair_cycle_identity is not None
            else getattr(conv, "_provider_turn_repair_cycle_identity", "") or ""
        ).strip(),
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8", errors="replace")
    return hashlib.sha256(encoded).hexdigest()


def _validated_provider_call_quantum_state(
    conv: Any,
    *,
    goal_statement_override: Optional[str] = None,
    dossier: Any = None,
    preserve_recognized_legacy_v1: bool = False,
    migrate_legacy_repair_v1: bool = False,
    max_tool_calls_per_turn: int = 0,
) -> dict[str, Any]:
    """Return only current-lane state, with one conservative v1 migration.

    Schema v1 predates authenticated lane identity.  During pre-dispatch it
    is ignored without deletion so the main loop can determine whether this
    is actually a repair turn.  A recognized repair continuation retains
    only bounded protocol counters/evidence, starts discovery exhausted, and
    receives a fresh lane-bound wall lease.  Target-bound timing, retirement,
    and tool signatures are never inherited.
    """

    raw_state = getattr(conv, "_provider_call_quantum_state", {}) or {}
    expected_identity = _provider_turn_lane_identity(
        conv,
        goal_statement_override,
    )
    if (
        isinstance(raw_state, Mapping)
        and str(raw_state.get("pending_tool_replay_disposition") or "").strip()
        == "durable_progress_cutpoint"
    ):
        durable_state = _validated_durable_progress_tool_continuation_state(
            raw_state,
            conv=conv,
            dossier=dossier,
            goal_statement_override=goal_statement_override,
            max_tool_calls_per_turn=max_tool_calls_per_turn,
        )
        if durable_state:
            return durable_state
        return {}
    valid = bool(
        isinstance(raw_state, Mapping)
        and _nonnegative_int(raw_state.get("schema_version", 0))
        == _PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION
        and str(raw_state.get("provider_turn_lane_identity") or "").strip()
        == expected_identity
    )
    if valid:
        return dict(raw_state)
    schema_version = (
        _nonnegative_int(raw_state.get("schema_version", 0))
        if isinstance(raw_state, Mapping)
        else 0
    )
    if schema_version == 1 and preserve_recognized_legacy_v1:
        return {}
    if schema_version == 1 and migrate_legacy_repair_v1:
        max_calls = max(0, int(max_tool_calls_per_turn or 0))
        # Reserve the final available slot for a verifier.  Discovery remains
        # exhausted even when a tiny configured budget cannot represent all
        # three historical discovery calls numerically.
        sanitized_tool_calls = min(
            _nonnegative_int(raw_state.get("tool_calls_used", 0)),
            max(0, max_calls - 1),
        )
        discovery_calls = min(
            sanitized_tool_calls,
            _REPAIR_DISCOVERY_TOOL_CALL_QUOTA,
        )
        verification_calls = min(
            max(0, sanitized_tool_calls - discovery_calls),
            _nonnegative_int(
                raw_state.get("repair_verification_tool_calls_used", 0)
            ),
        )
        raw_repair_codes = raw_state.get("repair_self_check_codes", [])
        legacy_repair_codes = (
            list(raw_repair_codes)
            if isinstance(raw_repair_codes, (list, tuple))
            else []
        )
        migrated = {
            "schema_version": _PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION,
            "provider_turn_lane_identity": expected_identity,
            "tool_calls_used": sanitized_tool_calls,
            "max_tool_calls_per_turn": max_calls,
            "seen_tool_call_signatures": [],
            "repair_discovery_tool_calls_used": discovery_calls,
            "repair_verification_tool_calls_used": verification_calls,
            "repair_discovery_quota_exhausted": True,
            "repair_self_check_seen": bool(
                raw_state.get("repair_self_check_seen", False)
            ),
            "repair_self_check_attempted": bool(
                raw_state.get("repair_self_check_attempted", False)
            ),
            "repair_self_check_status": str(
                raw_state.get("repair_self_check_status", "") or ""
            )[:80],
            "repair_self_check_codes": [
                str(code or "")[:20_000]
                for code in legacy_repair_codes[-4:]
                if str(code or "")
            ],
            "deepseek_dsml_reprompted_after_budget": False,
            "final_no_tools_policy_reprompted": False,
            "force_finalize_without_tools": False,
            "final_no_tools_recovery_attempted": False,
            "final_no_tools_visibility_recovery_pending": False,
            "provider_call_cumulative_elapsed_s": 0.0,
            "provider_call_cumulative_wall_cap_s": 0.0,
            "provider_call_cumulative_deadline_monotonic": 0.0,
            "provider_call_cumulative_wall_exhausted": False,
        }
        setattr(conv, "_provider_call_quantum_state", migrated)
        return migrated
    if hasattr(conv, "_provider_call_quantum_state"):
        delattr(conv, "_provider_call_quantum_state")
    return {}


def _tool_loop_process_deadline_monotonic(kwargs: Mapping[str, Any]) -> float:
    """Return the earliest hard turn/provider deadline before dispatch."""

    now = time.monotonic()
    max_turn_elapsed_s = _nonnegative_finite_float(
        kwargs.get("max_turn_elapsed_s", 0.0)
    )
    provider_quantum_s = _nonnegative_finite_float(
        kwargs.get(
            "provider_call_quantum_s",
            _CONVERSATION_PROVIDER_WALL_QUANTUM_S,
        ),
        default=_CONVERSATION_PROVIDER_WALL_QUANTUM_S,
    )
    provider_cap_s = (
        max(
            _CONVERSATION_PROVIDER_CUMULATIVE_WALL_FLOOR_S,
            provider_quantum_s * _CONVERSATION_PROVIDER_CUMULATIVE_WALL_QUANTA,
        )
        if provider_quantum_s > 0.0
        else 0.0
    )
    if max_turn_elapsed_s > 0.0:
        provider_cap_s = (
            min(provider_cap_s, max_turn_elapsed_s)
            if provider_cap_s > 0.0
            else max_turn_elapsed_s
        )

    provider_elapsed_s = 0.0
    stored_deadline = 0.0
    stored_exhausted = False
    conv = kwargs.get("conv")
    raw_state = _validated_provider_call_quantum_state(
        conv,
        goal_statement_override=kwargs.get("goal_statement_override"),
        preserve_recognized_legacy_v1=True,
    )
    if raw_state:
        stored_cap_s = _nonnegative_finite_float(
            raw_state.get("provider_call_cumulative_wall_cap_s", 0.0)
        )
        if stored_cap_s > 0.0:
            provider_cap_s = (
                min(provider_cap_s, stored_cap_s)
                if provider_cap_s > 0.0
                else stored_cap_s
            )
        provider_elapsed_s = _nonnegative_finite_float(
            raw_state.get("provider_call_cumulative_elapsed_s", 0.0)
        )
        stored_deadline = _nonnegative_finite_float(
            raw_state.get("provider_call_cumulative_deadline_monotonic", 0.0)
        )
        stored_exhausted = bool(
            raw_state.get("provider_call_cumulative_wall_exhausted", False)
        )
    if provider_quantum_s <= 0.0:
        stored_exhausted = False
        provider_cap_s = max_turn_elapsed_s if max_turn_elapsed_s > 0.0 else 0.0

    deadlines: list[float] = []
    if max_turn_elapsed_s > 0.0:
        deadlines.append(now + max_turn_elapsed_s)
    client = kwargs.get("client")
    operation_timeout_s = _nonnegative_finite_float(
        getattr(getattr(client, "cfg", None), "operation_timeout_s", 0.0)
    )
    if operation_timeout_s > 0.0:
        deadlines.append(now + operation_timeout_s)
    if provider_cap_s > 0.0 and not stored_exhausted:
        provider_deadline = now + max(0.0, provider_cap_s - provider_elapsed_s)
        if stored_deadline > 0.0:
            provider_deadline = min(provider_deadline, stored_deadline)
        deadlines.append(provider_deadline)
    return min(deadlines) if deadlines else 0.0

# Keep a substantial contiguous mathematical exploration verbatim while
# bounding genuinely long tool transcripts.  A four-round proof search is a
# normal reasoning chain, not compaction pressure; collapsing it erased the
# progression that productive providers use to synthesize the next step.
_IN_TURN_TOOL_HISTORY_KEEP_RECENT_ROUNDS = 8
_IN_TURN_TOOL_HISTORY_COMPACT_AT_ROUNDS = 12
_IN_TURN_TOOL_HISTORY_COMPACT_AT_CHARS = 60_000


def _canonicalize_tool_call_arguments(arguments: Any, *, tool_name: str = "") -> str:
    text = str(arguments or "").strip()
    if not text:
        return "{}"
    try:
        decoded = json.loads(text)
    except Exception:
        return text
    if isinstance(decoded, dict) and tool_name in {"try_lean", "try_skeleton"}:
        decoded = dict(decoded)
        decoded.pop("purpose", None)
    try:
        return json.dumps(
            decoded,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except Exception:
        return text


def _tool_call_signature(tool_call: Mapping[str, Any]) -> str:
    if not isinstance(tool_call, Mapping):
        return ""
    fn = tool_call.get("function") or {}
    if not isinstance(fn, Mapping):
        fn = {}
    name = str(fn.get("name", "") or "").strip()
    if not name:
        return ""
    args = _canonicalize_tool_call_arguments(
        fn.get("arguments", "{}"),
        tool_name=name,
    )
    return f"{name}:{args}"


_DURABLE_PROGRESS_ROOT_TOOL_NAMES = frozenset(
    {
        "apply_decl_to_goal",
        "certify_counterexample",
        "try_lean",
        "try_skeleton",
    }
)


def _durable_progress_tool_continuation_identity(
    *,
    role: str,
    target_statement: str,
    pending_tool_replay: Sequence[Mapping[str, Any]],
    helper_receipts: Sequence[Mapping[str, Any]] = (),
) -> str:
    """Bind deferred closing calls to one exact target and durable evidence."""

    signatures = [
        _tool_call_signature(call)
        for call in pending_tool_replay
        if isinstance(call, Mapping)
    ]
    if not signatures or any(not signature for signature in signatures):
        return ""
    receipts = sorted(
        (
            canonical_lean_identifier(str(receipt.get("name") or "").strip()),
            str(receipt.get("source_hash") or "").strip(),
        )
        for receipt in helper_receipts
        if isinstance(receipt, Mapping)
        and str(receipt.get("name") or "").strip()
        and str(receipt.get("source_hash") or "").strip()
    )
    payload = {
        "schema": 1,
        "role": str(role or "").strip(),
        "target": str(target_statement or "").strip(),
        "pending_tool_signatures": signatures,
        "helper_receipts": receipts,
    }
    return hashlib.sha256(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8", errors="replace")
    ).hexdigest()


def _validated_durable_progress_tool_continuation_state(
    raw_state: Mapping[str, Any],
    *,
    conv: Any,
    dossier: Any,
    goal_statement_override: Optional[str],
    max_tool_calls_per_turn: int,
) -> dict[str, Any]:
    """Validate a closing-call continuation without reusing provider timing state."""

    if (
        _nonnegative_int(raw_state.get("schema_version", 0))
        != _PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION
        or str(raw_state.get("pending_tool_replay_disposition") or "").strip()
        != "durable_progress_cutpoint"
    ):
        return {}
    try:
        max_calls = max(0, int(max_tool_calls_per_turn or 0))
    except Exception:
        return {}
    role = str(raw_state.get("durable_progress_tool_continuation_role") or "").strip()
    target = str(
        raw_state.get("durable_progress_tool_continuation_target") or ""
    ).strip()
    expected_target = str(
        goal_statement_override
        if goal_statement_override is not None
        else getattr(conv, "goal_statement", "")
    ).strip()
    if (
        not role
        or role != str(getattr(conv, "role", "") or "").strip()
        or not target
        or target != expected_target
    ):
        return {}
    used = min(max_calls, _nonnegative_int(raw_state.get("tool_calls_used", 0)))
    replay_capacity = max(0, max_calls - used)
    raw_pending = raw_state.get("pending_tool_replay") or []
    if not isinstance(raw_pending, (list, tuple)):
        return {}
    pending = [dict(call) for call in raw_pending if isinstance(call, Mapping)]
    if (
        not pending
        or len(pending) != len(raw_pending)
        or len(pending) > replay_capacity
        or any(
            str((call.get("function") or {}).get("name") or "").strip()
            not in _DURABLE_PROGRESS_ROOT_TOOL_NAMES
            for call in pending
        )
    ):
        return {}
    raw_receipts = raw_state.get(
        "durable_progress_tool_continuation_helper_receipts"
    ) or []
    if not isinstance(raw_receipts, (list, tuple)):
        return {}
    receipts = [dict(receipt) for receipt in raw_receipts if isinstance(receipt, Mapping)]
    if len(receipts) != len(raw_receipts):
        return {}
    helper_registry = getattr(dossier, "verified_helpers", None)
    resolver = getattr(dossier, "resolve_verified_helper_name", None)
    for receipt in receipts:
        name = str(receipt.get("name") or "").strip()
        source_hash = str(receipt.get("source_hash") or "").strip()
        if not name or not source_hash or not isinstance(helper_registry, Mapping):
            return {}
        resolved = (
            str(resolver(name) or name).strip()
            if callable(resolver)
            else name
        )
        helper = helper_registry.get(resolved)
        if str(getattr(helper, "source_hash", "") or "").strip() != source_hash:
            return {}
    identity = str(
        raw_state.get("durable_progress_tool_continuation_identity") or ""
    ).strip()
    expected_identity = _durable_progress_tool_continuation_identity(
        role=role,
        target_statement=target,
        pending_tool_replay=pending,
        helper_receipts=receipts,
    )
    if not identity or identity != expected_identity:
        return {}
    return {
        "schema_version": _PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION,
        "provider_turn_lane_identity": _provider_turn_lane_identity(
            conv,
            goal_statement_override,
        ),
        "tool_calls_used": used,
        "max_tool_calls_per_turn": max_calls,
        "pending_tool_replay": pending,
        "pending_tool_replay_is_paid_retry": False,
        "pending_tool_replay_disposition": "durable_progress_cutpoint",
        "durable_progress_tool_continuation_identity": identity,
        "durable_progress_tool_continuation_role": role,
        "durable_progress_tool_continuation_target": target,
        "durable_progress_tool_continuation_helper_receipts": receipts,
    }


_PLAIN_EXAMPLE_DECL_RE = re.compile(
    r"^(?P<prefix>\s*(?:noncomputable\s+)?)example\b"
)


def _named_checked_bridge_source(
    code: str,
    *,
    reserved_names: Sequence[str] = (),
) -> tuple[str, str]:
    """Name one already-accepted scratch example for durable helper storage."""

    raw = str(code or "").strip()
    match = _PLAIN_EXAMPLE_DECL_RE.match(raw)
    if match is None:
        return "", ""
    digest = hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:16]
    base_name = f"mini_checked_bridge_{digest}"
    reserved = {
        canonical_lean_identifier(str(item or "").strip())
        for item in reserved_names
        if str(item or "").strip()
    }
    name = base_name
    suffix = 2
    while canonical_lean_identifier(name) in reserved:
        name = f"{base_name}_{suffix}"
        suffix += 1
    source = (
        raw[: match.start()]
        + str(match.group("prefix") or "")
        + f"lemma {name}"
        + raw[match.end() :]
    )
    return name, source


_LEAN_LOCATION_RE = re.compile(
    r"\b(?:line\s+)?\d+\s*(?:,|:)\s*(?:col(?:umn)?\s+)?\d+\b",
    flags=re.IGNORECASE,
)
_LEAN_GENERATED_BINDER_RE = re.compile(r"(?<![\w'])_(?:b|a|h)\d+(?![\w'])")


@dataclass(frozen=True)
class _SemanticLeanDiagnosticState:
    """Evidence-bearing compiler/proof-state snapshot for one tool result.

    The phase is deliberately derived from Lean's canonical error family, not
    source locations or free-form diagnostic prose.  ``goal_count`` is present
    only when the result exposes residual goals.  This lets the governor
    recognize a proof that reaches a strictly later Lean phase, or closes at
    least one residual goal, without treating message/location churn as
    progress.
    """

    phase: int
    error_kind: str
    goal_count: Optional[int]
    signature: str


_LEAN_DIAGNOSTIC_PHASES: dict[str, int] = {
    # Lean cannot elaborate terms until parsing succeeds.
    "parse_error": 0,
    # Name/universe resolution precedes typed term elaboration.
    "unknown_identifier": 1,
    "unknown_universe": 1,
    # These families establish that Lean reached typed elaboration.
    "type_mismatch": 2,
    "missing_instance": 2,
    "binder_mismatch": 2,
    "binder_arity_mismatch": 2,
    "unification_failed": 2,
    # These establish that an elaborated tactic/program actually ran.
    "tactic_failed": 3,
    "simp_no_progress": 3,
    "timeout": 3,
    "termination_failed": 3,
    "proposition_falsified": 3,
    # An explicit residual proof state is the strongest rejected result: the
    # candidate elaborated and executed, leaving concrete obligations.
    "unsolved_goals": 4,
}


def _normalized_lean_error_kind(value: Any) -> str:
    compact = str(value or "").strip().lower().replace("-", "_")
    compact = re.sub(r"\s+", "_", compact)
    aliases = {
        "unknown_constant": "unknown_identifier",
        "unknown_declaration": "unknown_identifier",
        "application_type_mismatch": "type_mismatch",
        "unification_failure": "unification_failed",
        "unsolved_goal": "unsolved_goals",
        "deterministic_timeout": "timeout",
    }
    return aliases.get(compact, compact)


def _semantic_lean_diagnostic_state(
    tool_name: str,
    result_text: str,
) -> Optional[_SemanticLeanDiagnosticState]:
    """Extract only monotone, formal evidence useful for progress accounting."""

    name = str(tool_name or "").strip()
    if name not in {"try_lean", "try_skeleton", "apply_decl_to_goal"}:
        return None
    text = str(result_text or "").strip()
    if not text:
        return None

    error_kind = ""
    goal_count: Optional[int] = None
    try:
        payload = json.loads(text)
    except Exception:
        payload = None
    if isinstance(payload, Mapping):
        error_kind = _normalized_lean_error_kind(
            payload.get("error_kind") or payload.get("reason")
        )
        update = payload.get("proof_state_update")
        update_record = dict(update) if isinstance(update, Mapping) else {}
        if "residual_goal_count" in update_record:
            try:
                goal_count = max(
                    0,
                    int(update_record.get("residual_goal_count", 0) or 0),
                )
            except (TypeError, ValueError):
                goal_count = None
        if goal_count is None and isinstance(payload.get("remaining_goals"), list):
            remaining = list(payload.get("remaining_goals") or ())
            if remaining:
                goal_count = len(remaining)
        if goal_count is None and isinstance(payload.get("obligations"), list):
            obligations = list(payload.get("obligations") or ())
            if obligations:
                goal_count = len(obligations)
    elif name == "try_lean" and text.startswith("try_lean rejected."):
        error_match = re.search(
            r"scratch proof \(([^)]+)\)",
            text,
            flags=re.IGNORECASE,
        )
        error_kind = _normalized_lean_error_kind(
            error_match.group(1) if error_match is not None else ""
        )
        goals_match = re.search(
            r"\bRemaining goals:\s*(.*)$",
            text,
            flags=re.IGNORECASE | re.DOTALL,
        )
        if goals_match is not None:
            rendered_goals = str(goals_match.group(1) or "").strip()
            if rendered_goals:
                # try_lean renders at most two goals separated by a padded
                # vertical bar.  A decrease from two-or-more to one is still
                # strict evidence even when the earlier output was truncated.
                goal_count = len(re.split(r"\s+\|\s+", rendered_goals))

    phase = _LEAN_DIAGNOSTIC_PHASES.get(error_kind)
    if phase is None:
        return None
    return _SemanticLeanDiagnosticState(
        phase=phase,
        error_kind=error_kind,
        goal_count=goal_count,
        signature=_semantic_proof_tool_result_signature(name, text),
    )


def _semantic_diagnostic_improvement(
    previous_best: Optional[_SemanticLeanDiagnosticState],
    current: Optional[_SemanticLeanDiagnosticState],
) -> str:
    """Describe a strict, globally monotone diagnostic improvement.

    Comparing against the best state seen (rather than merely the immediately
    preceding state) prevents A→B→A→B diagnostic cycles from repeatedly
    resetting the no-progress counter.
    """

    if previous_best is None or current is None:
        return ""
    if current.phase > previous_best.phase:
        return "lean_phase_advanced"
    if (
        current.phase == previous_best.phase == _LEAN_DIAGNOSTIC_PHASES["unsolved_goals"]
        and current.goal_count is not None
        and previous_best.goal_count is not None
        and current.goal_count < previous_best.goal_count
    ):
        return "residual_goal_count_decreased"
    return ""


def _semantic_proof_tool_result_signature(
    tool_name: str,
    result_text: str,
    *,
    candidate_identity: str = "",
) -> str:
    """Return a conservative semantic signature for a formal-tool outcome.

    Exact tool arguments are a poor stagnation key: an LLM can make dozens of
    whitespace/name variants of one rejected proof.  Lean's canonical error
    class and residual goals are substantially more stable.  We intentionally
    normalize only source locations, generated binder suffixes, and whitespace;
    distinct constants and goal expressions remain distinct, so this cannot
    merge unrelated mathematical states.
    """

    name = str(tool_name or "").strip()
    if name not in {"try_lean", "try_skeleton", "apply_decl_to_goal"}:
        return ""
    text = str(result_text or "").strip()
    if not text:
        return ""
    # Skeleton/apply results are structured.  Keep their status/reason and any
    # residual count/node-free target description, but exclude fresh node ids.
    try:
        payload = json.loads(text)
    except Exception:
        payload = None
    if isinstance(payload, Mapping):
        update = payload.get("proof_state_update")
        update_record = dict(update) if isinstance(update, Mapping) else {}

        def semantic_text(value: Any) -> str:
            compact = _LEAN_LOCATION_RE.sub("<loc>", str(value or ""))
            compact = _LEAN_GENERATED_BINDER_RE.sub("_g", compact)
            return re.sub(r"\s+", " ", compact).strip()

        remaining_goals = payload.get("remaining_goals")
        if not isinstance(remaining_goals, list):
            remaining_goals = []
        obligations = payload.get("obligations")
        if not isinstance(obligations, list):
            obligations = []
        try:
            residual_goal_count = max(
                0,
                int(update_record.get("residual_goal_count", 0) or 0),
            )
        except (TypeError, ValueError, OverflowError):
            # Semantic novelty is an optimization boundary, never a reason
            # to crash an otherwise well-formed tool transcript. Keep the
            # malformed value out of the identity and let the ordinary tool
            # result remain visible to the model.
            residual_goal_count = 0
        semantic = {
            "tool": name,
            "status": str(payload.get("status") or ""),
            "reason": str(payload.get("reason") or ""),
            "summary": semantic_text(payload.get("summary")),
            # Declaration applications can all have empty status/reason.
            # Retain their actual mathematical route and Lean diagnostic so
            # distinct lemmas are not collapsed into one repeated state.
            "statement": semantic_text(payload.get("statement")),
            "decl_name": semantic_text(payload.get("decl_name")),
            "decl_type": semantic_text(payload.get("decl_type")),
            "applicable": payload.get("applicable"),
            "error_kind": semantic_text(payload.get("error_kind")),
            "error": semantic_text(
                payload.get("error") or payload.get("diagnostics")
            ),
            "remaining_goals": [
                semantic_text(goal) for goal in remaining_goals[:8]
            ],
            "obligation_targets": [
                semantic_text(item.get("target"))
                for item in obligations[:8]
                if isinstance(item, Mapping)
            ],
            "update_status": str(update_record.get("status") or ""),
            "residual_goal_count": residual_goal_count,
        }
        normalized = json.dumps(semantic, sort_keys=True, ensure_ascii=False)
    else:
        normalized_source = text
        if name == "try_lean" and text.startswith("try_lean rejected."):
            error_match = re.search(
                r"scratch proof \(([^)]+)\)",
                text,
                flags=re.IGNORECASE,
            )
            goals_match = re.search(
                r"\bRemaining goals:\s*(.*)$",
                text,
                flags=re.IGNORECASE | re.DOTALL,
            )
            diagnostics_match = re.search(
                r"\bDiagnostics:\s*(.*?)(?:\bRemaining goals:|$)",
                text,
                flags=re.IGNORECASE | re.DOTALL,
            )
            # Purpose prose and the named-helper count do not describe Lean's
            # state and commonly change across cosmetic proof variants.
            normalized_source = json.dumps(
                {
                    "status": "rejected",
                    "error": (
                        str(error_match.group(1)).strip()
                        if error_match is not None
                        else "lean_rejected"
                    ),
                    "remaining_goals": (
                        str(goals_match.group(1)).strip()
                        if goals_match is not None
                        else ""
                    ),
                    "diagnostics": (
                        str(diagnostics_match.group(1)).strip()
                        if diagnostics_match is not None
                        else ""
                    ),
                },
                sort_keys=True,
                ensure_ascii=False,
            )
        normalized = _LEAN_LOCATION_RE.sub("<loc>", normalized_source)
        normalized = _LEAN_GENERATED_BINDER_RE.sub("_g", normalized)
        normalized = re.sub(r"\s+", " ", normalized).strip()
    if not normalized:
        return ""
    candidate = str(candidate_identity or "").strip()
    if candidate:
        comment_free_candidate = _strip_lean_comments(candidate)
        candidate_tokens = re.findall(
            r'"(?:\\.|[^"\\])*"|[A-Za-z0-9_\'.]+|[^\s]',
            comment_free_candidate,
            flags=re.DOTALL,
        )
        canonical_candidate = "\x1f".join(candidate_tokens)
        candidate_hash = hashlib.sha256(
            canonical_candidate.encode("utf-8")
        ).hexdigest()[:16]
    else:
        candidate_hash = ""
    return hashlib.sha256(
        f"{name}\n{candidate_hash}\n{normalized}".encode("utf-8")
    ).hexdigest()[:16]


def _is_invalid_prompt_error(exc: BaseException) -> bool:
    return bool(_INVALID_PROMPT_RE.search(format_exception(exc)))


def _sanitize_model_facing_value(
    value: Any,
    *,
    redact_solution_refs: bool,
    limit: int = 1000,
) -> Any:
    if isinstance(value, str):
        return _prompt_safe_inline_text(
            value,
            limit=limit,
            redact_solution_refs=redact_solution_refs,
        )
    if isinstance(value, Mapping):
        return {
            str(
                _sanitize_model_facing_value(
                    str(key),
                    redact_solution_refs=redact_solution_refs,
                    limit=limit,
                )
            ): _sanitize_model_facing_value(
                item,
                redact_solution_refs=redact_solution_refs,
                limit=limit,
            )
            for key, item in value.items()
        }
    if isinstance(value, (list, tuple)):
        return [
            _sanitize_model_facing_value(
                item,
                redact_solution_refs=redact_solution_refs,
                limit=limit,
            )
            for item in value
        ]
    return value


def _neutralize_invalid_prompt_terms(text: str) -> str:
    out = str(text or "")
    for pattern, replacement in _PROMPT_NEUTRALIZATIONS:
        out = pattern.sub(replacement, out)
    return out


def _neutralize_messages_for_invalid_prompt(
    messages: Sequence[dict],
) -> List[dict]:
    sanitized: List[dict] = []
    for message in messages:
        item = dict(message or {})
        required_context = item.get("_required_prompt_context")
        is_required = bool(
            required_context is True
            or (
                isinstance(required_context, Mapping)
                and required_context.get("required", True)
            )
        )
        if "content" in item and not is_required:
            item["content"] = _neutralize_invalid_prompt_terms(
                str(item.get("content", "") or "")
            )
        tool_calls = None if is_required else item.get("tool_calls")
        if isinstance(tool_calls, list):
            sanitized_calls: List[dict] = []
            for tool_call in tool_calls:
                call_item = dict(tool_call or {})
                function = call_item.get("function")
                if isinstance(function, dict):
                    function_item = dict(function)
                    if "arguments" in function_item:
                        function_item["arguments"] = _neutralize_invalid_prompt_terms(
                            str(function_item.get("arguments", "") or "")
                        )
                    call_item["function"] = function_item
                sanitized_calls.append(call_item)
            item["tool_calls"] = sanitized_calls
        sanitized.append(item)
    return sanitized


async def _call_with_invalid_prompt_rescue(
    *,
    invoke: Any,
    messages: Sequence[dict],
    trace: Any,
    trace_prefix: str,
    on_rescue: Optional[Callable[[], None]] = None,
) -> tuple[Any, List[dict], bool]:
    """Call the provider, retrying once with neutral wording on prompt rejection."""

    request_messages = list(messages or [])
    try:
        return await invoke(request_messages), request_messages, False
    except Exception as exc:
        if not _is_invalid_prompt_error(exc):
            raise
        sanitized = _neutralize_messages_for_invalid_prompt(request_messages)
        if sanitized == request_messages:
            raise
        if on_rescue is not None:
            on_rescue()
        trace(
            trace_prefix,
            "  provider rejected prompt; retrying this same LLM turn with "
            "neutral answer-placeholder wording",
        )
        return await invoke(sanitized), sanitized, True


def _legacy_imports():
    from ensemble_prover.mini_prover import (
        _feedback_lemmas_for_answer_safe_recheck,
        _messages_with_search_context,
        _prompt_safe_tool_call_token,
        _prompt_safe_tool_name_token,
        _prompt_safe_tool_arguments,
        _proof_state_acceptance_preamble,
        _needs_answer_safe_feedback_check,
        _run_apply_decl_to_goal_tool,
        _run_check_lean_tool,
        _run_search_tool,
        _run_search_theorems_tool,
        _repair_content_is_helper_only_decomposition,
        _repair_self_check_required_message,
        _repair_turn_requires_self_check,
        _select_tool_calls_for_repair_budget,
        _is_retryable_llm_exception,
        _trace,
    )
    from ensemble_prover.lean_compute_tool import run_compute_examples_tool
    from ensemble_prover.try_lean_tool import run_try_lean_tool
    from ensemble_prover.certify_counterexample_tool import (
        run_certify_counterexample_tool,
    )
    from ensemble_prover.skeleton_tool import run_try_skeleton_tool

    return {
        "feedback_lemmas": _feedback_lemmas_for_answer_safe_recheck,
        "messages_with_search_context": _messages_with_search_context,
        "prompt_safe_tool_call_token": _prompt_safe_tool_call_token,
        "prompt_safe_tool_name_token": _prompt_safe_tool_name_token,
        "prompt_safe_tool_arguments": _prompt_safe_tool_arguments,
        "proof_state_acceptance_preamble": _proof_state_acceptance_preamble,
        "needs_answer_safe_feedback_check": _needs_answer_safe_feedback_check,
        "run_apply_decl_to_goal_tool": _run_apply_decl_to_goal_tool,
        "run_check_lean_tool": _run_check_lean_tool,
        "run_compute_examples_tool": run_compute_examples_tool,
        "run_search_tool": _run_search_tool,
        "run_search_theorems_tool": _run_search_theorems_tool,
        "run_try_lean_tool": run_try_lean_tool,
        "run_certify_counterexample_tool": run_certify_counterexample_tool,
        "run_try_skeleton_tool": run_try_skeleton_tool,
        "repair_content_is_helper_only_decomposition": (
            _repair_content_is_helper_only_decomposition
        ),
        "repair_self_check_required_message": _repair_self_check_required_message,
        "repair_turn_requires_self_check": _repair_turn_requires_self_check,
        "select_tool_calls_for_repair_budget": _select_tool_calls_for_repair_budget,
        "is_retryable_llm_exception": _is_retryable_llm_exception,
        "trace": _trace,
    }


async def _call_llm_with_tools_one_round_impl(
    *,
    conv: Any,
    client: Any,
    lean: Any,
    dossier: Any = None,
    authority_dossier: Any = None,
    proof_state: Any = None,
    searcher: Any = None,
    tools_list: Sequence[dict] = (),
    use_tools: bool = False,
    lean_check_tool_enabled: bool = False,
    try_lean_tool_enabled: bool = False,
    compute_examples_tool_enabled: bool = False,
    try_skeleton_tool_enabled: bool = False,
    apply_decl_to_goal_tool_enabled: bool = False,
    max_tool_calls_per_turn: int = 10,
    max_no_formal_progress_tool_calls: int = 6,
    max_consecutive_search_tool_calls: int = 6,
    proof_state_child_goal_limit: int = 4,
    proof_cache: Any = None,
    temperature_override: Any = None,
    trace_prefix: str = "",
    turn: int = 1,
    goal_statement_override: Optional[str] = None,
    try_lean_allow_declarations: bool = False,
    try_lean_require_declaration: bool = False,
    cost_controller: Optional[Any] = None,
    cost_role: str = "",
    cost_scope: str = "",
    session_scope: str = "problem",
    cost_action_id: str = "",
    max_tokens_override: Any = None,
    temperature_metadata: Optional[Mapping[str, Any]] = None,
    max_turn_elapsed_s: float = 0.0,
    request_timeout_override_s: Optional[float] = None,
    provider_call_quantum_s: float = _CONVERSATION_PROVIDER_WALL_QUANTUM_S,
    scheduler_call_quantum_enabled: bool = False,
    publication_guard: Optional[Callable[[], None]] = None,
) -> ToolLoopResult:
    """Run the inner tool-use loop for one outer turn.

    Mirrors mini_prover.py:3273-3534 line-for-line. Mutates ``conv.history``
    by appending the assistant tool-call message and per-call tool messages.
    """

    primitives = _legacy_imports()
    started = time.monotonic()
    supports_tool_calls = getattr(client, "supports_tool_calls", None)
    if use_tools and callable(supports_tool_calls):
        try:
            use_tools = bool(supports_tool_calls())
        except Exception:
            # Capability probing is advisory. Preserve the historical attempt
            # when a third-party client cannot answer it reliably.
            pass
    try:
        max_turn_elapsed_f = float(max_turn_elapsed_s or 0.0)
    except Exception:
        max_turn_elapsed_f = 0.0
    if max_turn_elapsed_f < 0.0:
        max_turn_elapsed_f = 0.0
    try:
        request_timeout_override_f = (
            float(request_timeout_override_s)
            if request_timeout_override_s is not None
            else None
        )
    except Exception:
        request_timeout_override_f = None
    if request_timeout_override_f is not None and request_timeout_override_f <= 0.0:
        request_timeout_override_f = None
    effective_request_timeout_s = request_timeout_override_f
    effective_operation_timeout_s = (
        request_timeout_override_f * 2.0
        if request_timeout_override_f is not None
        else None
    )
    provider_timeout_lease_partitioned = False
    try:
        provider_call_quantum_f = max(0.0, float(provider_call_quantum_s or 0.0))
    except Exception:
        provider_call_quantum_f = _CONVERSATION_PROVIDER_WALL_QUANTUM_S
    redact_solution_refs = _conversation_should_redact_solution_refs(conv)

    def prompt_safe_tool_call_token(value: Any) -> str:
        sanitizer = primitives.get(
            "prompt_safe_tool_call_token",
            lambda item: str(item or ""),
        )
        try:
            return str(sanitizer(value, redact_solution_refs=redact_solution_refs))
        except TypeError:
            return str(sanitizer(value))

    def prompt_safe_tool_name_token(value: Any) -> str:
        sanitizer = primitives.get("prompt_safe_tool_name_token")
        if sanitizer is None:
            return prompt_safe_tool_call_token(value)
        try:
            return str(sanitizer(value, redact_solution_refs=redact_solution_refs))
        except TypeError:
            return str(sanitizer(value))

    def prompt_safe_tool_arguments(value: Any) -> str:
        def sanitize(item: Any) -> Any:
            if isinstance(item, str):
                return _prompt_safe_inline_text(
                    item,
                    limit=1200,
                    redact_solution_refs=redact_solution_refs,
                )
            if isinstance(item, list):
                return [sanitize(child) for child in item[:20]]
            if isinstance(item, dict):
                return {
                    _prompt_safe_inline_text(
                        str(key),
                        limit=120,
                        redact_solution_refs=redact_solution_refs,
                    ): sanitize(child)
                    for key, child in list(item.items())[:40]
                }
            return item

        def fallback(item: Any) -> str:
            raw = "" if item is None else str(item)
            parsed, parse_error = parse_tool_arguments(item)
            if parse_error:
                # Redact JSON string VALUES, not the whole literal set: the
                # schema-derived keys are what make a malformed call
                # diagnosable (truncated vs wrong-shaped).
                safe_raw = prompt_safe_malformed_tool_arguments(raw, limit=1600)
                return json.dumps(
                    {"__malformed_arguments__": safe_raw},
                    ensure_ascii=False,
                    allow_nan=False,
                )
            return json.dumps(sanitize(parsed), ensure_ascii=False, allow_nan=False)

        sanitizer = primitives.get(
            "prompt_safe_tool_arguments",
            fallback,
        )
        try:
            return str(sanitizer(value, redact_solution_refs=redact_solution_refs))
        except TypeError:
            return str(sanitizer(value))

    def prompt_safe_tool_args_record(value: Any, parse_error: str = "") -> dict:
        def sanitize_record(item: Any) -> Any:
            if isinstance(item, str):
                return _prompt_safe_inline_text(
                    item,
                    limit=1200,
                    redact_solution_refs=redact_solution_refs,
                )
            if isinstance(item, list):
                return [sanitize_record(child) for child in item[:20]]
            if isinstance(item, dict):
                return {
                    _prompt_safe_inline_text(
                        str(key),
                        limit=120,
                        redact_solution_refs=redact_solution_refs,
                    ): sanitize_record(child)
                    for key, child in list(item.items())[:40]
                }
            return item

        if parse_error:
            return {}
        try:
            payload = json.loads(prompt_safe_tool_arguments(value))
        except Exception:
            return {}
        return sanitize_record(payload) if isinstance(payload, dict) else {}

    def increment_dossier_metric(key: str, amount: int = 1) -> None:
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

    handoff_compact_record: dict = {}
    if str(getattr(conv, "role", "") or "") == "refine":
        handoff_compact = getattr(conv, "compact_history_for_refine_handoff", None)
        if callable(handoff_compact):
            try:
                handoff_compact_record = handoff_compact()
            except Exception as exc:
                handoff_compact_record = {}
                primitives["trace"](
                    trace_prefix,
                    f"  refiner handoff compaction failed: {type(exc).__name__}: {exc}",
                )
            if handoff_compact_record:
                increment_dossier_metric("mini_refine_handoff_compactions", 1)
                increment_dossier_metric(
                    "mini_refine_handoff_compacted_messages",
                    int(handoff_compact_record.get("removed_messages", 0) or 0),
                )
                increment_dossier_metric(
                    "mini_refine_handoff_compacted_chars",
                    int(handoff_compact_record.get("removed_chars", 0) or 0),
                )
                increment_dossier_metric(
                    "mini_refine_handoff_compacted_tool_rounds",
                    int(handoff_compact_record.get("removed_tool_rounds", 0) or 0),
                )
                primitives["trace"](
                    trace_prefix,
                    "  compacted refiner handoff history: "
                    f"removed {handoff_compact_record.get('removed_messages', 0)} msg(s), "
                    f"{handoff_compact_record.get('removed_chars', 0)} chars.",
                )

    compact = getattr(conv, "compact_history_for_next_turn", None)
    if callable(compact):
        try:
            compact_record = compact()
        except Exception as exc:
            compact_record = {}
            primitives["trace"](
                trace_prefix,
                f"  history compaction failed: {type(exc).__name__}: {exc}",
            )
        if compact_record:
            primitives["trace"](
                trace_prefix,
                "  compacted stale history: "
                f"removed {compact_record.get('removed_messages', 0)} msg(s), "
                f"{compact_record.get('removed_chars', 0)} chars.",
            )

    content = ""
    tool_calls_used = 0
    tool_call_log: List[dict] = []
    llm_error: Optional[str] = None
    llm_failure_kind = ""
    llm_retryable = False
    llm_terminal = False
    llm_failure_reason = ""
    llm_retry_deadline: dict = {}
    provider_attempts: List[dict] = []
    tool_state_updates = 0
    tool_state_closures = 0
    tool_state_update_statuses: List[str] = []
    try:
        turn_max_tokens_override = (
            max_tokens_override
            if isinstance(max_tokens_override, MiniRequestEnvelopePolicy)
            else (
            max(1, int(max_tokens_override))
            if max_tokens_override is not None
            and int(max_tokens_override) > 0
            else None
            )
        )
    except Exception:
        turn_max_tokens_override = None
    repair_turn_requires_self_check = primitives.get(
        "repair_turn_requires_self_check",
        lambda _conv: False,
    )
    repair_self_check_required = (
        bool(repair_turn_requires_self_check(conv))
        and use_tools
        and try_lean_tool_enabled
    )
    repair_self_check_seen = False
    repair_self_check_attempted = False
    repair_self_check_budget_exhausted = False
    repair_self_check_status = ""
    repair_self_check_helper_only_allowed = False
    repair_self_check_reminder_sent = False
    repair_self_check_final_slot_recovery_reminder_sent = False
    repair_self_check_codes: List[str] = []
    pending_tool_replay: List[dict] = []
    pending_tool_replay_is_paid_retry = False
    durable_progress_tool_replay_pending = False
    durable_progress_tool_replay_exhausted = False
    durable_progress_tool_replay_predecessor_identity = ""
    durable_progress_tool_continuation_identity = ""
    durable_progress_tool_continuation_granted = False
    durable_progress_helper_receipts: list[dict[str, str]] = []
    tool_infrastructure_receipt_id = ""
    tool_infrastructure_disposition = ""
    paid_tool_infrastructure_disposition = ""
    paid_tool_continuation_identity = ""
    paid_tool_continuation_granted = False
    infrastructure_replay_signatures: set[str] = set()
    accepted_try_lean_receipts: dict[str, str] = {}
    durable_tool_retry_banked = False
    repair_discovery_tool_calls_used = 0
    repair_verification_tool_calls_used = 0
    repair_discovery_quota_exhausted = False
    non_verdict_repair_self_check_statuses = {
        "try_lean_infrastructure_error",
        "try_lean_malformed_arguments",
        "try_lean_preflight_error",
    }
    deepseek_dsml_reprompted_after_budget = False
    final_no_tools_policy_reprompted = False
    provider_protocol_event = ""
    provider_protocol_original_content = ""
    provider_defer: dict[str, Any] = {}
    failed_provider_pre_generation_rejection = False
    recovered_finalizer_error = ""
    recovered_finalizer_failure_kind = ""
    recovered_finalizer_retryable = False
    recovered_finalizer_provider_call_quantum_exhausted = False
    recovered_finalizer_terminal = False
    recovered_finalizer_failure_reason = ""
    recovered_finalizer_retry_deadline: dict[str, Any] = {}
    recovered_finalizer_provider_attempts: list[dict] = []
    recovered_finalizer_provider_defer: dict[str, Any] = {}
    llm_turn_elapsed_budget_exhausted = False
    llm_turn_elapsed_task_unsettled = False
    seen_tool_call_signatures: set[str] = set()
    repeat_guidance_used = False
    repeat_recovery_pending = False
    force_finalize_without_tools = False
    final_no_tools_recovery_attempted = False
    final_no_tools_visibility_recovery_pending = False
    tool_repeat_detected = False
    tool_repeat_action = ""
    tool_repeat_signature = ""
    proof_tool_attempts = 0
    consecutive_no_formal_progress = 0
    consecutive_search_tool_calls = 0
    search_cadence_violation_batches = 0
    search_cadence_stall_detected = False
    semantic_result_counts: dict[str, int] = {}
    semantic_no_progress_detected = False
    semantic_no_progress_reason = ""
    semantic_no_progress_signature = ""
    semantic_diagnostic_progress_count = 0
    semantic_diagnostic_best_phase = -1
    semantic_diagnostic_best_error_kind = ""
    semantic_diagnostic_best_goal_count = -1
    semantic_diagnostic_last_reason = ""
    semantic_diagnostic_best_signature = ""
    semantic_diagnostic_best_by_tool: dict[str, _SemanticLeanDiagnosticState] = {}
    partial_try_lean_promotions = 0
    accepted_try_lean_helper_names: list[str] = []
    accepted_exact_target_code = ""
    final_no_tools_event = ""
    final_no_tools_finish_reason = ""
    final_no_tools_reasoning_content_chars = 0
    final_no_tools_used_accepted_proof = False
    banked_mixed_final_content = ""
    banked_mixed_finalizer_pending = False
    banked_mixed_finalizer_lane_identity = ""
    authoritative_falsification = False
    proof_disproof_conflict = False
    authoritative_falsification_target = ""
    authoritative_falsification_certificate_hash = ""
    authoritative_falsification_environment_hash = ""
    in_turn_tool_history_compactions = 0
    in_turn_tool_history_compacted_messages = 0
    in_turn_tool_history_compacted_tool_rounds = 0
    in_turn_tool_history_compacted_chars = 0
    provider_calls_completed = 0
    provider_dispatches_started = 0
    provider_call_quantum_exhausted = False
    provider_finalizer_continuation_exhausted = False
    provider_dispatch_quantum_yield_metric_pending = False
    provider_quantum_cap_active = False
    provider_finalizer_continuation_active = False
    provider_quantum_authenticated_dispatches_started = 0
    provider_dispatch_quantum_spent = False
    provider_call_elapsed_s = 0.0
    provider_call_cumulative_elapsed_s = 0.0
    provider_call_cumulative_wall_exhausted = False
    provider_call_cumulative_wall_cap_s = (
        max(
            _CONVERSATION_PROVIDER_CUMULATIVE_WALL_FLOOR_S,
            provider_call_quantum_f
            * _CONVERSATION_PROVIDER_CUMULATIVE_WALL_QUANTA,
        )
        if provider_call_quantum_f > 0.0
        else 0.0
    )
    if scheduler_call_quantum_enabled and provider_call_cumulative_wall_cap_s <= 0.0:
        client_cfg = getattr(client, "cfg", None)
        try:
            configured_operation_timeout_s = float(
                getattr(client_cfg, "operation_timeout_s", 0.0) or 0.0
            )
        except (TypeError, ValueError):
            configured_operation_timeout_s = 0.0
        try:
            configured_request_timeout_s = float(
                request_timeout_override_f
                or getattr(client_cfg, "request_timeout_s", 0.0)
                or getattr(client_cfg, "timeout_s", 0.0)
                or 0.0
            )
        except (TypeError, ValueError):
            configured_request_timeout_s = 0.0
        provider_call_cumulative_wall_cap_s = (
            configured_operation_timeout_s
            if configured_operation_timeout_s > 0.0
            else configured_request_timeout_s * 2.0
        )
    if max_turn_elapsed_f > 0.0:
        provider_call_cumulative_wall_cap_s = (
            min(provider_call_cumulative_wall_cap_s, max_turn_elapsed_f)
            if provider_call_cumulative_wall_cap_s > 0.0
            else max_turn_elapsed_f
        )
    provider_call_cumulative_deadline_monotonic = (
        started + provider_call_cumulative_wall_cap_s
        if provider_call_cumulative_wall_cap_s > 0.0
        else 0.0
    )
    provider_call_quantum_max_retries = max(
        2,
        (
            max(1, int(max_tool_calls_per_turn or 1))
            + _CONVERSATION_PROVIDER_CALL_QUANTUM
            - 1
        )
        // _CONVERSATION_PROVIDER_CALL_QUANTUM
        + 1,
    )
    try:
        no_progress_cap = max(1, int(max_no_formal_progress_tool_calls or 0))
    except Exception:
        no_progress_cap = 6
    try:
        search_cadence_cap = max(0, int(max_consecutive_search_tool_calls or 0))
    except Exception:
        search_cadence_cap = 6
    advertised_tool_names = {
        str((item.get("function") or {}).get("name", "") or "")
        for item in tools_list
        if isinstance(item, Mapping)
    }
    formal_cadence_available = bool(
        advertised_tool_names & _FORMAL_CADENCE_TOOL_NAMES
    )
    # Seeing the same Lean state three times is stronger evidence than merely
    # accumulating failed attempts, so it has a tighter independent cap.
    semantic_repeat_cap = min(3, no_progress_cap)
    quantum_state = _validated_provider_call_quantum_state(
        conv,
        goal_statement_override=goal_statement_override,
        dossier=dossier,
        migrate_legacy_repair_v1=repair_self_check_required,
        max_tool_calls_per_turn=max_tool_calls_per_turn,
    )
    resumed_provider_continuation = bool(quantum_state)
    provider_chain_resume_target_id = str(
        quantum_state.get("provider_chain_resume_target_id") or ""
    ).strip()
    if not re.fullmatch(
        r"(?:target:[0-9]+|chain:[0-9a-f]{64}:target:[0-9]+)",
        provider_chain_resume_target_id,
    ):
        provider_chain_resume_target_id = ""
    invalid_prompt_neutralization_pending = bool(
        quantum_state.get("invalid_prompt_neutralization_pending", False)
    )
    if quantum_state:
        prior_cumulative_elapsed = _nonnegative_finite_float(
            quantum_state.get("provider_call_cumulative_elapsed_s", 0.0)
        )
        stored_cumulative_cap = _nonnegative_finite_float(
            quantum_state.get("provider_call_cumulative_wall_cap_s", 0.0)
        )
        if stored_cumulative_cap > 0.0:
            provider_call_cumulative_wall_cap_s = (
                min(
                    provider_call_cumulative_wall_cap_s,
                    stored_cumulative_cap,
                )
                if provider_call_cumulative_wall_cap_s > 0.0
                else stored_cumulative_cap
            )
        provider_call_cumulative_elapsed_s = prior_cumulative_elapsed
        stored_deadline = _nonnegative_finite_float(
            quantum_state.get(
                "provider_call_cumulative_deadline_monotonic",
                0.0,
            )
        )
        fresh_remaining_deadline = (
            started
            + max(
                0.0,
                provider_call_cumulative_wall_cap_s
                - provider_call_cumulative_elapsed_s,
            )
            if provider_call_cumulative_wall_cap_s > 0.0
            else 0.0
        )
        if stored_deadline > 0.0 and fresh_remaining_deadline > 0.0:
            provider_call_cumulative_deadline_monotonic = min(
                stored_deadline,
                fresh_remaining_deadline,
            )
        elif stored_deadline > 0.0:
            provider_call_cumulative_deadline_monotonic = stored_deadline
        elif fresh_remaining_deadline > 0.0:
            provider_call_cumulative_deadline_monotonic = fresh_remaining_deadline
        tool_calls_used = max(
            0,
            min(
                max(0, int(max_tool_calls_per_turn or 0)),
                _nonnegative_int(quantum_state.get("tool_calls_used", 0)),
            ),
        )
        repair_discovery_tool_calls_used = min(
            tool_calls_used,
            _nonnegative_int(
                quantum_state.get("repair_discovery_tool_calls_used", 0)
            ),
        )
        repair_verification_tool_calls_used = min(
            max(0, tool_calls_used - repair_discovery_tool_calls_used),
            _nonnegative_int(
                quantum_state.get("repair_verification_tool_calls_used", 0)
            ),
        )
        repair_discovery_quota_exhausted = bool(
            repair_discovery_quota_exhausted
            or quantum_state.get("repair_discovery_quota_exhausted", False)
        )
        repair_self_check_seen = bool(
            quantum_state.get("repair_self_check_seen", False)
        )
        repair_self_check_required = bool(
            repair_self_check_required
            or quantum_state.get("repair_self_check_required", False)
        )
        repair_self_check_attempted = bool(
            quantum_state.get("repair_self_check_attempted", False)
        )
        repair_self_check_status = str(
            quantum_state.get("repair_self_check_status", "") or ""
        )
        repair_self_check_codes = [
            str(code or "")
            for code in list(
                quantum_state.get("repair_self_check_codes", []) or []
            )
            if str(code or "")
        ]
        repair_self_check_reminder_sent = bool(
            quantum_state.get("repair_self_check_reminder_sent", False)
        )
        repair_self_check_final_slot_recovery_reminder_sent = bool(
            quantum_state.get(
                "repair_self_check_final_slot_recovery_reminder_sent",
                False,
            )
        )
        raw_pending_tool_replay = quantum_state.get("pending_tool_replay", [])
        if isinstance(raw_pending_tool_replay, (list, tuple)):
            replay_capacity = (
                max(
                    0,
                    max(0, int(max_tool_calls_per_turn or 0))
                    - tool_calls_used,
                )
                if quantum_state.get("pending_tool_replay_disposition")
                == "durable_progress_cutpoint"
                else 4
            )
            pending_tool_replay = [
                dict(call)
                for call in raw_pending_tool_replay[:replay_capacity]
                if isinstance(call, Mapping)
            ]
        durable_progress_tool_replay_pending = bool(
            pending_tool_replay
            and quantum_state.get("pending_tool_replay_disposition")
            == "durable_progress_cutpoint"
        )
        if durable_progress_tool_replay_pending:
            durable_progress_tool_continuation_identity = str(
                quantum_state.get(
                    "durable_progress_tool_continuation_identity"
                )
                or ""
            ).strip()
            durable_progress_tool_continuation_granted = bool(
                durable_progress_tool_continuation_identity
            )
            durable_progress_tool_replay_predecessor_identity = (
                durable_progress_tool_continuation_identity
            )
            durable_progress_helper_receipts = [
                {
                    "name": str(receipt.get("name") or "").strip(),
                    "source_hash": str(
                        receipt.get("source_hash") or ""
                    ).strip(),
                }
                for receipt in list(
                    quantum_state.get(
                        "durable_progress_tool_continuation_helper_receipts",
                        [],
                    )
                    or []
                )
                if isinstance(receipt, Mapping)
                and str(receipt.get("name") or "").strip()
                and str(receipt.get("source_hash") or "").strip()
            ]
        tool_infrastructure_receipt_id = str(
            quantum_state.get("tool_infrastructure_receipt_id", "") or ""
        )[:128]
        stored_tool_infrastructure_disposition = str(
            quantum_state.get("tool_infrastructure_disposition", "") or ""
        ).strip()
        if stored_tool_infrastructure_disposition in {
            "infrastructure_deferred_before_launch",
            "infrastructure_after_launch",
        }:
            tool_infrastructure_disposition = (
                stored_tool_infrastructure_disposition
            )
        if "pending_tool_replay_is_paid_retry" in quantum_state:
            pending_tool_replay_is_paid_retry = bool(
                quantum_state.get("pending_tool_replay_is_paid_retry")
            )
        else:
            # The immediately preceding schema-v4 writer persisted an exact
            # disposition but not the entitlement bit. Only explicit
            # post-launch evidence migrates as an already-earned paid retry;
            # older receipts missing both fields remain conservatively free
            # and can earn at most one bounded replay after an actual launch.
            pending_tool_replay_is_paid_retry = bool(
                pending_tool_replay
                and stored_tool_infrastructure_disposition
                == "infrastructure_after_launch"
            )
        if pending_tool_replay:
            paid_tool_continuation_identity = tool_infrastructure_receipt_id
        provider_call_cumulative_wall_exhausted = bool(
            quantum_state.get(
                "provider_call_cumulative_wall_exhausted",
                False,
            )
        )
        seen_tool_call_signatures = {
            str(signature or "")
            for signature in list(
                quantum_state.get("seen_tool_call_signatures", []) or []
            )
            if str(signature or "")
        }
        final_no_tools_visibility_recovery_pending = bool(
            quantum_state.get("final_no_tools_visibility_recovery_pending")
        )
        deepseek_dsml_reprompted_after_budget = bool(
            quantum_state.get("deepseek_dsml_reprompted_after_budget", False)
        )
        final_no_tools_policy_reprompted = bool(
            quantum_state.get("final_no_tools_policy_reprompted", False)
        )
        force_finalize_without_tools = bool(
            quantum_state.get("force_finalize_without_tools", False)
        )
        final_no_tools_recovery_attempted = bool(
            quantum_state.get("final_no_tools_recovery_attempted", False)
            or force_finalize_without_tools
        )
        repeat_guidance_used = bool(
            quantum_state.get("repeat_guidance_used", False)
        )
        repeat_recovery_pending = bool(
            quantum_state.get("repeat_recovery_pending", False)
        )
        tool_repeat_detected = bool(
            quantum_state.get("tool_repeat_detected", False)
        )
        tool_repeat_action = str(
            quantum_state.get("tool_repeat_action", "") or ""
        )[:120]
        tool_repeat_signature = str(
            quantum_state.get("tool_repeat_signature", "") or ""
        )[:256]
        proof_tool_attempts = min(
            max(0, int(max_tool_calls_per_turn or 0)),
            _nonnegative_int(quantum_state.get("proof_tool_attempts", 0)),
        )
        consecutive_no_formal_progress = min(
            max(0, int(max_tool_calls_per_turn or 0)),
            _nonnegative_int(
                quantum_state.get("consecutive_no_formal_progress", 0)
            ),
        )
        consecutive_search_tool_calls = min(
            max(0, int(max_tool_calls_per_turn or 0)),
            _nonnegative_int(
                quantum_state.get("consecutive_search_tool_calls", 0)
            ),
        )
        raw_semantic_counts = quantum_state.get("semantic_result_counts", {})
        search_cadence_violation_batches = min(
            _SEARCH_CADENCE_VIOLATION_BATCH_CAP,
            _nonnegative_int(
                quantum_state.get("search_cadence_violation_batches", 0)
            ),
        )
        search_cadence_stall_detected = bool(
            quantum_state.get("search_cadence_stall_detected", False)
        )
        if isinstance(raw_semantic_counts, Mapping):
            semantic_result_counts = {
                str(signature or "")[:256]: min(
                    semantic_repeat_cap,
                    _nonnegative_int(count),
                )
                for signature, count in list(raw_semantic_counts.items())[:32]
                if str(signature or "")
            }
        semantic_no_progress_detected = bool(
            quantum_state.get("semantic_no_progress_detected", False)
        )
        semantic_no_progress_reason = str(
            quantum_state.get("semantic_no_progress_reason", "") or ""
        )[:120]
        semantic_no_progress_signature = str(
            quantum_state.get("semantic_no_progress_signature", "") or ""
        )[:256]
        semantic_diagnostic_progress_count = min(
            max(0, int(max_tool_calls_per_turn or 0)),
            _nonnegative_int(
                quantum_state.get("semantic_diagnostic_progress_count", 0)
            ),
        )
        semantic_diagnostic_best_phase = _bounded_int(
            quantum_state.get("semantic_diagnostic_best_phase", -1),
            minimum=-1,
            maximum=16,
            default=-1,
        )
        semantic_diagnostic_best_error_kind = str(
            quantum_state.get("semantic_diagnostic_best_error_kind", "") or ""
        )[:120]
        semantic_diagnostic_best_goal_count = _bounded_int(
            quantum_state.get("semantic_diagnostic_best_goal_count", -1),
            minimum=-1,
            maximum=10_000,
            default=-1,
        )
        semantic_diagnostic_last_reason = str(
            quantum_state.get("semantic_diagnostic_last_reason", "") or ""
        )[:120]
        semantic_diagnostic_best_signature = str(
            quantum_state.get("semantic_diagnostic_best_signature", "") or ""
        )[:256]
        raw_best_by_tool = quantum_state.get(
            "semantic_diagnostic_best_by_tool", {}
        )
        if isinstance(raw_best_by_tool, Mapping):
            for raw_name, raw_diagnostic in list(raw_best_by_tool.items())[:8]:
                name = str(raw_name or "")[:80]
                if not name or not isinstance(raw_diagnostic, Mapping):
                    continue
                try:
                    phase = int(raw_diagnostic.get("phase", -1))
                    goal_count_raw = raw_diagnostic.get("goal_count")
                    goal_count = (
                        None
                        if goal_count_raw is None
                        else max(0, int(goal_count_raw))
                    )
                except (TypeError, ValueError, OverflowError):
                    continue
                if phase < 0:
                    continue
                semantic_diagnostic_best_by_tool[name] = (
                    _SemanticLeanDiagnosticState(
                        phase=phase,
                        error_kind=str(
                            raw_diagnostic.get("error_kind", "") or ""
                        )[:120],
                        goal_count=goal_count,
                        signature=str(
                            raw_diagnostic.get("signature", "") or ""
                        )[:256],
                    )
                )
        partial_try_lean_promotions = min(
            max(0, int(max_tool_calls_per_turn or 0)),
            _nonnegative_int(
                quantum_state.get("partial_try_lean_promotions", 0)
            ),
        )
        banked_mixed_final_content = str(
            quantum_state.get("banked_mixed_final_content", "") or ""
        )[:100_000]
        banked_mixed_finalizer_pending = bool(
            banked_mixed_final_content
            and quantum_state.get("banked_mixed_finalizer_pending", False)
        )
        banked_mixed_finalizer_lane_identity = str(
            quantum_state.get("banked_mixed_finalizer_lane_identity", "") or ""
        )[:128]
        if final_no_tools_visibility_recovery_pending:
            final_no_tools_recovery_attempted = True
            force_finalize_without_tools = True
    if (
        provider_call_quantum_f <= 0.0
        and max_turn_elapsed_f <= 0.0
        and not scheduler_call_quantum_enabled
    ):
        # An older resume must not re-introduce a finite cap after the
        # production proving policy disabled both wall-clock limits. An
        # explicit hard turn lease remains authoritative across call-count
        # scheduler yields.
        provider_call_cumulative_wall_cap_s = 0.0
        provider_call_cumulative_deadline_monotonic = 0.0
        provider_call_cumulative_wall_exhausted = False
    turn_deadline_monotonic = (
        started + max_turn_elapsed_f if max_turn_elapsed_f > 0.0 else 0.0
    )

    def elapsed_budget_exhausted() -> bool:
        return bool(
            max_turn_elapsed_f > 0.0
            and (time.monotonic() - started) >= max_turn_elapsed_f
        )

    def elapsed_budget_remaining_s() -> Optional[float]:
        if max_turn_elapsed_f <= 0.0:
            return None
        return max_turn_elapsed_f - (time.monotonic() - started)

    def provider_call_quantum_boundary_reached() -> bool:
        """Whether a completed provider call owes the scheduler a yield.

        A zero wall quantum disables cancellation of an admitted response; it
        must not also disable call-count fairness after that response settles.
        A positive wall quantum retains the opt-in fast-call batching policy.
        """

        return bool(
            scheduler_call_quantum_enabled
            and provider_calls_completed >= _CONVERSATION_PROVIDER_CALL_QUANTUM
            and (
                provider_call_quantum_f <= 0.0
                or provider_call_elapsed_s >= provider_call_quantum_f
            )
        )

    def record_provider_call_quantum_yield(*, boundary: str) -> None:
        """Close one settled provider/tool transaction for scheduler fairness."""

        nonlocal provider_call_quantum_exhausted
        nonlocal llm_error, llm_failure_kind, llm_retryable, llm_terminal
        nonlocal llm_failure_reason
        provider_call_quantum_exhausted = True
        llm_error = "llm_provider_quantum_exhausted"
        llm_failure_kind = "llm_provider_quantum_exhausted"
        llm_retryable = True
        llm_terminal = False
        llm_failure_reason = llm_failure_kind
        _increment_tool_metric("mini_provider_call_quantum_yields", 1)
        primitives["trace"](
            trace_prefix,
            "  provider-call quantum exhausted at a complete "
            f"{boundary} boundary ({provider_calls_completed} calls, "
            f"{provider_call_elapsed_s:.3f}s); yielding to scheduler",
        )

    async def await_with_elapsed_budget(
        awaitable: Any,
        *,
        additional_deadline_monotonic: float = 0.0,
        additional_deadline_exception: Any = None,
    ) -> Any:
        nonlocal llm_turn_elapsed_task_unsettled
        turn_remaining = elapsed_budget_remaining_s()
        additional_remaining = (
            float(additional_deadline_monotonic) - time.monotonic()
            if float(additional_deadline_monotonic or 0.0) > 0.0
            else None
        )
        remaining_candidates = [
            value
            for value in (turn_remaining, additional_remaining)
            if value is not None
        ]
        remaining = min(remaining_candidates) if remaining_candidates else None
        additional_deadline_is_limiting = bool(
            additional_remaining is not None
            and (
                turn_remaining is None
                # When max_turn_elapsed also supplies the cumulative cap, both
                # deadlines are mathematically identical but are sampled a few
                # instructions apart. Treat sub-microsecond drift as a tie so
                # the established per-turn failure remains authoritative.
                or additional_remaining + 1e-6 < turn_remaining
            )
        )

        def deadline_exception() -> Exception:
            if (
                additional_deadline_is_limiting
                and additional_deadline_exception is not None
            ):
                return additional_deadline_exception()
            return _TurnElapsedBudgetExhausted()

        if remaining is None:
            return await awaitable
        if remaining <= 0.0:
            if hasattr(awaitable, "close"):
                awaitable.close()
            raise deadline_exception()
        task = asyncio.ensure_future(awaitable)

        def consume_late_task_result(done_task: asyncio.Future[Any]) -> None:
            # A cancellation-resistant runner must never surface a late
            # result into this turn, and its eventual exception must still be
            # observed so asyncio does not emit an unhandled-task warning.
            try:
                done_task.result()
            except asyncio.CancelledError:
                pass
            except Exception:
                pass

        consume_late_task_result = mark_runtime_owned_callback(
            consume_late_task_result
        )

        try:
            done, _pending = await asyncio.wait({task}, timeout=remaining)
        except asyncio.CancelledError:
            task.cancel()
            try:
                await asyncio.wait_for(asyncio.shield(task), timeout=0.2)
            except asyncio.CancelledError:
                pass
            except asyncio.TimeoutError:
                llm_turn_elapsed_task_unsettled = True
                task.add_done_callback(consume_late_task_result)
                detach_task_from_loop_shutdown(task)
            except Exception:
                pass
            raise
        additional_deadline_exhausted = bool(
            additional_deadline_monotonic > 0.0
            and time.monotonic() >= additional_deadline_monotonic
        )
        if (
            task not in done
            or elapsed_budget_exhausted()
            or additional_deadline_exhausted
        ):
            task.cancel()
            try:
                await asyncio.wait_for(asyncio.shield(task), timeout=0.2)
            except asyncio.CancelledError:
                pass
            except asyncio.TimeoutError:
                llm_turn_elapsed_task_unsettled = True
                task.add_done_callback(consume_late_task_result)
                detach_task_from_loop_shutdown(task)
            except Exception:
                pass
            if (
                additional_deadline_exhausted
                and additional_deadline_exception
                and additional_deadline_is_limiting
            ):
                raise additional_deadline_exception()
            raise deadline_exception()
        return task.result()

    def provider_timeout_kwargs() -> dict[str, float]:
        nonlocal effective_request_timeout_s
        nonlocal effective_operation_timeout_s
        nonlocal provider_timeout_lease_partitioned
        if request_timeout_override_f is None:
            if max_turn_elapsed_f <= 0.0:
                return {}
            # Partition the *remaining* turn lease at every provider boundary.
            # The former path inherited a 900-second HTTP window inside a
            # 1200-second action, then admitted another request which the
            # enclosing action could only cancel.  Keep ten percent (at most
            # two minutes) for tools, publication, and scheduler handoff. Keep
            # the model's configured request window when it fits; this
            # preserves long-reasoning capacity. A fast disconnect can still
            # retry inside the operation window, while a genuinely timed-out
            # generation cannot consume the whole turn because the transport
            # layer requires a complete request window before retrying.
            remaining_turn_s = max(
                0.0,
                max_turn_elapsed_f - (time.monotonic() - started),
            )
            settlement_reserve_s = min(
                _PROVIDER_SETTLEMENT_RESERVE_MAX_S,
                max(
                    _PROVIDER_SETTLEMENT_RESERVE_MIN_S,
                    remaining_turn_s * _PROVIDER_SETTLEMENT_RESERVE_FRACTION,
                ),
            )
            operation_window_s = max(
                0.001,
                remaining_turn_s - settlement_reserve_s,
            )
            configured_window_s = 0.0
            resolve_request_timeout = getattr(
                client,
                "_configured_request_timeout_s",
                None,
            )
            if callable(resolve_request_timeout):
                try:
                    configured_window_s = _nonnegative_finite_float(
                        resolve_request_timeout()
                    )
                except Exception:
                    configured_window_s = 0.0
            if configured_window_s <= 0.0:
                client_cfg = getattr(client, "cfg", None)
                configured_window_s = _nonnegative_finite_float(
                    getattr(client_cfg, "request_timeout_s", None)
                )
            if configured_window_s <= 0.0:
                configured_window_s = _nonnegative_finite_float(
                    getattr(getattr(client, "cfg", None), "timeout_s", 0.0)
                )
            request_window_s = max(
                0.001,
                min(
                    operation_window_s * (5.0 / 6.0),
                    configured_window_s
                    if configured_window_s > 0.0
                    else operation_window_s * (5.0 / 6.0),
                ),
            )
            effective_request_timeout_s = request_window_s
            effective_operation_timeout_s = operation_window_s
            provider_timeout_lease_partitioned = True
            return {
                "request_timeout_override_s": request_window_s,
                "operation_timeout_override_s": operation_window_s,
            }
        # The operation window must be larger than one request window:
        # a single hung attempt otherwise consumes the whole operation
        # budget and every provider-level retry dies with "LLM retry would
        # exceed deadline (attempt=1)" — the pre-ed5e8941 failure mode from
        # the 2026-06-22..25 run corpus. Reserve one extra request window
        # so at least one retry can run; overall turn wall-clock stays
        # bounded by max_turn_elapsed_s via await_with_elapsed_budget.
        # This branch is live whenever a role request-timeout override is
        # configured (``--prover-request-timeout-s`` / ``--refiner-request-
        # timeout-s`` set ``request_timeout_override_s``); the x2 keeps the
        # zero-retry failure from resurfacing on this path. The admission gate
        # in ``models._transport_retry_window_admissible`` must not charge the
        # backoff sleep against the reserved window, or the x2 is defeated.
        return {
            "request_timeout_override_s": request_timeout_override_f,
            "operation_timeout_override_s": request_timeout_override_f * 2.0,
        }

    def record_elapsed_budget_exhausted() -> None:
        nonlocal llm_error, llm_failure_kind, llm_retryable, llm_terminal
        nonlocal llm_failure_reason, llm_turn_elapsed_budget_exhausted
        llm_turn_elapsed_budget_exhausted = True
        llm_error = "llm_turn_elapsed_budget_exhausted"
        llm_failure_kind = "llm_turn_elapsed_budget_exhausted"
        llm_retryable = True
        llm_terminal = False
        llm_failure_reason = "llm_turn_elapsed_budget_exhausted"

    def provider_cumulative_wall_exhausted() -> bool:
        return bool(
            provider_call_cumulative_wall_exhausted
            or (
                provider_call_cumulative_wall_cap_s > 0.0
                and (
                    provider_call_cumulative_elapsed_s
                    >= provider_call_cumulative_wall_cap_s
                    or (
                        provider_call_cumulative_deadline_monotonic > 0.0
                        and time.monotonic()
                        >= provider_call_cumulative_deadline_monotonic
                    )
                )
            )
        )

    def record_provider_cumulative_wall_exhausted() -> None:
        nonlocal llm_error, llm_failure_kind, llm_retryable, llm_terminal
        nonlocal llm_failure_reason, provider_call_cumulative_wall_exhausted
        provider_call_cumulative_wall_exhausted = True
        llm_error = "llm_provider_cumulative_wall_exhausted"
        llm_failure_kind = "llm_provider_cumulative_wall_exhausted"
        llm_retryable = False
        # This lease belongs to one logical target/repair lane. Exhausting it
        # retires that lane from immediate provider redispatch; it is not a
        # mathematical/session terminal and must leave deterministic and
        # alternate frontier work runnable.
        llm_terminal = False
        llm_failure_reason = "llm_provider_cumulative_wall_exhausted"

    def observe_tool_state_update(tool_name: str, result_text: str) -> Optional[str]:
        nonlocal tool_state_updates, tool_state_closures
        if str(tool_name or "") not in {"apply_decl_to_goal", "try_skeleton"}:
            return None
        try:
            payload = json.loads(str(result_text or ""))
        except Exception:
            return None
        if not isinstance(payload, Mapping):
            return None
        update = payload.get("proof_state_update")
        if not isinstance(update, Mapping):
            return None
        status = str(update.get("status") or "").strip()
        if status not in {
            "closed",
            "root_finalized",
            "spawned_remaining_goals",
        }:
            return status or None
        tool_state_updates += 1
        if status in {"closed", "root_finalized"}:
            tool_state_closures += 1
        tool_state_update_statuses.append(status)
        return status

    def observe_proof_tool_progress(
        tool_name: str,
        result_text: str,
        *,
        state_status: Optional[str] = None,
        candidate_identity: str = "",
    ) -> str:
        """Update the per-turn progress governor from Lean-validated outcomes."""

        nonlocal proof_tool_attempts, consecutive_no_formal_progress
        nonlocal semantic_no_progress_detected, semantic_no_progress_reason
        nonlocal semantic_no_progress_signature
        nonlocal semantic_diagnostic_progress_count
        nonlocal semantic_diagnostic_best_phase
        nonlocal semantic_diagnostic_best_error_kind
        nonlocal semantic_diagnostic_best_goal_count
        nonlocal semantic_diagnostic_last_reason
        nonlocal semantic_diagnostic_best_signature
        name = str(tool_name or "")
        if name not in {
            "try_lean",
            "certify_counterexample",
            "try_skeleton",
            "apply_decl_to_goal",
        }:
            return ""
        proof_tool_attempts += 1
        accepted_try = name == "try_lean" and str(result_text or "").startswith(
            "try_lean accepted."
        )
        accepted_counterexample = name == "certify_counterexample" and str(
            result_text or ""
        ).startswith("certify_counterexample accepted.")
        durable_update = str(state_status or "") in {
            "closed",
            "root_finalized",
            "spawned_remaining_goals",
        }
        if accepted_try or accepted_counterexample or durable_update:
            consecutive_no_formal_progress = 0
            return ""

        diagnostic_state = _semantic_lean_diagnostic_state(name, result_text)
        previous_tool_best = semantic_diagnostic_best_by_tool.get(name)
        tool_progress_reason = _semantic_diagnostic_improvement(
            previous_tool_best,
            diagnostic_state,
        )
        previous_global_best = (
            _SemanticLeanDiagnosticState(
                phase=semantic_diagnostic_best_phase,
                error_kind=semantic_diagnostic_best_error_kind,
                goal_count=(
                    semantic_diagnostic_best_goal_count
                    if semantic_diagnostic_best_goal_count >= 0
                    else None
                ),
                signature=semantic_diagnostic_best_signature,
            )
            if semantic_diagnostic_best_phase >= 0
            else None
        )
        diagnostic_progress_reason = _semantic_diagnostic_improvement(
            previous_global_best,
            diagnostic_state,
        )
        if diagnostic_state is not None and (
            previous_tool_best is None or tool_progress_reason
        ):
            semantic_diagnostic_best_by_tool[name] = diagnostic_state
        if diagnostic_state is not None and (
            previous_global_best is None or diagnostic_progress_reason
        ):
            semantic_diagnostic_best_phase = diagnostic_state.phase
            semantic_diagnostic_best_error_kind = diagnostic_state.error_kind
            semantic_diagnostic_best_goal_count = (
                diagnostic_state.goal_count
                if diagnostic_state.goal_count is not None
                else -1
            )
            semantic_diagnostic_best_signature = diagnostic_state.signature
        if diagnostic_progress_reason:
            # This is diagnostic progress, not proof evidence: it keeps a
            # demonstrably converging debugging sequence alive but never banks
            # a helper, closes a node, or marks the turn successful.
            consecutive_no_formal_progress = 0
            semantic_diagnostic_progress_count += 1
            semantic_diagnostic_last_reason = diagnostic_progress_reason
            _increment_tool_metric("mini_tool_semantic_diagnostic_progress", 1)
            return diagnostic_progress_reason

        consecutive_no_formal_progress += 1
        signature = _semantic_proof_tool_result_signature(
            name,
            result_text,
            candidate_identity=candidate_identity,
        )
        if signature:
            semantic_result_counts[signature] = (
                int(semantic_result_counts.get(signature, 0) or 0) + 1
            )
        repeated = bool(
            signature
            and semantic_result_counts.get(signature, 0) >= semantic_repeat_cap
        )
        exhausted = consecutive_no_formal_progress >= no_progress_cap
        if not (repeated or exhausted):
            return ""
        semantic_no_progress_detected = True
        semantic_no_progress_signature = signature
        semantic_no_progress_reason = (
            "repeated_semantic_lean_state" if repeated else "formal_progress_cap"
        )
        _increment_tool_metric("mini_tool_semantic_no_progress_detected", 1)
        return ""

    # One retry is scoped to this outer tool-loop turn, shared by tool-mode
    # and raw fallback provider calls.
    llm_retry_count = 0
    if goal_statement_override is not None:
        tool_goal_statement = str(goal_statement_override)
    else:
        tool_goal_statement = (
            _active_root_tool_goal_statement(dossier, conv)
            or str(getattr(conv, "goal_statement", "") or "")
        )

    def _messages_with_current_context(
        messages: Sequence[dict],
        *,
        validate_selected_context: bool = True,
    ) -> List[dict]:
        renderer = primitives["messages_with_search_context"]
        context_lemmas: List[str] = []
        feedback_lemmas = primitives.get("feedback_lemmas")
        if dossier is not None and callable(feedback_lemmas):
            context_lemmas = list(
                feedback_lemmas(
                    dossier.verified_helper_blocks(),
                    conv,
                )
            )
        try:
            rendered = list(
                renderer(
                    list(messages or ()),
                    dossier,
                    proof_state,
                    goal_statement=tool_goal_statement,
                    preamble=str(getattr(conv, "preamble", "") or ""),
                    context_lemmas=context_lemmas,
                    session_scope=session_scope,
                )
                or []
            )
        except TypeError:
            # Unit tests and old adapters may monkeypatch the legacy
            # three-argument shape. Keep that compatibility while the real
            # mini-prover renderer receives the current goal hash.
            rendered = list(
                renderer(list(messages or ()), dossier, proof_state) or []
            )
        if validate_selected_context:
            _validate_selected_proof_idea_dispatch_context(rendered, dossier)
        return rendered

    # The first snapshot is observability initialization. The request-path
    # invocation inside the outer exception boundary below performs the
    # authoritative immediately-before-dispatch validation.
    sent_messages = _messages_with_current_context(
        conv.messages_for_llm(),
        validate_selected_context=False,
    )

    def _set_repair_self_check_gap(*, budget_exhausted: bool = False) -> str:
        nonlocal repair_self_check_budget_exhausted, repair_self_check_status
        if budget_exhausted:
            repair_self_check_budget_exhausted = True
        if repair_self_check_seen:
            repair_self_check_status = "accepted"
        elif repair_self_check_attempted:
            repair_self_check_status = "no_accepted_try_lean"
        elif repair_self_check_status in non_verdict_repair_self_check_statuses:
            pass
        elif budget_exhausted:
            repair_self_check_status = "tool_budget_exhausted"
        else:
            repair_self_check_status = "no_try_lean_call"
        return repair_self_check_status

    def _set_repair_self_check_non_verdict_status(status: str) -> None:
        nonlocal repair_self_check_status
        if repair_self_check_seen or repair_self_check_attempted:
            return
        repair_self_check_status = _merge_repair_self_check_non_verdict_status(
            repair_self_check_status,
            status,
        )

    def _repair_self_check_gap_error(status: str) -> str:
        if _repair_self_check_non_verdict_is_compliant(status):
            return ""
        if status == "tool_budget_exhausted":
            return "repair_self_check_tool_budget_exhausted"
        if status == "no_try_lean_call":
            return "repair_self_check_no_try_lean_call"
        if (
            status in non_verdict_repair_self_check_statuses
            and repair_self_check_budget_exhausted
        ):
            return "repair_self_check_tool_budget_exhausted"
        if status in non_verdict_repair_self_check_statuses:
            return "repair_self_check_no_try_lean_call"
        return ""

    def _increment_tool_metric(key: str, amount: int = 1) -> None:
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

    def _compact_completed_in_turn_tool_history() -> None:
        """Bound complete old tool rounds without consuming a proof attempt."""

        nonlocal in_turn_tool_history_compactions
        nonlocal in_turn_tool_history_compacted_messages
        nonlocal in_turn_tool_history_compacted_tool_rounds
        nonlocal in_turn_tool_history_compacted_chars
        history = list(getattr(conv, "history", []) or [])
        complete_rounds = 0
        payload_chars = 0
        for index, message in enumerate(history):
            try:
                payload_chars += len(
                    json.dumps(message, ensure_ascii=False, default=str)
                )
            except Exception:
                payload_chars += len(str(message or ""))
            if message.get("role") != "assistant" or not message.get("tool_calls"):
                continue
            expected = {
                str(call.get("id", "") or "")
                for call in list(message.get("tool_calls") or ())
                if isinstance(call, Mapping)
            }
            if not expected or "" in expected:
                continue
            observed: set[str] = set()
            cursor = index + 1
            while cursor < len(history) and history[cursor].get("role") == "tool":
                observed.add(str(history[cursor].get("tool_call_id", "") or ""))
                cursor += 1
            if observed == expected:
                complete_rounds += 1
        if (
            complete_rounds < _IN_TURN_TOOL_HISTORY_COMPACT_AT_ROUNDS
            and (
                complete_rounds < 2
                or payload_chars < _IN_TURN_TOOL_HISTORY_COMPACT_AT_CHARS
            )
        ):
            return
        compact = getattr(conv, "compact_history_for_refine_handoff", None)
        if not callable(compact):
            return
        try:
            record = dict(
                compact(
                    keep_recent_tool_rounds=(
                        _IN_TURN_TOOL_HISTORY_KEEP_RECENT_ROUNDS
                    ),
                    force=True,
                    reason="in_turn_tool_history",
                )
                or {}
            )
        except Exception as exc:
            primitives["trace"](
                trace_prefix,
                "  in-turn tool history compaction failed: "
                f"{type(exc).__name__}: {exc}",
            )
            return
        removed_rounds = int(record.get("removed_tool_rounds", 0) or 0)
        try:
            compacted_payload_chars = sum(
                len(json.dumps(message, ensure_ascii=False, default=str))
                for message in list(getattr(conv, "history", []) or [])
            )
        except Exception:
            compacted_payload_chars = payload_chars
        reduced_chars = max(0, payload_chars - compacted_payload_chars)
        if removed_rounds <= 0 and reduced_chars <= 0:
            return
        removed_messages = int(record.get("removed_messages", 0) or 0)
        removed_chars = max(
            int(record.get("removed_chars", 0) or 0),
            reduced_chars,
        )
        in_turn_tool_history_compactions += 1
        in_turn_tool_history_compacted_messages += removed_messages
        in_turn_tool_history_compacted_tool_rounds += removed_rounds
        in_turn_tool_history_compacted_chars += removed_chars
        _increment_tool_metric("mini_in_turn_tool_history_compactions", 1)
        _increment_tool_metric(
            "mini_in_turn_tool_history_compacted_messages",
            removed_messages,
        )
        _increment_tool_metric(
            "mini_in_turn_tool_history_compacted_tool_rounds",
            removed_rounds,
        )
        _increment_tool_metric(
            "mini_in_turn_tool_history_compacted_chars",
            removed_chars,
        )
        primitives["trace"](
            trace_prefix,
            "  compacted completed in-turn tool history: "
            f"removed {removed_rounds} round(s), {removed_chars} chars; "
            f"kept latest {_IN_TURN_TOOL_HISTORY_KEEP_RECENT_ROUNDS} round(s)",
        )

    def _advance_chain_after_unusable_output() -> None:
        """Move a semantic-output retry to the next concrete provider."""

        nonlocal provider_chain_resume_target_id
        next_target = getattr(
            client,
            "provider_dispatch_next_resume_target_id",
            None,
        )
        if not callable(next_target):
            return
        try:
            target_id = str(next_target() or "").strip()
        except Exception:
            return
        if re.fullmatch(
            r"chain:[0-9a-f]{64}:target:[0-9]+",
            target_id,
        ):
            provider_chain_resume_target_id = target_id

    def _terminalize_retryable_unusable_output(reason: str) -> None:
        """Persist a semantic failure and move its retry to another leaf."""

        nonlocal llm_error, llm_failure_kind, llm_failure_reason
        nonlocal llm_retryable, llm_terminal
        clean_reason = str(reason or "").strip()
        _advance_chain_after_unusable_output()
        llm_error = clean_reason
        llm_failure_kind = clean_reason
        llm_failure_reason = clean_reason
        llm_retryable = True
        llm_terminal = False

    async def _provider_call_with_policy(
        *,
        invoke: Any,
        messages: Sequence[dict],
        call_kind: str,
        tools_for_cost: Sequence[dict] = (),
        max_tokens_override: Any = None,
        request_kind: str = "tool_search",
        reasoning_mode: str = "floor",
        reasoning_effort: str = "",
    ):
        nonlocal llm_retry_count, provider_quantum_cap_active
        nonlocal provider_chain_resume_target_id
        nonlocal invalid_prompt_neutralization_pending
        nonlocal provider_finalizer_continuation_active
        nonlocal provider_call_quantum_max_retries
        nonlocal provider_dispatches_started
        nonlocal provider_quantum_authenticated_dispatches_started
        nonlocal provider_dispatch_quantum_spent
        # A recursive helper may outlive its finite cancellation settlement
        # allowance.  Its copied Context retains the same mutable timeout
        # lease, so revocation here closes even raw-client dispatch paths that
        # were captured before the child was detached.
        require_hard_timeout_capability_active(
            f"Mini provider dispatch ({call_kind})"
        )
        provider_call_metadata = dict(temperature_metadata or {})
        provider_quantum_cap_active = False
        provider_finalizer_continuation_active = False
        provider_quantum_authenticated_dispatches_started = 0
        provider_dispatch_quantum_spent = False
        # Awaited authorization is required to refuse a retry immediately
        # before transport.  Apply the physical-dispatch ceiling to every
        # logical provider call, including finalization after tool work.  The
        # state-safe predicate governs whether exhaustion is reported as a
        # cooperative quantum yield; it must not disable the transport fence
        # itself.  Otherwise one finalizer can restart the client's complete
        # request timeout up to its internal retry count and monopolize a
        # recursive child for hours.  Opaque and legacy marker-only clients
        # keep their established behavior.
        finalizer_continuation = request_kind == "final_no_tools"
        if bool(
            getattr(client, "supports_transport_dispatch_authorization", False)
        ):
            # Final proof serialization has no unfinished tool dispatch. Retry
            # it through the durable scheduler continuation instead of
            # spending another full request window inside the same action.
            # Hard-policy general calls may spend their one bounded transport
            # retry inline. Soft, finalizer, and repair calls yield after one
            # exposure so an unavailable provider cannot monopolize a worker.
            hard_deadline_policy = (
                str(
                    getattr(
                        getattr(client, "cfg", None),
                        "llm_deadline_policy",
                        "soft",
                    )
                    or "soft"
                )
                .strip()
                .lower()
                == "hard"
            )
            dispatch_quantum = (
                1
                if repair_self_check_required or finalizer_continuation
                else (
                    _CONVERSATION_HARD_PROVIDER_DISPATCH_QUANTUM
                    if hard_deadline_policy
                    else _CONVERSATION_PROVIDER_DISPATCH_QUANTUM
                )
            )
            configured_dispatch_limit = int(
                provider_call_metadata.get("provider_dispatch_max_attempts", 0)
                or 0
            )
            provider_call_metadata["provider_dispatch_max_attempts"] = (
                min(
                    configured_dispatch_limit,
                    dispatch_quantum,
                )
                if configured_dispatch_limit > 0
                else dispatch_quantum
            )
            provider_quantum_cap_active = bool(
                (
                    configured_dispatch_limit <= 0
                    or configured_dispatch_limit > dispatch_quantum
                )
            )
        dispatch_attempt_limit = max(
            0,
            int(
                provider_call_metadata.get(
                    "provider_dispatch_max_attempts",
                    0,
                )
                or 0
            ),
        )
        provider_dispatch_lease = (
            ProviderDispatchAttemptLease(dispatch_attempt_limit)
            if dispatch_attempt_limit > 0
            else None
        )
        reported_authenticated_dispatches = 0
        provider_finalizer_continuation_active = bool(
            finalizer_continuation and provider_dispatch_lease is not None
        )

        def _capture_authenticated_dispatches() -> None:
            nonlocal provider_dispatches_started
            nonlocal provider_quantum_authenticated_dispatches_started
            nonlocal reported_authenticated_dispatches
            if provider_dispatch_lease is None:
                return
            authenticated_dispatches = int(
                provider_dispatch_lease.authenticated_dispatches_started
            )
            provider_dispatches_started += max(
                0,
                authenticated_dispatches - reported_authenticated_dispatches,
            )
            reported_authenticated_dispatches = max(
                reported_authenticated_dispatches,
                authenticated_dispatches,
            )
            provider_quantum_authenticated_dispatches_started = max(
                provider_quantum_authenticated_dispatches_started,
                authenticated_dispatches,
            )
        request_max_tokens_override = (
            max_tokens_override
            if max_tokens_override is not None
            else turn_max_tokens_override
        )
        if isinstance(
            request_max_tokens_override,
            MiniRequestEnvelopePolicy,
        ):
            request_max_tokens_override = (
                request_max_tokens_override.for_request(
                    request_kind=request_kind,
                    reasoning_mode=reasoning_mode,
                    reasoning_effort=reasoning_effort,
                )
            )
        _validate_selected_proof_idea_dispatch_context(messages, dossier)
        if isinstance(
            request_max_tokens_override,
            MiniRequestEnvelopePolicy,
        ):
            await resolve_mini_request_envelopes(
                client,
                request_max_tokens_override,
            )

        async def _invoke_with_meter(request_messages: Sequence[dict]):
            # Invalid-prompt rescue and same-turn retries each cross this
            # boundary. Re-resolve after every transform, immediately before
            # the metered transport invocation.
            require_hard_timeout_capability_active(
                f"Mini metered provider transport ({call_kind})"
            )
            _validate_selected_proof_idea_dispatch_context(
                request_messages,
                dossier,
            )

            def _retryable_exception_will_be_retried(exc: BaseException) -> bool:
                if _is_invalid_prompt_error(exc):
                    try:
                        return (
                            _neutralize_messages_for_invalid_prompt(
                                list(request_messages or ()),
                            )
                            != list(request_messages or ())
                        )
                    except Exception:
                        return False
                if isinstance(exc, ProviderDispatchAttemptLimitExceeded):
                    return False
                if llm_retry_count >= 1:
                    return False
                try:
                    if classify_llm_exception(exc).kind == "http_400_tool_transcript":
                        return False
                except Exception:
                    pass
                retryable = primitives.get(
                    "is_retryable_llm_exception",
                    lambda _exc: False,
                )
                try:
                    return bool(retryable(exc))
                except Exception:
                    return False

            with provider_dispatch_resume_target(
                provider_chain_resume_target_id
            ):
                return await _metered_or_plain_call_compat(
                    cost_controller=cost_controller,
                    client=client,
                    messages=list(request_messages or ()),
                    role=cost_role or str(getattr(conv, "role", "") or ""),
                    scope=cost_scope,
                    action_id=cost_action_id,
                    call_kind=call_kind,
                    tools=list(tools_for_cost or ()),
                    max_tokens_override=request_max_tokens_override,
                    metadata=provider_call_metadata,
                    retryable_exception_no_charge=(
                        _retryable_exception_will_be_retried
                    ),
                    provider_dispatch_lease=provider_dispatch_lease,
                    invoke=lambda usage_callback: invoke(
                        list(request_messages or ()),
                        usage_callback,
                        request_max_tokens_override,
                    ),
                )

        def _capture_chain_resume_target(exc: BaseException) -> None:
            nonlocal provider_chain_resume_target_id
            target_id = str(
                getattr(
                    exc,
                    "provider_dispatch_attempt_limit_target_id",
                    "",
                )
                or ""
            ).strip()
            if re.fullmatch(
                r"(?:target:[0-9]+|chain:[0-9a-f]{64}:target:[0-9]+)",
                target_id,
            ):
                provider_chain_resume_target_id = target_id

        request_messages = list(messages or ())
        if invalid_prompt_neutralization_pending:
            # Consume the durable rewrite cursor on this fresh scheduler
            # quantum. Required selected-work packets are preserved verbatim
            # by the neutralizer and are revalidated immediately pre-dispatch.
            invalid_prompt_neutralization_pending = False
            request_messages = _neutralize_messages_for_invalid_prompt(
                request_messages
            )

        def _persist_invalid_prompt_rescue() -> None:
            nonlocal invalid_prompt_neutralization_pending
            invalid_prompt_neutralization_pending = True

        try:
            try:
                result = await await_with_elapsed_budget(
                    _call_with_invalid_prompt_rescue(
                        invoke=_invoke_with_meter,
                        messages=request_messages,
                        trace=primitives["trace"],
                        trace_prefix=trace_prefix,
                        on_rescue=_persist_invalid_prompt_rescue,
                    ),
                    additional_deadline_monotonic=0.0,
                    additional_deadline_exception=(
                        _ProviderCumulativeWallExhausted
                    ),
                )
            except BaseException as retry_exc:
                _capture_chain_resume_target(retry_exc)
                if provider_dispatch_lease is not None:
                    _capture_authenticated_dispatches()
                    provider_dispatch_lease.annotate_exception(retry_exc)
                    provider_dispatch_quantum_spent = bool(
                        int(provider_dispatch_lease.max_attempts or 0) > 0
                        and int(
                            provider_dispatch_lease.provider_dispatches_started
                            or 0
                        )
                        >= int(provider_dispatch_lease.max_attempts or 0)
                    )
                raise
        except _TurnElapsedBudgetExhausted as exc:
            if provider_dispatch_lease is not None:
                _capture_authenticated_dispatches()
                provider_dispatch_lease.annotate_exception(exc)
            raise
        except RuntimeCapabilityRevokedError as exc:
            if provider_dispatch_lease is not None:
                _capture_authenticated_dispatches()
                provider_dispatch_lease.annotate_exception(exc)
            raise
        except Exception as exc:
            if provider_dispatch_lease is not None:
                _capture_authenticated_dispatches()
                provider_dispatch_lease.annotate_exception(exc)
            try:
                same_turn_retry_blocked = (
                    classify_llm_exception(exc).kind == "http_400_tool_transcript"
                    or bool(provider_defer_record_from_exception(client, exc))
                    or bool(
                        provider_dispatch_lease is not None
                        and int(provider_dispatch_lease.max_attempts or 0) > 0
                        and int(
                            provider_dispatch_lease.provider_dispatches_started
                            or 0
                        )
                        >= int(provider_dispatch_lease.max_attempts or 0)
                    )
                )
            except Exception:
                same_turn_retry_blocked = False
            if same_turn_retry_blocked:
                raise
            retryable = primitives.get("is_retryable_llm_exception", lambda _exc: False)
            try:
                should_retry = bool(retryable(exc))
            except Exception:
                should_retry = False
            if (
                isinstance(exc, ProviderDispatchAttemptLimitExceeded)
                or llm_retry_count >= 1
                or not should_retry
            ):
                raise
            llm_retry_count += 1
            safe_exc_type = _prompt_safe_inline_text(
                type(exc).__name__,
                limit=120,
                redact_solution_refs=redact_solution_refs,
            )
            safe_exc = _prompt_safe_inline_text(
                exc,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            )
            primitives["trace"](
                trace_prefix,
                "  transient LLM call failed; retrying the same mini-session turn "
                f"once ({safe_exc_type}: {safe_exc})",
            )
            try:
                result = await await_with_elapsed_budget(
                    _call_with_invalid_prompt_rescue(
                        invoke=_invoke_with_meter,
                        messages=request_messages,
                        trace=primitives["trace"],
                        trace_prefix=trace_prefix,
                        on_rescue=_persist_invalid_prompt_rescue,
                    ),
                    additional_deadline_monotonic=0.0,
                    additional_deadline_exception=(
                        _ProviderCumulativeWallExhausted
                    ),
                )
            except BaseException as retry_exc:
                _capture_chain_resume_target(retry_exc)
                if provider_dispatch_lease is not None:
                    _capture_authenticated_dispatches()
                    provider_dispatch_lease.annotate_exception(retry_exc)
                raise
        # If revocation raced an already-admitted transport, discard its late
        # response before tool-state application or any subsequent provider
        # request. Child cost/usage callbacks receive a separately revocable
        # controller facade.
        require_hard_timeout_capability_active(
            f"Mini provider response publication ({call_kind})"
        )
        _capture_authenticated_dispatches()
        provider_chain_resume_target_id = ""
        invalid_prompt_neutralization_pending = False
        return result

    provider_call_started = 0.0
    repeat_recovery_active = False
    repeat_recovery_provider_calls_before = 0

    def _restore_unsettled_repeat_recovery() -> None:
        nonlocal repeat_recovery_pending
        if (
            repeat_recovery_active
            and provider_calls_completed <= repeat_recovery_provider_calls_before
        ):
            repeat_recovery_pending = True

    try:
        while True:
            if provider_call_quantum_boundary_reached() and not llm_failure_kind:
                # Every completed generation and its complete tool batch is a
                # transaction boundary.  Repair/finalizer/repetition state is
                # persisted below, so those valuable paths no longer acquire
                # another synchronous provider request before the scheduler
                # can run independent mathematical work.
                record_provider_call_quantum_yield(boundary="provider/tool")
                break
            repeat_recovery_active = repeat_recovery_pending
            repeat_recovery_provider_calls_before = int(provider_calls_completed)
            repeat_recovery_pending = False
            if elapsed_budget_exhausted():
                record_elapsed_budget_exhausted()
                break
            if provider_cumulative_wall_exhausted():
                record_provider_cumulative_wall_exhausted()
                break
            current_messages = _messages_with_current_context(conv.messages_for_llm())
            sent_messages = list(current_messages or [])
            replaying_persisted_tool = bool(pending_tool_replay)
            replaying_paid_tool_retry = bool(
                replaying_persisted_tool
                and pending_tool_replay_is_paid_retry
            )
            replaying_durable_progress_tool = bool(
                replaying_persisted_tool
                and durable_progress_tool_replay_pending
            )
            provider_call_started = (
                0.0 if replaying_persisted_tool else time.monotonic()
            )
            can_call_tools = (
                replaying_persisted_tool
                or (
                    use_tools
                    and tool_calls_used < max_tool_calls_per_turn
                    and not force_finalize_without_tools
                )
            )
            response_data: Any = None
            finalizer_ignored_none_budget_exhausted = False
            raw_visible_reasoning_effort = mini_visible_output_reasoning_effort(
                client,
                default="",
            )
            if replaying_persisted_tool:
                replay_seed = list(pending_tool_replay)
                tool_calls = []
                for replay_index, replay_call in enumerate(replay_seed, 1):
                    normalized_call = dict(replay_call)
                    normalized_call["id"] = (
                        "replay_"
                        + str(tool_infrastructure_receipt_id or "receipt")[:24]
                        + f"_{replay_index}"
                    )
                    tool_calls.append(normalized_call)
                content = ""
                actual_messages = current_messages
            elif can_call_tools:
                (
                    (content, tool_calls),
                    actual_messages,
                    _rescued_invalid_prompt,
                ) = await _provider_call_with_policy(
                    invoke=lambda request_messages, usage_callback, max_tokens_override: call_with_optional_usage_callback(
                        client.chat_with_tools,
                        request_messages,
                        required_keywords=(
                            "reasoning_effort_override",
                            *(("max_tokens_override",) if max_tokens_override is not None else ()),
                        ),
                        tools=list(tools_list),
                        temperature_override=temperature_override,
                        reasoning_effort_override=(
                            mini_visible_output_reasoning_effort(
                                client,
                                default=MINI_TOOL_REASONING_EFFORT,
                            )
                        ),
                        usage_callback=usage_callback,
                        **provider_timeout_kwargs(),
                        **(
                            {"max_tokens_override": max_tokens_override}
                            if max_tokens_override is not None
                            else {}
                        ),
                    ),
                    messages=current_messages,
                    call_kind="chat_with_tools",
                    tools_for_cost=tools_list,
                    request_kind="tool_search",
                    reasoning_mode="floor",
                    reasoning_effort=MINI_TOOL_REASONING_EFFORT,
                )
                raw_tool_response = getattr(
                    client,
                    "last_raw_response_data",
                    {},
                )
                response_data = (
                    dict(raw_tool_response)
                    if isinstance(raw_tool_response, dict)
                    else None
                )
            elif use_tools and tools_list:
                # Finalization serializes the proof discovered during the
                # tool-guided phase.  Respect the action's already-budgeted
                # output allowance: silently clamping it to 4K truncated
                # valid visible Qwen output even with reasoning disabled.
                finalizer_max_tokens = (
                    mini_model_output_capacity(client)
                    if turn_max_tokens_override is None
                    else (
                        turn_max_tokens_override
                        if isinstance(
                            turn_max_tokens_override,
                            MiniRequestEnvelopePolicy,
                        )
                        else max(1, int(turn_max_tokens_override))
                    )
                )
                if should_use_raw_final_no_tools(client):
                    _increment_tool_metric(DEEPSEEK_FINAL_RAW_NO_TOOLS_METRIC)
                    raw_final_messages = toolless_final_messages(current_messages)
                    (
                        (content, response_data),
                        actual_messages,
                        _rescued_invalid_prompt,
                    ) = await _provider_call_with_policy(
                        invoke=lambda request_messages, usage_callback, max_tokens_override: call_with_optional_usage_callback(
                            client.chat_raw,
                            request_messages,
                            required_keywords=(
                                "max_tokens_override",
                                "reasoning_effort_override",
                            ),
                            temperature_override=temperature_override,
                            reasoning_effort_override=(
                                mini_bounded_visible_output_reasoning_effort(
                                    client,
                                    effort="low",
                                )
                            ),
                            usage_callback=usage_callback,
                            **provider_timeout_kwargs(),
                            max_tokens_override=max_tokens_override,
                        ),
                        messages=raw_final_messages,
                        call_kind="chat_raw_final_no_tools",
                        max_tokens_override=finalizer_max_tokens,
                        request_kind="final_no_tools",
                        reasoning_mode="bounded",
                        reasoning_effort="low",
                    )
                    tool_calls = []
                else:
                    (
                        (content, _ignored),
                        actual_messages,
                        _rescued_invalid_prompt,
                    ) = await _provider_call_with_policy(
                        invoke=lambda request_messages, usage_callback, max_tokens_override: call_with_optional_usage_callback(
                            client.chat_with_tools,
                            request_messages,
                            required_keywords=(
                                "max_tokens_override",
                                "reasoning_effort_override",
                            ),
                            tools=list(tools_list),
                            tool_choice="none",
                            temperature_override=temperature_override,
                            reasoning_effort_override=(
                                mini_bounded_visible_output_reasoning_effort(
                                    client,
                                    effort="low",
                                )
                            ),
                            usage_callback=usage_callback,
                            **provider_timeout_kwargs(),
                            max_tokens_override=max_tokens_override,
                        ),
                        messages=current_messages,
                        call_kind="chat_with_tools_none",
                        tools_for_cost=tools_list,
                        max_tokens_override=finalizer_max_tokens,
                        request_kind="final_no_tools",
                        reasoning_mode="bounded",
                        reasoning_effort="low",
                    )
                    raw_final_response = getattr(
                        client, "last_raw_response_data", {}
                    )
                    response_data = (
                        dict(raw_final_response)
                        if isinstance(raw_final_response, dict)
                        else None
                    )
                    ignored_tool_calls = list(_ignored or [])
                    if ignored_tool_calls:
                        _increment_tool_metric(
                            "mini_final_no_tools_provider_tool_calls_observed",
                            len(ignored_tool_calls),
                        )
                    if ignored_tool_calls and (
                        tool_calls_used >= max_tool_calls_per_turn
                    ) and _bankable_final_proof_content(content):
                        # No executable slot remains, but the visible content
                        # may still be a valid proof. Preserve it for the
                        # ordinary downstream Lean gate and terminate normally.
                        tool_calls = []
                    elif ignored_tool_calls and (
                        tool_calls_used >= max_tool_calls_per_turn
                    ):
                        # There is no executable slot left. Reissuing the same
                        # forced finalizer lets a provider that ignores
                        # tool_choice=none create an unbounded paid loop.
                        ignored_none_error = (
                            "final_no_tools_provider_ignored_"
                            "tool_choice_none_budget_exhausted"
                        )
                        _terminalize_retryable_unusable_output(
                            ignored_none_error
                        )
                        finalizer_ignored_none_budget_exhausted = True
                        tool_calls = []
                    else:
                        # Some OpenAI-compatible providers ignore
                        # ``tool_choice=none`` but return useful executable
                        # evidence. Always execute it while a real tool slot
                        # remains. Content parsing is recall-oriented and is
                        # not a validity gate, so even proof-looking prose may
                        # not suppress executable evidence. The mixed content
                        # remains in assistant history for the next finalizer.
                        tool_calls = ignored_tool_calls
                        if (
                            ignored_tool_calls
                            and _bankable_final_proof_content(content)
                        ):
                            banked_mixed_final_content = str(content or "")
                            banked_mixed_finalizer_pending = True
                            banked_mixed_finalizer_lane_identity = (
                                _provider_turn_lane_identity(
                                    conv,
                                    goal_statement_override,
                                )
                            )
            else:
                (
                    (content, response_data),
                    actual_messages,
                    _rescued_invalid_prompt,
                ) = await _provider_call_with_policy(
                    invoke=lambda request_messages, usage_callback, max_tokens_override: call_with_optional_usage_callback(
                        client.chat_raw,
                        request_messages,
                        required_keywords=(
                            *(
                                ("reasoning_effort_override",)
                                if raw_visible_reasoning_effort
                                else ()
                            ),
                            *(("max_tokens_override",) if max_tokens_override is not None else ()),
                        ),
                        temperature_override=temperature_override,
                        **(
                            {
                                "reasoning_effort_override":
                                raw_visible_reasoning_effort
                            }
                            if raw_visible_reasoning_effort
                            else {}
                        ),
                        usage_callback=usage_callback,
                        **provider_timeout_kwargs(),
                        **(
                            {"max_tokens_override": max_tokens_override}
                            if max_tokens_override is not None
                            else {}
                        ),
                    ),
                    messages=current_messages,
                    call_kind="chat_raw",
                    request_kind="raw_visible",
                    reasoning_mode="floor",
                    reasoning_effort="",
                )
                tool_calls = []
            if (
                can_call_tools
                and not tool_calls
                and use_tools
                and tools_list
                and is_deepseek_client(client)
            ):
                simple_xml_calls = extract_simple_xml_tool_calls(
                    content,
                    allowed_tool_names=tuple(
                        str((item.get("function") or {}).get("name", "") or "")
                        for item in tools_list
                        if isinstance(item, dict)
                    ),
                )
                if simple_xml_calls:
                    tool_calls = simple_xml_calls
                    _increment_tool_metric(
                        DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
                        1,
                    )
                    provider_protocol_event = (
                        "deepseek_simple_xml_tool_call_normalized"
                    )
                    provider_protocol_original_content = str(content or "")
            sent_messages = list(actual_messages or [])
            if not replaying_persisted_tool:
                provider_calls_completed += 1
                settled_provider_elapsed_s = max(
                    0.0,
                    time.monotonic() - provider_call_started,
                )
                provider_call_elapsed_s += settled_provider_elapsed_s
                provider_call_cumulative_elapsed_s += settled_provider_elapsed_s
                provider_call_started = 0.0
            if finalizer_ignored_none_budget_exhausted:
                # Settle telemetry before terminating this bounded finalizer.
                # The recursive lane ledger must see every provider call that
                # was actually paid for.
                break
            if elapsed_budget_exhausted():
                record_elapsed_budget_exhausted()
                break
            if not tool_calls:
                # A provider may end a tool-enabled round without making a
                # tool call even while Mini still has tool budget. That is
                # already a final-output boundary. Nonempty, nontruncated
                # content passes through unchanged, including text-encoded
                # tool protocols handled below.
                final_resolution = resolve_final_no_tools_output(
                    content=content,
                    raw_response=response_data,
                    client=client,
                    accepted_proof_codes=repair_self_check_codes,
                )
                if banked_mixed_final_content and (
                    final_resolution.error
                    or not _bankable_final_proof_content(
                        final_resolution.content
                    )
                ):
                    # The provider supplied a plausible term beside an ignored
                    # tool call. We executed the evidence instead of dropping
                    # it; if the follow-up finalizer is unusable, preserve the
                    # earlier term for the ordinary downstream Lean gate.
                    final_resolution = resolve_final_no_tools_output(
                        content=banked_mixed_final_content,
                        raw_response=None,
                        client=None,
                        accepted_proof_codes=repair_self_check_codes,
                    )
                    banked_mixed_final_content = ""
                    banked_mixed_finalizer_pending = False
                    banked_mixed_finalizer_lane_identity = ""
                content = final_resolution.content
                if final_resolution.event:
                    final_no_tools_event = final_resolution.event
                    final_no_tools_finish_reason = (
                        final_resolution.finish_reason
                    )
                    final_no_tools_reasoning_content_chars = int(
                        final_resolution.reasoning_content_chars or 0
                    )
                    final_no_tools_used_accepted_proof = bool(
                        final_resolution.used_accepted_proof
                    )
                    if final_resolution.metric_key:
                        _increment_tool_metric(final_resolution.metric_key)
                    primitives["trace"](
                        trace_prefix,
                        "  no-tool output resolved: "
                        f"{final_resolution.event}",
                    )
                if final_resolution.error:
                    if (
                        can_call_tools
                        and use_tools
                        and tools_list
                        and not final_no_tools_recovery_attempted
                    ):
                        if provider_call_quantum_boundary_reached():
                            # The visibility repair is a separate provider
                            # request. Persist that bounded continuation and
                            # yield after the settled response instead of
                            # letting a multi-minute transcript echo buy a
                            # second multi-minute call in the same action.
                            final_no_tools_visibility_recovery_pending = True
                            record_provider_call_quantum_yield(
                                boundary="visibility-recovery"
                            )
                            break
                        # A tool-capable high-reasoning request may elect to
                        # answer without a tool yet consume its whole visible
                        # allowance in private reasoning.  Retry that output
                        # boundary exactly once with tools disabled and the
                        # bounded visible-output effort.  This is a protocol
                        # recovery, not another proof-search/tool round.
                        final_no_tools_recovery_attempted = True
                        force_finalize_without_tools = True
                        final_no_tools_event = ""
                        final_no_tools_finish_reason = ""
                        final_no_tools_reasoning_content_chars = 0
                        final_no_tools_used_accepted_proof = False
                        content = ""
                        primitives["trace"](
                            trace_prefix,
                            "  retrying no-tool output once with bounded "
                            "visible-output reasoning",
                        )
                        continue
                    _terminalize_retryable_unusable_output(
                        final_resolution.error
                    )
                    break
                if (
                    use_tools
                    and tools_list
                    and should_use_raw_final_no_tools(client)
                ):
                    handling = handle_deepseek_dsml_after_budget(
                        client=client,
                        content=str(content or ""),
                        already_reprompted=deepseek_dsml_reprompted_after_budget,
                    )
                    banked_final_override = False
                    if handling.changed and repair_self_check_codes:
                        banked_resolution = resolve_final_no_tools_output(
                            content="",
                            raw_response=response_data,
                            client=client,
                            accepted_proof_codes=repair_self_check_codes,
                        )
                        if banked_resolution.used_accepted_proof:
                            content = banked_resolution.content
                            final_no_tools_event = banked_resolution.event
                            final_no_tools_finish_reason = (
                                banked_resolution.finish_reason
                            )
                            final_no_tools_reasoning_content_chars = int(
                                banked_resolution.reasoning_content_chars or 0
                            )
                            final_no_tools_used_accepted_proof = True
                            if banked_resolution.metric_key:
                                _increment_tool_metric(
                                    banked_resolution.metric_key
                                )
                            banked_final_override = True
                            primitives["trace"](
                                trace_prefix,
                                "  final no-tools pseudo-tool output replaced "
                                "with current-turn Lean-accepted proof",
                            )
                    if handling.changed and not banked_final_override:
                        _increment_tool_metric(
                            handling.content_metric_key
                            or DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC
                        )
                        if handling.metric_key:
                            _increment_tool_metric(handling.metric_key)
                        provider_protocol_event = handling.event
                        provider_protocol_original_content = handling.original_content
                        content = handling.content
                        primitives["trace"](
                            trace_prefix,
                            f"  DeepSeek final tool content handled: {handling.event}",
                        )
                        if handling.should_reprompt:
                            # Bootstrap before the direct append: once history
                            # is non-empty, messages_for_llm() stops
                            # synthesizing the initial problem statement, so
                            # appending to an empty history here would erase
                            # the problem from every later LLM call.
                            conv.ensure_bootstrap()
                            conv.history.append(
                                {"role": "user", "content": handling.feedback}
                            )
                            deepseek_dsml_reprompted_after_budget = True
                            content = ""
                            continue
                        if handling.event.endswith("_repeated"):
                            _terminalize_retryable_unusable_output(
                                "deepseek_tool_after_budget"
                            )
                            content = ""
                            break
                forbidden_final_command = (
                    _find_forbidden_lean_command([], str(content or ""))
                    if use_tools and tools_list and is_deepseek_client(client)
                    else None
                )
                if forbidden_final_command is not None:
                    if not final_no_tools_policy_reprompted:
                        conv.ensure_bootstrap()
                        conv.history.append(
                            {
                                "role": "user",
                                "content": (
                                    "The previous final response used a top-level "
                                    f"Lean `{forbidden_final_command}` command, which "
                                    "is not an executable artifact for this turn. Do "
                                    "not inspect the environment or leave placeholders. "
                                    + _final_submission_shape_instruction(
                                        require_declaration=(
                                            try_lean_require_declaration
                                        )
                                    )
                                ),
                            }
                        )
                        final_no_tools_policy_reprompted = True
                        final_no_tools_event = (
                            "final_no_tools_policy_recovery_pending"
                        )
                        content = ""
                        continue
                    _terminalize_retryable_unusable_output(
                        "final_no_tools_forbidden_command"
                    )
                    final_no_tools_event = str(llm_error or "")
                    content = ""
                    break
                if (
                    repair_self_check_required
                    and not repair_self_check_seen
                    and not _repair_self_check_non_verdict_is_compliant(
                        repair_self_check_status
                    )
                ):
                    helper_only_decomposition = False
                    helper_only_checker = primitives.get(
                        "repair_content_is_helper_only_decomposition"
                    )
                    if callable(helper_only_checker):
                        try:
                            helper_only_decomposition = bool(
                                helper_only_checker(
                                    content,
                                    theorem_name=str(
                                        getattr(dossier, "theorem_name", "") or ""
                                    ),
                                )
                            )
                        except Exception:
                            helper_only_decomposition = False
                    if helper_only_decomposition:
                        repair_self_check_helper_only_allowed = True
                        repair_self_check_status = "helper_only_decomposition"
                        break
                    if (
                        not repair_self_check_attempted
                        and not repair_self_check_reminder_sent
                        and can_call_tools
                    ):
                        conv.ensure_bootstrap()
                        message_fn = primitives.get(
                            "repair_self_check_required_message",
                            lambda **_kw: "Repair self-check required.",
                        )
                        reminder = message_fn(
                            require_try_lean=try_lean_tool_enabled,
                            require_declaration=try_lean_require_declaration,
                            role=str(getattr(conv, "role", "") or "prove"),
                        )
                        conv.history.append(
                            {
                                "role": "user",
                                "content": reminder,
                            }
                        )
                        repair_self_check_reminder_sent = True
                        content = ""
                        continue
                    status = _set_repair_self_check_gap(
                        budget_exhausted=not can_call_tools
                    )
                    if status == "tool_budget_exhausted":
                        llm_error = "repair_self_check_tool_budget_exhausted"
                    elif status == "no_try_lean_call":
                        llm_error = "repair_self_check_no_try_lean_call"
                if not final_resolution.event:
                    if final_no_tools_policy_reprompted:
                        final_no_tools_event = (
                            "final_no_tools_policy_recovery_succeeded"
                        )
                    elif deepseek_dsml_reprompted_after_budget:
                        final_no_tools_event = (
                            "final_no_tools_protocol_recovery_succeeded"
                        )
                    elif final_no_tools_recovery_attempted:
                        final_no_tools_event = (
                            "final_no_tools_visibility_recovery_succeeded"
                        )
                    if final_no_tools_event:
                        final_no_tools_finish_reason = (
                            final_resolution.finish_reason
                        )
                        final_no_tools_reasoning_content_chars = int(
                            final_resolution.reasoning_content_chars or 0
                        )
                break

            round_call_signatures = [
                sig for sig in (_tool_call_signature(tc) for tc in tool_calls) if sig
            ]
            repeated_signatures = {
                sig
                for sig in round_call_signatures
                if sig in seen_tool_call_signatures
            }
            repeated_accepted_signature = next(
                (
                    signature
                    for signature in round_call_signatures
                    if signature in accepted_try_lean_receipts
                ),
                "",
            )
            accepted_repeat_only_batch = bool(
                repeated_accepted_signature
                and len(round_call_signatures) == len(tool_calls)
                and all(
                    signature in accepted_try_lean_receipts
                    for signature in round_call_signatures
                )
            )
            if accepted_repeat_only_batch:
                # The exact code and tool identity were already accepted by
                # Lean in this turn. Re-running the kernel or buying a third
                # provider call cannot add evidence and can only lose the
                # paid receipt to cancellation/transport failure.
                tool_repeat_detected = True
                tool_repeat_signature = repeated_accepted_signature
                tool_repeat_action = "reuse_accepted_try_lean"
                content = accepted_try_lean_receipts[
                    repeated_accepted_signature
                ]
                final_no_tools_event = "accepted_try_lean_exact_repeat_reused"
                final_no_tools_used_accepted_proof = True
                _increment_tool_metric(
                    "mini_final_no_tools_accepted_proof_fallbacks",
                    1,
                )
                break
            if repeated_signatures:
                tool_repeat_detected = True
                tool_repeat_signature = sorted(repeated_signatures)[0]
                novel_tool_calls = [
                    tc
                    for tc in tool_calls
                    if _tool_call_signature(tc) not in repeated_signatures
                ]
                repeated_count = max(1, len(tool_calls) - len(novel_tool_calls))
                _increment_tool_metric("tool_repeated_calls", repeated_count)
                if novel_tool_calls:
                    tool_repeat_action = "dropped_repeated_calls"
                    tool_calls = novel_tool_calls
                    primitives["trace"](
                        trace_prefix,
                        "  tool loop: dropped already-seen tool call(s) and "
                        f"kept {len(novel_tool_calls)} novel call(s)",
                    )
                elif not repeat_guidance_used and not repeat_recovery_active:
                    repeat_guidance_used = True
                    repeat_recovery_pending = True
                    tool_repeat_action = "guided_retry"
                    _increment_tool_metric("tool_repeat_guidance_rounds", 1)
                    conv.ensure_bootstrap()
                    conv.history.append(
                        _user_history_message(
                            (
                                "You already made this exact tool call. Do not "
                                "repeat it. Either make a meaningfully different "
                                "tool call that checks new information, or use the "
                                "tool results already present and submit the Lean "
                                "proof attempt now."
                            ),
                            repair_semantics=_REPAIR_CONTINUATION,
                        )
                    )
                    primitives["trace"](
                        trace_prefix,
                        "  tool loop: repeated call detected; requesting a "
                        "different tool step",
                    )
                    continue
                else:
                    force_finalize_without_tools = True
                    tool_repeat_action = "force_finalize"
                    _increment_tool_metric("tool_repeat_forced_finalize", 1)
                    conv.ensure_bootstrap()
                    conv.history.append(
                        _user_history_message(
                            (
                                "You repeated a tool call after correction. Tools are "
                                "now disabled for this attempt. Use the results already "
                                "present and write the active Lean artifact now. "
                                + _final_submission_shape_instruction(
                                    require_declaration=try_lean_require_declaration
                                )
                            ),
                            repair_semantics=_REPAIR_CONTINUATION,
                        )
                    )
                    primitives["trace"](
                        trace_prefix,
                        "  tool loop: repeated call detected after correction; "
                        "forcing no-tools finalization",
                    )
                    continue

            batch_duplicate_dropped = 0
            if tool_calls and not replaying_durable_progress_tool:
                unique_tool_calls: List[dict] = []
                selected_signatures: set[str] = set()
                for tc in tool_calls:
                    sig = _tool_call_signature(tc)
                    if sig and sig in selected_signatures:
                        batch_duplicate_dropped += 1
                        continue
                    if sig:
                        selected_signatures.add(sig)
                    unique_tool_calls.append(tc)
                if batch_duplicate_dropped:
                    tool_calls = unique_tool_calls
                    _increment_tool_metric(
                        "tool_repeated_calls",
                        batch_duplicate_dropped,
                    )
                    primitives["trace"](
                        trace_prefix,
                        "  tool loop: dropped duplicate tool call(s) from the "
                        f"same batch ({batch_duplicate_dropped})",
                    )

            budget_remaining = (
                len(tool_calls)
                if replaying_persisted_tool
                else max(0, max_tool_calls_per_turn - tool_calls_used)
            )
            selector = primitives.get("select_tool_calls_for_repair_budget")
            if replaying_durable_progress_tool:
                # These calls were already authenticated, capacity-validated,
                # and paid for by a durable cutpoint. Repair-turn selection is
                # for new model proposals; applying it here can silently drop
                # formal calls after the first verifier.
                calls_to_run = list(tool_calls)
                dropped = 0
                reserved_for_try_lean = False
            elif callable(selector):
                (
                    calls_to_run,
                    dropped,
                    reserved_for_try_lean,
                ) = selector(
                    tool_calls,
                    budget_remaining,
                    repair_self_check_required=repair_self_check_required,
                    repair_self_check_seen=repair_self_check_seen,
                    repair_self_check_attempted=repair_self_check_attempted,
                    repair_discovery_calls_used=(
                        _REPAIR_DISCOVERY_TOOL_CALL_QUOTA
                        if repair_discovery_quota_exhausted
                        else repair_discovery_tool_calls_used
                    ),
                )
            else:
                calls_to_run = list(tool_calls[:budget_remaining])
                dropped = len(tool_calls) - len(calls_to_run)
                reserved_for_try_lean = False
            # A cadence-rejected search does not spend the remaining tool
            # budget, but the batch selector runs before dispatch. Without
            # this reservation, a search placed just before a formal call can
            # occupy the final selected slot, be skipped, and strand the only
            # call capable of resetting the persisted cadence counter.
            selected_tool_names = {
                str((call.get("function") or {}).get("name") or "")
                for call in calls_to_run
                if isinstance(call, Mapping)
            }
            if (
                not replaying_durable_progress_tool
                and formal_cadence_available
                and search_cadence_cap > 0
                and consecutive_search_tool_calls >= search_cadence_cap
                and budget_remaining > 0
                and not selected_tool_names & _FORMAL_CADENCE_TOOL_NAMES
            ):
                formal_candidate = next(
                    (
                        call
                        for call in tool_calls
                        if isinstance(call, Mapping)
                        and str(
                            (call.get("function") or {}).get("name") or ""
                        )
                        in _FORMAL_CADENCE_TOOL_NAMES
                    ),
                    None,
                )
                replace_index = next(
                    (
                        index
                        for index in range(len(calls_to_run) - 1, -1, -1)
                        if str(
                            (
                                (calls_to_run[index].get("function") or {})
                                if isinstance(calls_to_run[index], Mapping)
                                else {}
                            ).get("name")
                            or ""
                        )
                        in _SEARCH_CADENCE_TOOL_NAMES
                    ),
                    -1,
                )
                if formal_candidate is not None and replace_index >= 0:
                    calls_to_run = list(calls_to_run)
                    calls_to_run[replace_index] = formal_candidate
            call_signatures = [
                sig for sig in (_tool_call_signature(tc) for tc in calls_to_run) if sig
            ]

            if (
                reserved_for_try_lean
                and not calls_to_run
                and not repair_self_check_attempted
            ):
                conv.ensure_bootstrap()
                allow_repeat_recovery_final_slot = bool(
                    repeat_recovery_active
                    and not repair_self_check_final_slot_recovery_reminder_sent
                )
                if not repair_self_check_reminder_sent or allow_repeat_recovery_final_slot:
                    message_fn = primitives.get(
                        "repair_self_check_required_message",
                        lambda **_kw: "Repair self-check required.",
                    )
                    if repair_self_check_reminder_sent:
                        reminder_message = _user_history_message(
                            (
                                "The remaining repair tool slot is reserved for "
                                "`try_lean`. Do not call other tools now; call "
                                "`try_lean` on the revised "
                                + (
                                    "complete named declaration."
                                    if try_lean_require_declaration
                                    else "proof."
                                )
                            ),
                            repair_semantics=_REPAIR_CONTINUATION,
                        )
                    else:
                        reminder = message_fn(
                            require_try_lean=try_lean_tool_enabled,
                            require_declaration=try_lean_require_declaration,
                            role=str(getattr(conv, "role", "") or "prove"),
                        )
                        reminder_message = {"role": "user", "content": reminder}
                        repair_self_check_reminder_sent = True
                    conv.history.append(reminder_message)
                    if allow_repeat_recovery_final_slot:
                        repeat_recovery_pending = True
                        repair_self_check_final_slot_recovery_reminder_sent = True
                    content = ""
                    primitives["trace"](
                        trace_prefix,
                        "  reserved final repair tool slot for try_lean; "
                        "dropped non-self-check tool call(s)",
                    )
                    continue
                _set_repair_self_check_gap()
                llm_error = "repair_self_check_no_try_lean_call"
                break

            conv.ensure_bootstrap()

            # Append the assistant's tool-call message containing only the
            # calls we'll actually execute (B1 invariant).
            batch_search_cadence_skipped = False
            batch_formal_cadence_requested = False
            assistant_tool_content = (
                ""
                if repair_self_check_required
                and not repair_self_check_attempted
                and not repair_self_check_seen
                else content or ""
            )

            used_tool_call_ids: set[str] = set()
            safe_tool_call_ids: List[str] = []

            def unique_tool_call_id(tc: Mapping[str, Any], index: int) -> str:
                raw_id = tc.get("id", "") if isinstance(tc, Mapping) else ""
                base = str(prompt_safe_tool_call_token(raw_id)).strip()
                if not base:
                    base = f"call_{turn}_{tool_calls_used + index + 1}"
                candidate = base
                suffix = 2
                while candidate in used_tool_call_ids:
                    candidate = f"{base}_{suffix}"
                    suffix += 1
                used_tool_call_ids.add(candidate)
                safe_tool_call_ids.append(candidate)
                return candidate

            def advertised_tool_call(tc: Mapping[str, Any], index: int) -> dict:
                fn = tc.get("function") or {}
                return {
                    "id": unique_tool_call_id(tc, index),
                    "type": "function",
                    "function": {
                        "name": str(
                            prompt_safe_tool_name_token(
                                fn.get("name", "") or ""
                            )
                        ),
                        "arguments": str(
                            prompt_safe_tool_arguments(
                                fn.get("arguments", None)
                                if "arguments" in fn
                                else None
                            )
                        ),
                    },
                }

            exact_openrouter_message = _openrouter_exact_continuation_message(
                client=client,
                response_data=response_data,
                calls_to_run=calls_to_run,
            )
            if exact_openrouter_message is not None:
                assistant_message = exact_openrouter_message
                advertised_tool_calls = assistant_message["tool_calls"]
                for call in advertised_tool_calls:
                    call_id = str(call.get("id") or "")
                    used_tool_call_ids.add(call_id)
                    safe_tool_call_ids.append(call_id)
            else:
                advertised_tool_calls = [
                    advertised_tool_call(tc, index)
                    for index, tc in enumerate(calls_to_run)
                ]
                assistant_message = {
                    "role": "assistant",
                    "content": assistant_tool_content,
                    "tool_calls": advertised_tool_calls,
                }
                cfg = getattr(client, "cfg", None)
                raw_openrouter_message = bool(
                    base_url_matches_provider(
                        str(getattr(cfg, "base_url", "") or ""),
                        "openrouter",
                    )
                    and isinstance(response_data, dict)
                    and isinstance(response_data.get("choices"), list)
                    and response_data.get("choices")
                    and isinstance(response_data["choices"][0], dict)
                    and isinstance(
                        response_data["choices"][0].get("message"),
                        dict,
                    )
                    and (
                        "reasoning_content"
                        in response_data["choices"][0]["message"]
                        or "reasoning"
                        in response_data["choices"][0]["message"]
                        or "reasoning_details"
                        in response_data["choices"][0]["message"]
                    )
                )
                reasoning_content = response_reasoning_text(response_data)
                if reasoning_content and not raw_openrouter_message:
                    # Direct DeepSeek requires this exact field on every
                    # continuation of a thinking-mode tool-call turn. An
                    # incomplete OpenRouter batch cannot reuse structured
                    # reasoning: flattening it onto reconstructed calls would
                    # forge a continuation the provider never authored.
                    assistant_message["reasoning_content"] = reasoning_content
                reasoning_items = response_reasoning_items(response_data)
                if reasoning_items:
                    assistant_message["_responses_reasoning_items"] = reasoning_items
                output_items = response_output_items(response_data)
                if output_items and _responses_output_matches_advertised_tool_calls(
                    output_items,
                    advertised_tool_calls,
                ):
                    assistant_message["_responses_output_items"] = output_items
            _bind_provider_continuation_policy_receipt(assistant_message, conv)
            conv.history.append(assistant_message)

            # Per-tc dispatch — B1 + Bonus #1 invariants preserved.
            for index, tc in enumerate(calls_to_run):
                fn = tc.get("function") or {}
                name = str(fn.get("name", "") or "")
                safe_log_name = prompt_safe_tool_name_token(name)
                safe_tcid = safe_tool_call_ids[index]
                raw_arg_value = fn.get("arguments", None) if "arguments" in fn else None
                raw_args = "" if raw_arg_value is None else str(raw_arg_value)
                completed_target_banked = bool(
                    accepted_exact_target_code
                    or any(
                        status in {"closed", "root_finalized"}
                        for status in tool_state_update_statuses
                    )
                )
                durable_progress_banked = bool(
                    accepted_try_lean_helper_names
                    or tool_state_update_statuses
                )
                root_closing_tool = name in _DURABLE_PROGRESS_ROOT_TOOL_NAMES
                if completed_target_banked or durable_progress_banked:
                    replay_capacity = max(
                        0,
                        max(0, int(max_tool_calls_per_turn or 0))
                        - int(tool_calls_used or 0),
                    )
                    if (
                        not completed_target_banked
                        and root_closing_tool
                        and len(pending_tool_replay) < replay_capacity
                    ):
                        pending_signature = _tool_call_signature(tc)
                        if pending_signature and all(
                            _tool_call_signature(pending_call)
                            != pending_signature
                            for pending_call in pending_tool_replay
                        ):
                            pending_tool_replay.append(dict(tc))
                            pending_tool_replay_is_paid_retry = False
                            durable_progress_tool_replay_pending = True
                    result_text = (
                        f"{safe_log_name} skipped: durable formal progress "
                        "was already banked in this provider batch."
                    )
                    conv.history.append(
                        {
                            "role": "tool",
                            "tool_call_id": safe_tcid,
                            "content": result_text,
                        }
                    )
                    tool_call_log.append(
                        {
                            "name": safe_log_name,
                            "tool_call_id": safe_tcid,
                            "args": {},
                            "result_preview": result_text[:400],
                            "skipped_reason": "durable_progress_cutpoint",
                            "protocol_attempted": False,
                            "json_parsed": False,
                            "raw_arguments_length": len(raw_args),
                            "raw_arguments_sha256": hashlib.sha256(
                                raw_args.encode("utf-8", errors="replace")
                            ).hexdigest(),
                            "result_length": len(result_text),
                            "result_sha256": hashlib.sha256(
                                result_text.encode("utf-8", errors="replace")
                            ).hexdigest(),
                        }
                    )
                    continue
                if elapsed_budget_exhausted():
                    record_elapsed_budget_exhausted()
                    if replaying_persisted_tool and not pending_tool_replay:
                        # Selection dequeues the exact replay before dispatch.
                        # A scheduler deadline is not a Lean launch, so retain
                        # the unspent entitlement and every call not yet run.
                        pending_tool_replay = [
                            dict(call) for call in calls_to_run[index:]
                        ]
                        pending_tool_replay_is_paid_retry = bool(
                            replaying_paid_tool_retry
                        )
                    result_text = (
                        f"{safe_log_name} skipped: "
                        "llm_turn_elapsed_budget_exhausted before this "
                        "advertised tool call could run."
                    )
                    conv.history.append(
                        {
                            "role": "tool",
                            "tool_call_id": safe_tcid,
                            "content": result_text,
                        }
                    )
                    skipped_record = {
                        "name": safe_log_name,
                        "tool_call_id": safe_tcid,
                        "args": {},
                        "result_preview": result_text[:400],
                        "skipped_reason": "llm_turn_elapsed_budget_exhausted",
                        "protocol_attempted": False,
                        "json_parsed": False,
                        "raw_arguments_length": len(raw_args),
                        "raw_arguments_sha256": hashlib.sha256(
                            raw_args.encode("utf-8", errors="replace")
                        ).hexdigest(),
                        "result_length": len(result_text),
                        "result_sha256": hashlib.sha256(
                            result_text.encode("utf-8", errors="replace")
                        ).hexdigest(),
                    }
                    if name == "compute_examples":
                        skipped_record.update(
                            runner_invoked=False,
                            execution_status="not_dispatched",
                        )
                    tool_call_log.append(skipped_record)
                    primitives["trace"](
                        trace_prefix,
                        f"  {safe_log_name} skipped: elapsed budget exhausted",
                    )
                    continue
                if replaying_persisted_tool and pending_tool_replay:
                    # A persisted entitlement remains durable throughout
                    # message preparation and selection. Dequeue only this
                    # call at its dispatch boundary. Untouched later calls
                    # remain owned even if this call consumes the turn lease.
                    pending_tool_replay = [
                        dict(call) for call in calls_to_run[index + 1 :]
                    ]
                    pending_tool_replay_is_paid_retry = bool(
                        replaying_paid_tool_retry and pending_tool_replay
                    )
                    durable_progress_tool_replay_pending = bool(
                        replaying_durable_progress_tool and pending_tool_replay
                    )
                args, args_parse_error = parse_tool_arguments(raw_arg_value)
                if name in _FORMAL_CADENCE_TOOL_NAMES and not args_parse_error:
                    # An infrastructure deferral of a well-formed formal call
                    # is not refusal to follow cadence guidance.
                    batch_formal_cadence_requested = True
                tool_call_started = time.monotonic()
                promoted_state_status: Optional[str] = None
                compute_runner_invoked = False
                search_runner_invoked = False
                formal_runner_invoked = False
                runner_raised = False
                runner_deferred_before_launch = False
                search_cadence_skipped = False
                accepted_try_lean_code = ""

                async def invoke_formal_runner(
                    runner: Callable[..., Any], *runner_args: Any, **runner_kwargs: Any
                ) -> Any:
                    nonlocal formal_runner_invoked
                    formal_runner_invoked = True
                    return await runner(*runner_args, **runner_kwargs)

                try:
                    if args_parse_error:
                        if name == "try_lean" and try_lean_tool_enabled:
                            _set_repair_self_check_non_verdict_status(
                                "try_lean_malformed_arguments"
                            )
                        result_text = (
                            f"{prompt_safe_tool_name_token(name)} error: malformed "
                            "JSON arguments; pass a JSON object matching the tool "
                            f"schema. Parse error: {args_parse_error}"
                        )
                    elif (
                        name in _SEARCH_CADENCE_TOOL_NAMES
                        and formal_cadence_available
                        and search_cadence_cap > 0
                        and consecutive_search_tool_calls >= search_cadence_cap
                    ):
                        search_cadence_skipped = True
                        batch_search_cadence_skipped = True
                        _increment_tool_metric(
                            "mini_tool_search_cadence_skips",
                            1,
                        )
                        result_text = (
                            f"{prompt_safe_tool_name_token(name)} skipped: "
                            "the retrieval cadence is exhausted. Make a formal "
                            "proof attempt before requesting more searches."
                        )
                    elif name == "search_mathlib" and searcher is not None:
                        run_search_tool = primitives["run_search_tool"]
                        shared_metrics = (
                            getattr(dossier, "tool_metrics", None)
                            if dossier is not None
                            else None
                        )

                        def run_search(metric_sink: Any) -> str:
                            nonlocal search_runner_invoked
                            search_runner_invoked = True
                            try:
                                return run_search_tool(
                                    searcher,
                                    args,
                                    known_decl_names=getattr(
                                        conv, "known_premise_names", []
                                    ),
                                    local_decl_names=_local_decl_names_for_search(
                                        dossier,
                                        conv,
                                    ),
                                    metric_sink=metric_sink,
                                    deadline_exhausted=(
                                        elapsed_budget_exhausted
                                        if max_turn_elapsed_f > 0.0
                                        else None
                                    ),
                                )
                            except TypeError as exc:
                                if (
                                    "known_decl_names" not in str(exc)
                                    and "local_decl_names" not in str(exc)
                                    and "metric_sink" not in str(exc)
                                    and "deadline_exhausted" not in str(exc)
                                ):
                                    raise
                                # Older unit-test primitives are intentionally
                                # tiny two-argument callables. Keep the
                                # production path context-rich without making
                                # those tests emulate every optional keyword.
                                return run_search_tool(searcher, args)

                        if max_turn_elapsed_f > 0.0:
                            baseline_metrics = (
                                dict(shared_metrics)
                                if isinstance(shared_metrics, dict)
                                else {}
                            )
                            isolated_metrics = dict(baseline_metrics)
                            result_text = await await_with_elapsed_budget(
                                _run_sync_abandonment_safe(
                                    lambda: run_search(isolated_metrics)
                                )
                            )
                            if elapsed_budget_exhausted():
                                raise _TurnElapsedBudgetExhausted()
                            if isinstance(shared_metrics, dict):
                                changed_metric_keys = set(baseline_metrics) | set(
                                    isolated_metrics
                                )
                                previous_metrics = {
                                    key: shared_metrics.get(key)
                                    for key in changed_metric_keys
                                }
                                for key in changed_metric_keys:
                                    delta = int(isolated_metrics.get(key, 0) or 0) - int(
                                        baseline_metrics.get(key, 0) or 0
                                    )
                                    if delta:
                                        shared_metrics[key] = int(
                                            shared_metrics.get(key, 0) or 0
                                        ) + delta
                                if elapsed_budget_exhausted():
                                    for key, previous in previous_metrics.items():
                                        if previous is None:
                                            shared_metrics.pop(key, None)
                                        else:
                                            shared_metrics[key] = previous
                                    raise _TurnElapsedBudgetExhausted()
                        else:
                            # Keep the search on a detached worker so a stuck
                            # GPU/index lock cannot freeze the event loop.
                            # Do not invent a shorter search budget than the
                            # searcher already advertises; omit the timeout
                            # when none is configured so a slow hit still
                            # returns.
                            #
                            # The searcher bounds *itself* at that same value
                            # and degrades gracefully there: adapters past the
                            # deadline report "timeout" and fusion still
                            # returns whatever landed. Arming the identical
                            # value out here made this abandonment guard race
                            # that graceful return and usually win, so a
                            # partially-successful search was reported as a
                            # crashed tool and its premises were lost. This
                            # guard exists only to catch a searcher that never
                            # returns at all, so give the searcher's own
                            # deadline room to land first.
                            raw_search_timeout = getattr(
                                searcher,
                                "operation_timeout_s",
                                None,
                            )
                            search_timeout_s = None
                            try:
                                if raw_search_timeout is not None:
                                    parsed_search_timeout = float(
                                        raw_search_timeout
                                    )
                                    if parsed_search_timeout > 0.0:
                                        search_timeout_s = (
                                            parsed_search_timeout
                                            + _SEARCH_ABANDONMENT_MARGIN_S
                                        )
                            except (TypeError, ValueError):
                                search_timeout_s = None
                            result_text = await _run_sync_abandonment_safe(
                                lambda: run_search(shared_metrics),
                                timeout_s=search_timeout_s,
                            )
                    elif name == "search_theorems" and hasattr(
                        searcher, "static_mathlib_searcher"
                    ):
                        run_federated_search = primitives[
                            "run_search_theorems_tool"
                        ]
                        accepted_result_out: dict[str, Any] = {}

                        def invoke_federated_search() -> str:
                            nonlocal search_runner_invoked
                            search_runner_invoked = True
                            try:
                                return run_federated_search(
                                    searcher,
                                    args,
                                    goal_state=tool_goal_statement,
                                    deadline_exhausted=(
                                        elapsed_budget_exhausted
                                        if max_turn_elapsed_f > 0.0
                                        else None
                                    ),
                                    accepted_result_out=accepted_result_out,
                                )
                            except TypeError as exc:
                                if (
                                    "deadline_exhausted" not in str(exc)
                                    and "accepted_result_out" not in str(exc)
                                    and "goal_state" not in str(exc)
                                ):
                                    raise
                                return run_federated_search(searcher, args)

                        # The absence of a turn-wide deadline must not remove
                        # the per-operation watchdog. Federated backends may
                        # block on an embedding provider or index lock, so the
                        # synchronous compatibility tool always runs behind an
                        # abandonment-safe worker boundary.
                        if max_turn_elapsed_f > 0.0:
                            result_text = await await_with_elapsed_budget(
                                _run_sync_abandonment_safe(
                                    invoke_federated_search
                                )
                            )
                            if elapsed_budget_exhausted():
                                raise _TurnElapsedBudgetExhausted()
                        else:
                            # Same collision as search_mathlib above: the
                            # federated searcher already bounds itself at this
                            # value and returns partial results there, so
                            # arming the identical value here preempted its
                            # graceful return and discarded the hits that did
                            # land. Keep the watchdog, but let the searcher's
                            # own deadline fire first.
                            operation_timeout_s = (
                                max(
                                    0.05,
                                    float(
                                        getattr(
                                            searcher,
                                            "operation_timeout_s",
                                            30.0,
                                        )
                                        or 30.0
                                    ),
                                )
                                + _SEARCH_ABANDONMENT_MARGIN_S
                            )
                            result_text = await _run_sync_abandonment_safe(
                                invoke_federated_search,
                                timeout_s=operation_timeout_s,
                            )
                        accepted_result = accepted_result_out.get("result")
                        if accepted_result is not None:
                            searcher.last_result = accepted_result
                            publish = getattr(
                                searcher,
                                "publish_result_metrics",
                                None,
                            )
                            if callable(publish):
                                publish(
                                    accepted_result,
                                    consumer="reactive",
                                )
                    elif name == "check_lean" and lean_check_tool_enabled:
                        context_lemmas = (
                            primitives["feedback_lemmas"](
                                dossier.verified_helper_blocks(),
                                conv,
                            )
                            if dossier is not None
                            else []
                        )
                        primitives["trace"](
                            trace_prefix,
                            "  check_lean starting",
                        )
                        result_text = await await_with_elapsed_budget(
                            primitives["run_check_lean_tool"](
                                lean,
                                preamble=conv.preamble,
                                context_lemmas=context_lemmas,
                                args=args,
                                redact_solution_refs=redact_solution_refs,
                            )
                        )
                    elif name == "try_lean" and try_lean_tool_enabled:
                        context_lemmas = (
                            primitives["feedback_lemmas"](
                                dossier.verified_helper_blocks(),
                                conv,
                            )
                            if dossier is not None
                            else []
                        )
                        accepted_code_out: dict[str, str] = {}
                        result_text = await await_with_elapsed_budget(
                            invoke_formal_runner(
                                primitives["run_try_lean_tool"],
                                lean,
                                goal_statement=tool_goal_statement,
                                preamble=conv.preamble,
                                args=args,
                                context_lemmas=context_lemmas,
                                dossier=dossier,
                                turn_index=turn,
                                tool_call_index=tool_calls_used + 1,
                                redact_solution_refs=redact_solution_refs,
                                allow_declarations=try_lean_allow_declarations,
                                require_declaration=try_lean_require_declaration,
                                deadline_exhausted=(
                                    elapsed_budget_exhausted
                                    if max_turn_elapsed_f > 0.0
                                    else None
                                ),
                                accepted_code_out=accepted_code_out,
                            )
                        )
                        if result_text.startswith("try_lean accepted."):
                            accepted_try_lean_code = str(
                                accepted_code_out.get("code")
                                or args.get("code", "")
                                or ""
                            )
                            helper_registry = getattr(
                                dossier,
                                "verified_helpers",
                                {},
                            )
                            authority_helper_registry = getattr(
                                authority_dossier,
                                "verified_helpers",
                                {},
                            )
                            reserved_bridge_names = {
                                str(name or "").strip()
                                for registry in (
                                    helper_registry,
                                    authority_helper_registry,
                                )
                                if isinstance(registry, Mapping)
                                for name in registry
                                if str(name or "").strip()
                            }
                            bridge_name, bridge_source = (
                                _named_checked_bridge_source(
                                    accepted_try_lean_code,
                                    reserved_names=reserved_bridge_names,
                                )
                            )
                            accepted_target_negation = False
                            accepted_exact_target = False
                            checked_target_headers: tuple[str, ...] = ()
                            if accepted_try_lean_code:
                                try:
                                    from ensemble_prover.mini_recursive import (
                                        _accepted_try_lean_negates_statement,
                                        _iter_checked_lean_target_headers,
                                    )

                                    checked_target_headers = tuple(
                                        _iter_checked_lean_target_headers(
                                            accepted_try_lean_code
                                        )
                                    )
                                    accepted_target_negation = bool(
                                        bridge_source
                                        and _accepted_try_lean_negates_statement(
                                            accepted_try_lean_code,
                                            tool_goal_statement,
                                        )
                                    )
                                    active_target_key = (
                                        canonical_dossier_statement_key(
                                            tool_goal_statement
                                        )
                                    )
                                    accepted_exact_target = bool(
                                        active_target_key
                                        and any(
                                            canonical_dossier_statement_key(
                                                statement
                                            )
                                            == active_target_key
                                            for statement in checked_target_headers
                                        )
                                    )
                                except Exception:
                                    # This optimization is not a trust gate.
                                    # If classification is unavailable, leave
                                    # the ordinary transcript path in control.
                                    accepted_target_negation = bool(bridge_source)
                            if accepted_exact_target:
                                accepted_exact_target_code = (
                                    accepted_try_lean_code
                                )
                            if accepted_target_negation or accepted_exact_target:
                                bridge_name = ""
                                bridge_source = ""
                            recorder = getattr(
                                dossier,
                                "record_verified_helper",
                                None,
                            )
                            bridge_was_new = bool(
                                bridge_name
                                and isinstance(helper_registry, Mapping)
                                and bridge_name not in helper_registry
                            )
                            bridge_validation = ""
                            bridge_replay_context_names = [
                                context_name
                                for block in context_lemmas
                                for context_name in [helper_decl_name(block)]
                                if context_name
                                and isinstance(helper_registry, Mapping)
                                and context_name in helper_registry
                            ]
                            if bridge_source and callable(recorder):
                                bridge_validation = await await_with_elapsed_budget(
                                    primitives["run_try_lean_tool"](
                                        lean,
                                        goal_statement=tool_goal_statement,
                                        preamble=conv.preamble,
                                        args={
                                            "code": bridge_source,
                                            "purpose": (
                                                "revalidate named durable bridge"
                                            ),
                                        },
                                        context_lemmas=context_lemmas,
                                        dossier=dossier,
                                        turn_index=turn,
                                        tool_call_index=tool_calls_used + 1,
                                        redact_solution_refs=(
                                            redact_solution_refs
                                        ),
                                        allow_declarations=True,
                                        require_declaration=True,
                                        accepted_code_out={},
                                        deadline_exhausted=(
                                            elapsed_budget_exhausted
                                            if max_turn_elapsed_f > 0.0
                                            else None
                                        ),
                                    )
                                )
                            if (
                                bridge_source
                                and callable(recorder)
                                and str(bridge_validation or "").startswith(
                                    "try_lean accepted."
                                )
                            ):
                                recorded_bridge = recorder(
                                    bridge_source,
                                    phase="try_lean_verified_bridge",
                                    turn_index=int(turn or 0),
                                    replay_context_names=(
                                        bridge_replay_context_names
                                    ),
                                    provenance_tags=(
                                        "try_lean_accepted_example",
                                    ),
                                )
                                visibility = getattr(
                                    dossier,
                                    "is_verified_helper_context_visible",
                                    None,
                                )
                                bridge_visible = bool(
                                    recorded_bridge is not None
                                    and (
                                        not callable(visibility)
                                        or visibility(recorded_bridge)
                                    )
                                )
                                if (
                                    bridge_was_new
                                    and bridge_visible
                                    and bridge_name
                                    not in accepted_try_lean_helper_names
                                ):
                                    accepted_try_lean_helper_names.append(
                                        bridge_name
                                    )
                                    _increment_tool_metric(
                                        "mini_try_lean_checked_bridges_banked",
                                        1,
                                    )
                            repair_self_check_attempted = True
                            repair_self_check_seen = True
                            repair_self_check_status = "accepted"
                            repair_self_check_codes.append(
                                accepted_try_lean_code
                            )
                        elif result_text.startswith("try_lean rejected."):
                            repair_self_check_attempted = True
                            # Batch order is not authority. Once any verifier
                            # has accepted this exact lane, a later rejected
                            # exploratory variant cannot erase that evidence.
                            # A proof/disproof conflict is handled separately
                            # by the counterexample trust boundary below.
                            if not repair_self_check_seen:
                                repair_self_check_status = (
                                    "no_accepted_try_lean"
                                )
                            # A rejected full proof can still be a valuable,
                            # Lean-elaborated reduction.  Re-run only residual-
                            # bearing attempts through the fail-closed skeleton
                            # validator; it independently validates the parent
                            # stub before mutating proof state.  Raw failed
                            # diagnostics are never scheduled directly.
                            if (
                                "Remaining goals:" in result_text
                                and "scratch proof (unsolved_goals)" in result_text
                                and try_skeleton_tool_enabled
                                and proof_state is not None
                                and callable(primitives.get("run_try_skeleton_tool"))
                                and not try_lean_require_declaration
                            ):
                                try:
                                    promotion_result = await await_with_elapsed_budget(
                                        primitives["run_try_skeleton_tool"](
                                            lean,
                                            goal_statement=tool_goal_statement,
                                            preamble=conv.preamble,
                                            args=args,
                                            conv=conv,
                                            dossier=dossier,
                                            proof_state=proof_state,
                                            turn_index=turn,
                                            tool_call_index=tool_calls_used + 1,
                                            max_residual_goals=max(
                                                0,
                                                int(
                                                    proof_state_child_goal_limit
                                                    or 0
                                                ),
                                            ),
                                            redact_solution_refs=(
                                                redact_solution_refs
                                            ),
                                            deadline_exhausted=(
                                                elapsed_budget_exhausted
                                                if max_turn_elapsed_f > 0.0
                                                else None
                                            ),
                                            deadline_monotonic=(
                                                turn_deadline_monotonic
                                            ),
                                        )
                                    )
                                except (
                                    _TurnElapsedBudgetExhausted,
                                    asyncio.CancelledError,
                                ):
                                    raise
                                except Exception as promotion_exc:
                                    # Skeleton promotion is a secondary,
                                    # fail-closed validation path.  Its own
                                    # infrastructure failure must not erase
                                    # the primary try_lean rejection and its
                                    # useful Lean diagnostics from the model
                                    # transcript or progress governor.
                                    safe_promotion_exc = _prompt_safe_inline_text(
                                        type(promotion_exc).__name__,
                                        limit=120,
                                        redact_solution_refs=(
                                            redact_solution_refs
                                        ),
                                    )
                                    result_text += (
                                        "\nPartial route was not banked: "
                                        "independent skeleton validation "
                                        "failed with "
                                        f"{safe_promotion_exc}."
                                    )
                                    primitives["trace"](
                                        trace_prefix,
                                        "  try_lean residual promotion "
                                        "failed closed; preserving primary "
                                        "Lean rejection "
                                        f"({safe_promotion_exc})",
                                    )
                                    promotion_result = ""
                                promoted_state_status = (
                                    observe_tool_state_update(
                                        "try_skeleton",
                                        promotion_result,
                                    )
                                    if promotion_result
                                    else None
                                )
                                if promoted_state_status in {
                                    "closed",
                                    "root_finalized",
                                    "spawned_remaining_goals",
                                }:
                                    partial_try_lean_promotions += 1
                                    _increment_tool_metric(
                                        "mini_try_lean_partial_state_promotions",
                                        1,
                                    )
                                    result_text += (
                                        "\nPartial proof route banked after independent "
                                        "skeleton validation."
                                    )
                        elif result_text.startswith("try_lean infrastructure error:"):
                            _set_repair_self_check_non_verdict_status(
                                "try_lean_infrastructure_error"
                            )
                        elif result_text.startswith(
                            ("try_lean error:", "try_lean rejected by preflight:")
                        ):
                            _set_repair_self_check_non_verdict_status(
                                "try_lean_preflight_error"
                            )
                    elif name == "certify_counterexample" and try_lean_tool_enabled:
                        authoritative_context_lemmas = (
                            list(dossier.verified_helper_blocks())
                            if dossier is not None
                            else []
                        )
                        feedback_context_lemmas = (
                            primitives["feedback_lemmas"](
                                authoritative_context_lemmas,
                                conv,
                            )
                            if dossier is not None
                            else []
                        )
                        result_text = await await_with_elapsed_budget(
                            invoke_formal_runner(
                                primitives["run_certify_counterexample_tool"],
                                lean,
                                goal_statement=tool_goal_statement,
                                preamble=str(
                                    primitives.get(
                                        "proof_state_acceptance_preamble",
                                        lambda item: str(
                                            getattr(item, "preamble", "") or ""
                                        ),
                                    )(conv)
                                    or ""
                                ),
                                feedback_preamble=str(
                                    getattr(conv, "preamble", "") or ""
                                ),
                                args=args,
                                context_lemmas=authoritative_context_lemmas,
                                feedback_context_lemmas=feedback_context_lemmas,
                                dossier=(
                                    authority_dossier
                                    if authority_dossier is not None
                                    else dossier
                                ),
                                proof_state=proof_state,
                                deadline_exhausted=(
                                    elapsed_budget_exhausted
                                    if max_turn_elapsed_f > 0.0
                                    else None
                                ),
                                publication_guard=publication_guard,
                            )
                        )
                    elif name == "compute_examples" and compute_examples_tool_enabled:
                        async def invoke_compute_runner() -> Any:
                            nonlocal compute_runner_invoked
                            compute_runner_invoked = True
                            return await primitives["run_compute_examples_tool"](
                                lean,
                                preamble=conv.preamble,
                                args=args,
                                dossier=dossier,
                                redact_solution_refs=redact_solution_refs,
                                allow_solution_refs=not redact_solution_refs,
                                deadline_exhausted=(
                                    elapsed_budget_exhausted
                                    if max_turn_elapsed_f > 0.0
                                    else None
                                ),
                            )

                        result_text = await await_with_elapsed_budget(
                            invoke_compute_runner()
                        )
                    elif name == "try_skeleton" and try_skeleton_tool_enabled:
                        result_text = await await_with_elapsed_budget(
                            invoke_formal_runner(
                                primitives["run_try_skeleton_tool"],
                                lean,
                                goal_statement=tool_goal_statement,
                                preamble=conv.preamble,
                                args=args,
                                conv=conv,
                                dossier=dossier,
                                proof_state=proof_state,
                                turn_index=turn,
                                tool_call_index=tool_calls_used + 1,
                                max_residual_goals=max(
                                    0,
                                    int(proof_state_child_goal_limit or 0),
                                ),
                                redact_solution_refs=redact_solution_refs,
                                deadline_exhausted=(
                                    elapsed_budget_exhausted
                                    if max_turn_elapsed_f > 0.0
                                    else None
                                ),
                                deadline_monotonic=turn_deadline_monotonic,
                            )
                        )
                    elif (
                        name == "apply_decl_to_goal"
                        and apply_decl_to_goal_tool_enabled
                    ):
                        context_lemmas = (
                            primitives["feedback_lemmas"](
                                dossier.verified_helper_blocks(),
                                conv,
                            )
                            if dossier is not None
                            else []
                        )
                        result_text = await await_with_elapsed_budget(
                            invoke_formal_runner(
                                primitives["run_apply_decl_to_goal_tool"],
                                lean,
                                preamble=conv.preamble,
                                context_lemmas=context_lemmas,
                                args=args,
                                conv=conv,
                                dossier=dossier,
                                proof_state=proof_state,
                                proof_cache=proof_cache,
                                turn_index=turn,
                                tool_call_index=tool_calls_used + 1,
                                max_residual_goals=max(
                                    0,
                                    int(proof_state_child_goal_limit or 0),
                                ),
                                goal_statement_override=tool_goal_statement,
                                redact_solution_refs=redact_solution_refs,
                                deadline_exhausted=(
                                    elapsed_budget_exhausted
                                    if max_turn_elapsed_f > 0.0
                                    else None
                                ),
                                deadline_monotonic=turn_deadline_monotonic,
                            )
                        )
                    else:
                        safe_name = prompt_safe_tool_name_token(name)
                        result_text = f"Unknown tool: {safe_name}"
                except _TurnElapsedBudgetExhausted:
                    record_elapsed_budget_exhausted()
                    if formal_runner_invoked:
                        # The provider obeyed the requested cadence even when
                        # its formal attempt outlived this action's wall lease.
                        # A pre-dispatch expiry never enters the wrapper.
                        consecutive_search_tool_calls = 0
                        search_cadence_violation_batches = 0
                    if (
                        name in _SEARCH_CADENCE_TOOL_NAMES
                        and search_runner_invoked
                        and not args_parse_error
                    ):
                        # The runner consumed a real retrieval dispatch even
                        # though the shared wall lease won the race. Persist
                        # that work exactly like a completed search so timeout
                        # retries cannot reopen retrieval cadence for free.
                        consecutive_search_tool_calls = min(
                            max(0, int(max_tool_calls_per_turn or 0)),
                            consecutive_search_tool_calls + 1,
                        )
                    if name == "search_theorems":
                        publish_failure = getattr(
                            searcher,
                            "publish_boundary_failure",
                            None,
                        )
                        if callable(publish_failure):
                            publish_failure(
                                consumer="reactive",
                                elapsed_s=max(
                                    0.0,
                                    time.monotonic() - tool_call_started,
                                ),
                            )
                    result_text = (
                        f"{safe_log_name} timed out: "
                        "llm_turn_elapsed_budget_exhausted while this "
                        "advertised tool call was running."
                    )
                    conv.history.append(
                        {
                            "role": "tool",
                            "tool_call_id": safe_tcid,
                            "content": result_text,
                        }
                    )
                    tool_calls_used += 1
                    if replaying_durable_progress_tool:
                        # A timed closer is not semantically disproved. Rotate
                        # it behind untouched calls when the configured replay
                        # capacity can still represent the retry. This keeps
                        # the candidate available without starving a later
                        # exact closer.
                        remaining_capacity = max(
                            0,
                            max(0, int(max_tool_calls_per_turn or 0))
                            - int(tool_calls_used or 0),
                        )
                        timed_signature = _tool_call_signature(tc)
                        if (
                            pending_tool_replay
                            and len(pending_tool_replay) < remaining_capacity
                            and timed_signature
                            and all(
                                _tool_call_signature(pending_call)
                                != timed_signature
                                for pending_call in pending_tool_replay
                            )
                        ):
                            pending_tool_replay.append(dict(tc))
                        durable_progress_tool_replay_pending = bool(
                            pending_tool_replay
                        )
                        durable_progress_tool_replay_exhausted = bool(
                            not pending_tool_replay
                        )
                    timed_out_record = {
                            "name": safe_log_name,
                            "tool_call_id": safe_tcid,
                            "args": prompt_safe_tool_args_record(
                                raw_arg_value,
                                args_parse_error,
                            ),
                            "result_preview": result_text[:400],
                            "protocol_attempted": True,
                            "json_parsed": not bool(args_parse_error),
                            "raw_arguments_length": len(raw_args),
                            "raw_arguments_sha256": hashlib.sha256(
                                raw_args.encode("utf-8", errors="replace")
                            ).hexdigest(),
                            "result_length": len(result_text),
                            "result_sha256": hashlib.sha256(
                                result_text.encode("utf-8", errors="replace")
                            ).hexdigest(),
                        }
                    if name == "compute_examples":
                        timed_out_queries = args.get("queries")
                        timed_out_record.update(
                            runner_invoked=bool(compute_runner_invoked),
                            query_count=(
                                len(timed_out_queries)
                                if compute_runner_invoked
                                and isinstance(timed_out_queries, list)
                                else 0
                            ),
                            result_status="infrastructure_error",
                            execution_status=(
                                "runner_timeout"
                                if compute_runner_invoked
                                else "not_dispatched"
                            ),
                        )
                        if compute_runner_invoked:
                            timed_out_record["error_reason"] = (
                                "llm_turn_elapsed_budget_exhausted"
                            )
                        else:
                            timed_out_record["skipped_reason"] = (
                                "llm_turn_elapsed_budget_exhausted"
                            )
                    else:
                        timed_out_record["skipped_reason"] = (
                            "llm_turn_elapsed_budget_exhausted"
                        )
                    tool_call_log.append(timed_out_record)
                    for remaining_index, remaining_tc in enumerate(
                        calls_to_run[index + 1 :],
                        start=index + 1,
                    ):
                        remaining_fn = remaining_tc.get("function") or {}
                        remaining_name = str(
                            remaining_fn.get("name", "") or ""
                        )
                        remaining_tcid = safe_tool_call_ids[remaining_index]
                        remaining_safe_name = prompt_safe_tool_name_token(
                            remaining_name
                        )
                        remaining_text = (
                            f"{remaining_safe_name} skipped: "
                            "llm_turn_elapsed_budget_exhausted before this "
                            "advertised tool call could run."
                        )
                        conv.history.append(
                            {
                                "role": "tool",
                                "tool_call_id": remaining_tcid,
                                "content": remaining_text,
                            }
                        )
                        remaining_raw_value = (
                            remaining_fn.get("arguments", None)
                            if "arguments" in remaining_fn
                            else None
                        )
                        remaining_raw = (
                            "" if remaining_raw_value is None else str(remaining_raw_value)
                        )
                        remaining_record = {
                                "name": remaining_safe_name,
                                "tool_call_id": remaining_tcid,
                                "args": {},
                                "result_preview": remaining_text[:400],
                                "skipped_reason": "llm_turn_elapsed_budget_exhausted",
                                "protocol_attempted": False,
                                "json_parsed": False,
                                "raw_arguments_length": len(remaining_raw),
                                "raw_arguments_sha256": hashlib.sha256(
                                    remaining_raw.encode("utf-8", errors="replace")
                                ).hexdigest(),
                                "result_length": len(remaining_text),
                                "result_sha256": hashlib.sha256(
                                    remaining_text.encode("utf-8", errors="replace")
                                ).hexdigest(),
                            }
                        if remaining_name == "compute_examples":
                            remaining_record.update(
                                runner_invoked=False,
                                query_count=0,
                                result_status="not_dispatched",
                                execution_status="not_dispatched",
                            )
                        tool_call_log.append(remaining_record)
                    raise
                except asyncio.CancelledError as cancellation:
                    result_text = (
                        f"{safe_log_name} cancelled: tool runner cancelled before "
                        "this advertised tool call completed."
                    )
                    conv.history.append(
                        {
                            "role": "tool",
                            "tool_call_id": safe_tcid,
                            "content": result_text,
                        }
                    )
                    cancelled_record = {
                        "name": safe_log_name,
                        "tool_call_id": safe_tcid,
                        "args": prompt_safe_tool_args_record(
                            raw_arg_value,
                            args_parse_error,
                        ),
                        "result_preview": result_text[:400],
                        "protocol_attempted": True,
                        "json_parsed": not bool(args_parse_error),
                        "raw_arguments_length": len(raw_args),
                        "raw_arguments_sha256": hashlib.sha256(
                            raw_args.encode("utf-8", errors="replace")
                        ).hexdigest(),
                        "result_length": len(result_text),
                        "result_sha256": hashlib.sha256(
                            result_text.encode("utf-8", errors="replace")
                        ).hexdigest(),
                    }
                    if name == "compute_examples":
                        cancelled_queries = args.get("queries")
                        cancelled_record.update(
                            runner_invoked=bool(compute_runner_invoked),
                            query_count=(
                                len(cancelled_queries)
                                if compute_runner_invoked
                                and isinstance(cancelled_queries, list)
                                else 0
                            ),
                            result_status="cancelled",
                            execution_status=(
                                "runner_cancelled"
                                if compute_runner_invoked
                                else "not_dispatched"
                            ),
                        )
                        if compute_runner_invoked:
                            cancelled_record["error_reason"] = "tool_loop_cancelled"
                        else:
                            cancelled_record["skipped_reason"] = "tool_loop_cancelled"
                    else:
                        cancelled_record["skipped_reason"] = "tool_loop_cancelled"
                    tool_call_log.append(cancelled_record)
                    for remaining_index, remaining_tc in enumerate(
                        calls_to_run[index + 1 :],
                        start=index + 1,
                    ):
                        remaining_fn = remaining_tc.get("function") or {}
                        remaining_name = str(remaining_fn.get("name", "") or "")
                        remaining_tcid = safe_tool_call_ids[remaining_index]
                        remaining_safe_name = prompt_safe_tool_name_token(
                            remaining_name
                        )
                        remaining_text = (
                            f"{remaining_safe_name} skipped: tool loop "
                            "cancelled before this advertised tool call "
                            "could run."
                        )
                        conv.history.append(
                            {
                                "role": "tool",
                                "tool_call_id": remaining_tcid,
                                "content": remaining_text,
                            }
                        )
                        remaining_raw_value = (
                            remaining_fn.get("arguments", None)
                            if "arguments" in remaining_fn
                            else None
                        )
                        remaining_raw = (
                            "" if remaining_raw_value is None else str(remaining_raw_value)
                        )
                        remaining_record = {
                            "name": remaining_safe_name,
                            "tool_call_id": remaining_tcid,
                            "args": {},
                            "result_preview": remaining_text[:400],
                            "skipped_reason": "tool_loop_cancelled",
                            "protocol_attempted": False,
                            "json_parsed": False,
                            "raw_arguments_length": len(remaining_raw),
                            "raw_arguments_sha256": hashlib.sha256(
                                remaining_raw.encode("utf-8", errors="replace")
                            ).hexdigest(),
                            "result_length": len(remaining_text),
                            "result_sha256": hashlib.sha256(
                                remaining_text.encode("utf-8", errors="replace")
                            ).hexdigest(),
                        }
                        if remaining_name == "compute_examples":
                            remaining_record.update(
                                runner_invoked=False,
                                query_count=0,
                                result_status="not_dispatched",
                                execution_status="not_dispatched",
                            )
                        tool_call_log.append(remaining_record)
                    cancellation.mini_tool_call_log = [
                        dict(item) for item in tool_call_log
                    ]
                    raise
                except _DetachedSyncWorkerCapacityExhausted as exc:
                    runner_deferred_before_launch = True
                    safe_exc = _prompt_safe_inline_text(
                        exc,
                        limit=500,
                        redact_solution_refs=redact_solution_refs,
                    )
                    result_text = (
                        f"{safe_log_name} infrastructure deferred before launch: "
                        f"{safe_exc}"
                    )
                    primitives["trace"](
                        trace_prefix,
                        f"  {safe_log_name} deferred before launch: {safe_exc}",
                    )
                except Exception as exc:
                    runner_raised = True
                    # B1: synthesize a tool error message so the
                    # tool_call_id is matched. Without this, conv.history
                    # ends up with an ``assistant`` tool-calls message
                    # whose tool_call_ids have no matching ``tool``
                    # messages, and a downstream refiner re-sending this
                    # transcript hits OpenAI 400.
                    safe_exc = _prompt_safe_inline_text(
                        exc,
                        limit=500,
                        redact_solution_refs=redact_solution_refs,
                    )
                    safe_exc_type = _prompt_safe_inline_text(
                        type(exc).__name__,
                        limit=120,
                        redact_solution_refs=redact_solution_refs,
                    )
                    result_text = (
                        f"Tool runner error ({safe_exc_type}): "
                        f"{safe_exc}"
                    )
                    primitives["trace"](
                        trace_prefix,
                        f"  {safe_log_name}(?) crashed: "
                        f"{safe_exc_type}: {safe_exc} "
                        "(synthesized tool error message to keep transcript well-formed)",
                    )
                conv.history.append(
                    {
                        "role": "tool",
                        "tool_call_id": safe_tcid,
                        "content": result_text,
                    }
                )
                execution_disposition = _tool_execution_disposition(
                    name,
                    result_text,
                    runner_raised=runner_raised,
                    runner_deferred_before_launch=(
                        runner_deferred_before_launch
                    ),
                )
                infrastructure_result = execution_disposition != (
                    "completed_semantic"
                )
                counterexample_infrastructure_error = bool(
                    name == "certify_counterexample"
                    and str(result_text or "").startswith(
                        "certify_counterexample infrastructure error:"
                    )
                )
                tool_state_status = (
                    None
                    if infrastructure_result
                    else promoted_state_status
                    or observe_tool_state_update(name, result_text)
                )
                diagnostic_progress_reason = (
                    ""
                    if counterexample_infrastructure_error
                    or infrastructure_result
                    else observe_proof_tool_progress(
                        name,
                        result_text,
                        state_status=tool_state_status,
                        candidate_identity=str(args.get("code", "") or ""),
                    )
                )
                consumes_tool_budget = bool(
                    not search_cadence_skipped
                    and execution_disposition
                    != "infrastructure_deferred_before_launch"
                )
                tool_was_dispatched = bool(
                    not args_parse_error
                    and consumes_tool_budget
                )
                if consumes_tool_budget:
                    tool_calls_used += 1
                    if repair_self_check_required:
                        if name in {"try_lean", "certify_counterexample"}:
                            repair_verification_tool_calls_used += 1
                        else:
                            repair_discovery_tool_calls_used += 1
                if tool_was_dispatched:
                    if name in _FORMAL_CADENCE_TOOL_NAMES:
                        consecutive_search_tool_calls = 0
                        search_cadence_violation_batches = 0
                    elif name in _SEARCH_CADENCE_TOOL_NAMES:
                        consecutive_search_tool_calls = min(
                            max(0, int(max_tool_calls_per_turn or 0)),
                            consecutive_search_tool_calls + 1,
                        )
                query_count = 0
                prepared_query_count = 0
                if args_parse_error:
                    log_query = (
                        "<malformed args: "
                        f"{prompt_safe_tool_arguments(raw_args).replace(chr(10), ' ')}"
                        ">"
                    )[:160]
                else:
                    if name == "compute_examples":
                        queries = args.get("queries")
                        query_count = len(queries) if isinstance(queries, list) else 0
                        mode = str(args.get("mode", "") or "").strip()
                        purpose = str(args.get("purpose", "") or "").strip()
                        legacy_query = str(args.get("query", "") or "").strip()
                        raw_log_query = ", ".join(
                            item
                            for item in (
                                f"queries={query_count}",
                                f"mode={mode}" if mode else "",
                                f"purpose={purpose}" if purpose else "",
                                f"query={legacy_query}" if legacy_query else "",
                            )
                            if item
                        )
                    else:
                        raw_log_query = (
                            str(args.get("query", "") or "")
                            or str(args.get("term", "") or "")
                            or str(args.get("name", "") or "")
                            or str(args.get("code", "") or "").replace("\n", " ")
                        )
                    query_renderer = (
                        _prompt_safe_natural_language_text
                        if name in {"search_mathlib", "search_theorems"}
                        else _prompt_safe_inline_text
                    )
                    log_query = query_renderer(
                        raw_log_query,
                        limit=160,
                        redact_solution_refs=redact_solution_refs,
                    )
                if args_parse_error:
                    primitives["trace"](
                        trace_prefix,
                        f"  {safe_log_name} malformed arguments; tool was not executed",
                    )
                else:
                    log_count = display_line_count(result_text)
                    result_status = "completed"
                    if name == "compute_examples":
                        lowered_result = str(result_text or "").lstrip().lower()
                        prepared_query_count = (
                            query_count
                            if compute_runner_invoked
                            and any(
                                line.strip() == "Commands:"
                                for line in str(result_text or "").splitlines()
                            )
                            else 0
                        )
                        result_status = (
                            "protocol_error"
                            if args_parse_error
                            else "infrastructure_error"
                            if runner_raised
                            else "accepted"
                            if lowered_result.startswith("compute_examples accepted")
                            else "rejected"
                            if lowered_result.startswith(
                                ("compute_examples rejected", "compute_examples error")
                            )
                            else "completed"
                        )
                        diagnostic = " ".join(
                            str(result_text or "").splitlines()[-3:]
                        )
                        diagnostic = _prompt_safe_inline_text(
                            diagnostic,
                            limit=360,
                            redact_solution_refs=redact_solution_refs,
                        )
                        primitives["trace"](
                            trace_prefix,
                            f"  {safe_log_name} result={result_status} "
                            f"queries={prepared_query_count} diagnostic={diagnostic}",
                        )
                    primitives["trace"](
                        trace_prefix,
                        f"  {safe_log_name}({log_query!r}) → {log_count} line(s)",
                    )
                tool_call_record = {
                    "name": safe_log_name,
                    "tool_call_id": safe_tcid,
                    "args": prompt_safe_tool_args_record(
                        raw_arg_value,
                        args_parse_error,
                    ),
                    "result_preview": result_text[:400],
                    "protocol_attempted": True,
                    "json_parsed": not bool(args_parse_error),
                    "raw_arguments_length": len(raw_args),
                    "raw_arguments_sha256": hashlib.sha256(
                        raw_args.encode("utf-8", errors="replace")
                    ).hexdigest(),
                    "result_length": len(str(result_text or "")),
                    "result_sha256": hashlib.sha256(
                        str(result_text or "").encode("utf-8", errors="replace")
                    ).hexdigest(),
                    "execution_disposition": execution_disposition,
                    "deferred_before_launch": bool(
                        execution_disposition
                        == "infrastructure_deferred_before_launch"
                    ),
                }
                if name == "compute_examples":
                    lowered_result = str(result_text or "").lstrip().lower()
                    result_status = (
                        "protocol_error"
                        if args_parse_error
                        else "infrastructure_error"
                        if infrastructure_result
                        else "accepted"
                        if lowered_result.startswith("compute_examples accepted")
                        else "rejected"
                        if lowered_result.startswith(
                            ("compute_examples rejected", "compute_examples error")
                        )
                        else "completed"
                    )
                    tool_call_record["runner_invoked"] = bool(
                        compute_runner_invoked
                    )
                    tool_call_record["query_count"] = prepared_query_count
                    tool_call_record["result_status"] = result_status
                    tool_call_record["result_diagnostic"] = (
                        _prompt_safe_inline_text(
                            " ".join(str(result_text or "").splitlines()[-3:]),
                            limit=400,
                            redact_solution_refs=redact_solution_refs,
                        )
                    )
                    tool_call_record["execution_status"] = (
                        "protocol_rejected"
                        if args_parse_error
                        else "runner_error"
                        if infrastructure_result
                        else "runner_completed"
                        if compute_runner_invoked
                        else "not_dispatched"
                    )
                if args_parse_error:
                    tool_call_record["args_parse_error"] = args_parse_error
                    tool_call_record["skipped_reason"] = "malformed_arguments"
                    tool_call_record["raw_arguments_preview"] = (
                        prompt_safe_tool_arguments(raw_args)[:400]
                    )
                if search_cadence_skipped:
                    tool_call_record.update(
                        skipped_reason="search_cadence_requires_formal_attempt",
                        protocol_attempted=False,
                        runner_invoked=False,
                        execution_status="not_dispatched",
                    )
                if tool_state_status:
                    tool_call_record["proof_state_update_status"] = tool_state_status
                if promoted_state_status:
                    tool_call_record["partial_try_lean_promoted"] = True
                if diagnostic_progress_reason:
                    tool_call_record["semantic_diagnostic_progress"] = (
                        diagnostic_progress_reason
                    )
                tool_call_log.append(tool_call_record)

                call_signature = _tool_call_signature(tc)
                if (
                    execution_disposition == "completed_semantic"
                    and name == "try_lean"
                    and str(result_text or "").startswith("try_lean accepted.")
                    and call_signature
                ):
                    accepted_try_lean_receipts[call_signature] = str(
                        accepted_try_lean_code
                    )
                    # Any accepted repair candidate satisfies the verifier
                    # contract; a different candidate's infrastructure retry
                    # must not downgrade that stronger evidence.
                    if repair_self_check_seen:
                        pending_tool_replay = []
                        tool_infrastructure_receipt_id = ""

                if repair_self_check_required and name == "try_lean":
                    # Scheduler accounting needs to know whether this paid
                    # verifier call actually launched even when its semantic
                    # result is followed by a zero-receipt provider failure.
                    paid_tool_infrastructure_disposition = (
                        "infrastructure_deferred_before_launch"
                        if execution_disposition
                        == "infrastructure_deferred_before_launch"
                        else "infrastructure_after_launch"
                    )
                    if replaying_paid_tool_retry:
                        paid_tool_continuation_identity = str(
                            tool_infrastructure_receipt_id or ""
                        )

                if infrastructure_result and call_signature:
                    durable_skeleton_retry_banked = False
                    if name == "try_skeleton" and proof_state is not None:
                        try:
                            skeleton_payload = json.loads(
                                str(result_text or "")
                            )
                        except Exception:
                            skeleton_payload = {}
                        if bool(
                            isinstance(skeleton_payload, Mapping)
                            and skeleton_payload.get(
                                "pending_residual_goal_extraction"
                            )
                        ):
                            nodes = getattr(proof_state, "nodes", {}) or {}
                            durable_skeleton_retry_banked = any(
                                bool(
                                    getattr(
                                        node,
                                        "pending_residual_goal_extraction",
                                        {},
                                    )
                                )
                                for node in (
                                    nodes.values()
                                    if isinstance(nodes, Mapping)
                                    else ()
                                )
                            )
                            durable_tool_retry_banked = bool(
                                durable_skeleton_retry_banked
                            )
                    if repair_self_check_required and name == "try_lean":
                        replay_consumed_paid_launch = bool(
                            replaying_paid_tool_retry
                            and execution_disposition
                            == "infrastructure_after_launch"
                        )
                        if (
                            not pending_tool_replay
                            and not replay_consumed_paid_launch
                        ):
                            pending_tool_replay = [dict(tc)]
                            preserve_paid_receipt = bool(
                                replaying_paid_tool_retry
                                and execution_disposition
                                == "infrastructure_deferred_before_launch"
                                and tool_infrastructure_receipt_id
                            )
                            if not preserve_paid_receipt:
                                provider_lane_identity = (
                                    _provider_turn_lane_identity(
                                        conv,
                                        goal_statement_override,
                                    )
                                )
                                tool_infrastructure_receipt_id = hashlib.sha256(
                                    (
                                        provider_lane_identity
                                        + "\0"
                                        + call_signature
                                        + "\0"
                                        + str(result_text or "")
                                    ).encode("utf-8", errors="replace")
                                ).hexdigest()
                            tool_infrastructure_disposition = (
                                execution_disposition
                            )
                            pending_tool_replay_is_paid_retry = bool(
                                execution_disposition
                                == "infrastructure_after_launch"
                                or preserve_paid_receipt
                            )
                            paid_tool_continuation_identity = (
                                tool_infrastructure_receipt_id
                            )
                            paid_tool_continuation_granted = bool(
                                not replaying_persisted_tool
                                or pending_tool_replay_is_paid_retry
                            )
                        elif replay_consumed_paid_launch:
                            # The original launch and this one exact replay
                            # are both paid receipts. Do not mint a fresh
                            # continuation merely because the replay failed
                            # in the same way.
                            pending_tool_replay = []
                            pending_tool_replay_is_paid_retry = False
                            tool_infrastructure_receipt_id = ""
                            tool_infrastructure_disposition = ""
                    elif (
                        name != "certify_counterexample"
                        and not runner_raised
                        and not durable_skeleton_retry_banked
                        and call_signature
                        not in infrastructure_replay_signatures
                    ):
                        # Replay the exact admitted call locally. This is not
                        # a new model decision, so it bypasses repeat policing
                        # and may consume one paid slot beyond the nominal
                        # budget when the first attempt launched and failed.
                        infrastructure_replay_signatures.add(call_signature)
                        replay_call = dict(tc)
                        calls_to_run.append(replay_call)
                        advertised_tool_calls.append(
                            advertised_tool_call(
                                replay_call,
                                len(advertised_tool_calls),
                            )
                        )
                        assistant_message.pop("_responses_output_items", None)

                counterexample_result = str(result_text or "")
                if counterexample_infrastructure_error:
                    llm_error = counterexample_result
                    llm_failure_kind = (
                        "certify_counterexample_infrastructure_error"
                    )
                    # Reuse the scheduler's bounded scoped-infrastructure
                    # recovery lane while the precise tool failure remains in
                    # ``llm_failure_kind`` and the B1 receipt.
                    llm_failure_reason = "llm_network_error"
                    llm_retryable = True
                    llm_terminal = False
                    for remaining_index, remaining_tc in enumerate(
                        calls_to_run[index + 1 :],
                        start=index + 1,
                    ):
                        remaining_fn = remaining_tc.get("function") or {}
                        remaining_name = str(
                            remaining_fn.get("name", "") or ""
                        )
                        remaining_tcid = safe_tool_call_ids[remaining_index]
                        remaining_safe_name = prompt_safe_tool_name_token(
                            remaining_name
                        )
                        remaining_text = (
                            f"{remaining_safe_name} skipped: counterexample "
                            "certification infrastructure failure requires "
                            "scheduler retry."
                        )
                        conv.history.append({
                            "role": "tool",
                            "tool_call_id": remaining_tcid,
                            "content": remaining_text,
                        })
                        remaining_raw_value = (
                            remaining_fn.get("arguments", None)
                            if "arguments" in remaining_fn
                            else None
                        )
                        remaining_raw = (
                            ""
                            if remaining_raw_value is None
                            else str(remaining_raw_value)
                        )
                        remaining_record = {
                            "name": remaining_safe_name,
                            "tool_call_id": remaining_tcid,
                            "args": {},
                            "result_preview": remaining_text[:400],
                            "skipped_reason": (
                                "certify_counterexample_infrastructure_error"
                            ),
                            "protocol_attempted": False,
                            "json_parsed": False,
                            "raw_arguments_length": len(remaining_raw),
                            "raw_arguments_sha256": hashlib.sha256(
                                remaining_raw.encode(
                                    "utf-8",
                                    errors="replace",
                                )
                            ).hexdigest(),
                            "result_length": len(remaining_text),
                            "result_sha256": hashlib.sha256(
                                remaining_text.encode(
                                    "utf-8",
                                    errors="replace",
                                )
                            ).hexdigest(),
                        }
                        if remaining_name == "compute_examples":
                            remaining_record.update(
                                runner_invoked=False,
                                execution_status="not_dispatched",
                            )
                        tool_call_log.append(remaining_record)
                    break
                if name == "certify_counterexample" and counterexample_result.startswith(
                    (
                        "certify_counterexample accepted.",
                        "certify_counterexample conflict.",
                    )
                ):
                    proof_disproof_conflict = counterexample_result.startswith(
                        "certify_counterexample conflict."
                    )
                    if not proof_disproof_conflict:
                        authoritative_falsification = True
                        authoritative_falsification_target = tool_goal_statement
                        authoritative_falsification_environment_hash = str(
                            getattr(
                                authority_dossier
                                if authority_dossier is not None
                                else dossier,
                                "current_lean_environment_hash",
                                "",
                            )
                            or ""
                        ).strip()
                        certificate_match = re.search(
                            r"\bcertificate=([0-9a-f]{64})\b",
                            counterexample_result,
                        )
                        authoritative_falsification_certificate_hash = (
                            certificate_match.group(1) if certificate_match else ""
                        )
                        authority_target_dossier = (
                            authority_dossier
                            if authority_dossier is not None
                            else dossier
                        )
                        root_certificate = dict(
                            getattr(
                                authority_target_dossier,
                                "root_disproof_certificate",
                                {},
                            )
                            or {}
                        )
                        if (
                            authority_target_dossier is not None
                            and active_root_disproof_certificate_is_valid(
                                authority_target_dossier
                            )
                            and str(root_certificate.get("certificate_hash") or "")
                            == authoritative_falsification_certificate_hash
                        ):
                            authoritative_falsification_target = str(
                                getattr(
                                    authority_target_dossier,
                                    "root_statement",
                                    "",
                                )
                                or ""
                            ).strip()
                    repair_self_check_attempted = True
                    repair_self_check_seen = not proof_disproof_conflict
                    repair_self_check_status = (
                        "proof_disproof_conflict"
                        if proof_disproof_conflict
                        else "accepted_counterexample"
                    )
                    repair_self_check_codes.append(str(args.get("code", "") or ""))
                    for remaining_index, remaining_tc in enumerate(
                        calls_to_run[index + 1 :],
                        start=index + 1,
                    ):
                        remaining_fn = remaining_tc.get("function") or {}
                        remaining_name = str(remaining_fn.get("name", "") or "")
                        remaining_tcid = safe_tool_call_ids[remaining_index]
                        remaining_safe_name = prompt_safe_tool_name_token(
                            remaining_name
                        )
                        remaining_text = (
                            f"{remaining_safe_name} skipped: proof/disproof trust "
                            "boundary conflict is terminal."
                            if proof_disproof_conflict
                            else f"{remaining_safe_name} skipped: active target "
                            "already authoritatively refuted."
                        )
                        conv.history.append({
                            "role": "tool",
                            "tool_call_id": remaining_tcid,
                            "content": remaining_text,
                        })
                        remaining_raw_value = (
                            remaining_fn.get("arguments", None)
                            if "arguments" in remaining_fn
                            else None
                        )
                        remaining_raw = (
                            ""
                            if remaining_raw_value is None
                            else str(remaining_raw_value)
                        )
                        remaining_record = {
                            "name": remaining_safe_name,
                            "tool_call_id": remaining_tcid,
                            "args": {},
                            "result_preview": remaining_text[:400],
                            "skipped_reason": (
                                "proof_disproof_conflict_terminal"
                                if proof_disproof_conflict
                                else "authoritative_counterexample_terminal"
                            ),
                            "protocol_attempted": False,
                            "json_parsed": False,
                            "raw_arguments_length": len(remaining_raw),
                            "raw_arguments_sha256": hashlib.sha256(
                                remaining_raw.encode("utf-8", errors="replace")
                            ).hexdigest(),
                            "result_length": len(remaining_text),
                            "result_sha256": hashlib.sha256(
                                remaining_text.encode("utf-8", errors="replace")
                            ).hexdigest(),
                        }
                        if remaining_name == "compute_examples":
                            remaining_record.update(
                                runner_invoked=False,
                                query_count=0,
                                result_status="not_dispatched",
                                execution_status="not_dispatched",
                            )
                        tool_call_log.append(remaining_record)
                    break

                if semantic_no_progress_detected:
                    # Preserve the B1 transcript invariant for every call the
                    # provider advertised, but do not execute more expensive
                    # variants after this route's formal progress governor
                    # fired.
                    for remaining_index, remaining_tc in enumerate(
                        calls_to_run[index + 1 :],
                        start=index + 1,
                    ):
                        remaining_fn = remaining_tc.get("function") or {}
                        remaining_name = str(remaining_fn.get("name", "") or "")
                        remaining_tcid = safe_tool_call_ids[remaining_index]
                        remaining_safe_name = prompt_safe_tool_name_token(
                            remaining_name
                        )
                        remaining_text = (
                            f"{remaining_safe_name} skipped: semantic formal "
                            "progress governor exhausted for this attempt."
                        )
                        conv.history.append({
                            "role": "tool",
                            "tool_call_id": remaining_tcid,
                            "content": remaining_text,
                        })
                        remaining_raw_value = (
                            remaining_fn.get("arguments", None)
                            if "arguments" in remaining_fn
                            else None
                        )
                        remaining_raw = (
                            "" if remaining_raw_value is None else str(remaining_raw_value)
                        )
                        remaining_record = {
                            "name": remaining_safe_name,
                            "tool_call_id": remaining_tcid,
                            "args": {},
                            "result_preview": remaining_text[:400],
                            "skipped_reason": "semantic_no_formal_progress",
                            "protocol_attempted": False,
                            "json_parsed": False,
                            "raw_arguments_length": len(remaining_raw),
                            "raw_arguments_sha256": hashlib.sha256(
                                remaining_raw.encode("utf-8", errors="replace")
                            ).hexdigest(),
                            "result_length": len(remaining_text),
                            "result_sha256": hashlib.sha256(
                                remaining_text.encode("utf-8", errors="replace")
                            ).hexdigest(),
                        }
                        if remaining_name == "compute_examples":
                            remaining_record.update(
                                runner_invoked=False,
                                execution_status="not_dispatched",
                            )
                        tool_call_log.append(remaining_record)
                    break

            # Every advertised call now has its matching tool receipt.  This
            # is the only safe point to compact within an active provider
            # transcript: never split the assistant/tool protocol pair, and
            # retain the latest actionable Lean evidence for the next round.
            _compact_completed_in_turn_tool_history()

            if (
                replaying_durable_progress_tool
                and not pending_tool_replay
                and not accepted_exact_target_code
                and not accepted_try_lean_helper_names
                and not tool_state_update_statuses
                and not authoritative_falsification
                and not proof_disproof_conflict
            ):
                # The authenticated queue has a terminal empty successor only
                # when the consumed calls produced no proof-state progress.
                # Accepted work must remain replayable if the outer workspace
                # later loses its publication race.
                durable_progress_tool_replay_exhausted = True

            if accepted_exact_target_code:
                # The kernel already accepted the active target. Publish that
                # exact artifact instead of asking the provider to restate it
                # or allowing an earlier helper cutpoint to hide the solve.
                content = accepted_exact_target_code
                break

            if any(
                status in {"closed", "root_finalized"}
                for status in tool_state_update_statuses
            ):
                # A completed graph/root mutation must publish before any
                # later provider or tool work can consume the outer lease.
                content = ""
                break

            if "spawned_remaining_goals" in tool_state_update_statuses:
                # A Lean-validated route is a complete unit of useful work.
                # End at this formal cutpoint so a later provider delay cannot
                # roll the new obligations back with the surrounding action
                # transaction.  The scheduler can now prove the children and
                # return to the recorded assembly route autonomously.
                content = ""
                break

            if accepted_try_lean_helper_names:
                # A completed off-target example is verified mathematical
                # progress, not disposable scratch. End before another model
                # request can turn this action into an all-or-nothing timeout.
                content = ""
                break

            if (
                durable_tool_retry_banked
                and not accepted_try_lean_receipts
                and not authoritative_falsification
                and not proof_disproof_conflict
                and tool_state_closures <= 0
            ):
                # The exact paid skeleton has moved to proof-state-owned
                # verifier replay. End this provider turn at that durable
                # boundary instead of looping until a tiny turn deadline
                # converts the neutral handoff into a timeout failure.
                break

            if llm_turn_elapsed_budget_exhausted:
                break

            if pending_tool_replay:
                llm_error = "lean_tool_infrastructure_retry_pending"
                llm_failure_kind = "lean_tool_infrastructure_retry_pending"
                llm_retryable = True
                llm_terminal = False
                llm_failure_reason = llm_failure_kind
                content = ""
                break

            if authoritative_falsification or proof_disproof_conflict:
                break

            if (
                llm_failure_kind
                == "certify_counterexample_infrastructure_error"
            ):
                break

            seen_tool_call_signatures.update(call_signatures)

            if (
                batch_search_cadence_skipped
                and not batch_formal_cadence_requested
                and not replaying_persisted_tool
            ):
                search_cadence_violation_batches = min(
                    _SEARCH_CADENCE_VIOLATION_BATCH_CAP,
                    search_cadence_violation_batches + 1,
                )
                search_cadence_stall_detected = (
                    search_cadence_violation_batches
                    >= _SEARCH_CADENCE_VIOLATION_BATCH_CAP
                )
                if search_cadence_stall_detected:
                    force_finalize_without_tools = True
                    conv.history.append(
                        _user_history_message(
                            "Search requests repeatedly ignored the required "
                            "formal-attempt guidance. Tools are disabled for "
                            "this attempt. Use the retrieved evidence to "
                            "provide your best final Lean artifact now. "
                            + _final_submission_shape_instruction(
                                require_declaration=try_lean_require_declaration
                            ),
                            repair_semantics=_REPAIR_CONTINUATION,
                        )
                    )
                    primitives["trace"](
                        trace_prefix,
                        "  tool loop: repeated search cadence violations; "
                        "forcing no-tools finalization",
                    )
                    continue

            if semantic_no_progress_detected:
                force_finalize_without_tools = True
                conv.history.append(
                    _user_history_message(
                        (
                            "Tool work has produced no bankable formal progress "
                            "across several completed proof-tool "
                            "attempts. Tools are disabled for this attempt. Do "
                            "not submit another cosmetic variant: use the banked "
                            "residual route if present and provide your best "
                            "final artifact. Do not add a prose-only bottleneck "
                            "report. If useful, describe the remaining obstacle "
                            "in a Lean comment inside the single required fenced "
                            "block alongside the artifact. "
                            + _final_submission_shape_instruction(
                                require_declaration=try_lean_require_declaration
                            )
                        ),
                        repair_semantics=_REPAIR_CONTINUATION,
                    )
                )
                primitives["trace"](
                    trace_prefix,
                    "  tool loop: semantic no-formal-progress governor fired; "
                    "forcing no-tools finalization",
                )
                continue

            if (
                repair_self_check_required
                and repair_self_check_status in non_verdict_repair_self_check_statuses
                and not _repair_self_check_non_verdict_is_compliant(
                    repair_self_check_status
                )
                and not repair_self_check_seen
                and not repair_self_check_attempted
                and tool_calls_used < max_tool_calls_per_turn
            ):
                message_fn = primitives.get(
                    "repair_self_check_required_message",
                    lambda **_kw: "Repair self-check required.",
                )
                reminder = message_fn(
                    require_try_lean=try_lean_tool_enabled,
                    require_declaration=try_lean_require_declaration,
                    role=str(getattr(conv, "role", "") or "prove"),
                )
                conv.history.append({"role": "user", "content": reminder})
                repair_self_check_reminder_sent = True
                primitives["trace"](
                    trace_prefix,
                    "  malformed/non-verdict repair self-check did not run Lean; "
                    "requesting a valid try_lean call while tool budget remains",
                )
                if repeat_recovery_active:
                    repeat_recovery_pending = True
                continue

            if (
                reserved_for_try_lean
                and repair_self_check_required
                and not repair_self_check_seen
                and not repair_self_check_attempted
                and not _repair_self_check_non_verdict_is_compliant(
                    repair_self_check_status
                )
            ):
                message_fn = primitives.get(
                    "repair_self_check_required_message",
                    lambda **_kw: "Repair self-check required.",
                )
                reminder = message_fn(
                    require_try_lean=try_lean_tool_enabled,
                    require_declaration=try_lean_require_declaration,
                    role=str(getattr(conv, "role", "") or "prove"),
                )
                conv.history.append({"role": "user", "content": reminder})
                repair_self_check_reminder_sent = True
                if dropped > 0:
                    primitives["trace"](
                        trace_prefix,
                        "  reserved one repair tool slot for try_lean; "
                        f"dropped {dropped} non-self-check call(s)",
                    )
                if repeat_recovery_active:
                    repeat_recovery_pending = True
                continue

            if repeat_recovery_active and not force_finalize_without_tools:
                force_finalize_without_tools = True
                tool_repeat_action = "force_finalize_after_guided_retry"
                _increment_tool_metric("tool_repeat_forced_finalize", 1)
                conv.history.append(
                    _user_history_message(
                        (
                            "You used the final corrective tool step. Tools are "
                            "now disabled for this attempt. Use the results already "
                            "present and write the active Lean artifact now. "
                            + _final_submission_shape_instruction(
                                require_declaration=try_lean_require_declaration
                            )
                        ),
                        repair_semantics=_REPAIR_CONTINUATION,
                    )
                )
                primitives["trace"](
                    trace_prefix,
                    "  tool loop: corrective tool step consumed; forcing "
                    "no-tools finalization",
                )
                continue

            if dropped > 0 or tool_calls_used >= max_tool_calls_per_turn:
                # Either the model wanted more calls than budget allowed,
                # or we just ran the last permitted call. On repair turns,
                # never ask for a final proof after the required self-check
                # became impossible.
                if (
                    repair_self_check_required
                    and not repair_self_check_seen
                    and not repair_self_check_attempted
                    and not _repair_self_check_non_verdict_is_compliant(
                        repair_self_check_status
                    )
                ):
                    status = _set_repair_self_check_gap(budget_exhausted=True)
                    llm_error = _repair_self_check_gap_error(status) or llm_error
                    break
                msg = (
                    f"Tool budget exhausted "
                    f"({tool_calls_used}/{max_tool_calls_per_turn} calls used"
                    + (
                        f"; {dropped} additional call(s) dropped"
                        if dropped > 0
                        else ""
                    )
                    + "). Use what you have and write the active Lean artifact now. "
                    + _final_submission_shape_instruction(
                        require_declaration=try_lean_require_declaration
                    )
                )
                conv.history.append(
                    _user_history_message(
                        msg,
                        repair_semantics=_REPAIR_CONTINUATION,
                    )
                )
                if dropped > 0:
                    primitives["trace"](
                        trace_prefix,
                        f"  budget exhausted mid-batch; dropped {dropped} call(s)",
                    )
            if (
                provider_call_quantum_boundary_reached()
                and tool_calls_used < max_tool_calls_per_turn
                and not llm_failure_kind
            ):
                record_provider_call_quantum_yield(boundary="tool")
                break
            # Loop back. Next iter: if budget reached, the provider-aware
            # finalizer forces the model to commit to a proof using what it's
            # seen.
    except _TurnElapsedBudgetExhausted as exc:
        _restore_unsettled_repeat_recovery()
        provider_dispatches_started = max(
            provider_dispatches_started,
            _exception_nonnegative_int(exc, "provider_dispatches_started"),
        )
        if provider_call_started > 0.0:
            exhausted_provider_elapsed_s = max(
                0.0,
                time.monotonic() - provider_call_started,
            )
            provider_call_elapsed_s += exhausted_provider_elapsed_s
            provider_call_cumulative_elapsed_s += exhausted_provider_elapsed_s
            provider_call_started = 0.0
        record_elapsed_budget_exhausted()
    except _ProviderCumulativeWallExhausted as exc:
        _restore_unsettled_repeat_recovery()
        provider_dispatches_started = max(
            provider_dispatches_started,
            _exception_nonnegative_int(exc, "provider_dispatches_started"),
        )
        if provider_call_started > 0.0:
            exhausted_provider_elapsed_s = max(
                0.0,
                time.monotonic() - provider_call_started,
            )
            provider_call_elapsed_s += exhausted_provider_elapsed_s
            provider_call_cumulative_elapsed_s += exhausted_provider_elapsed_s
            provider_call_started = 0.0
        record_provider_cumulative_wall_exhausted()
    except RuntimeCapabilityRevokedError:
        raise
    except Exception as exc:
        _restore_unsettled_repeat_recovery()
        provider_dispatches_started = max(
            provider_dispatches_started,
            _exception_nonnegative_int(exc, "provider_dispatches_started"),
        )
        reasoning_capability_unavailable = bool(
            getattr(
                exc,
                "mini_reasoning_capability_unavailable",
                False,
            )
        )
        safe_llm_error = _prompt_safe_inline_text(
            format_exception(exc),
            limit=1000,
            redact_solution_refs=redact_solution_refs,
        )
        llm_retry_deadline = llm_retry_deadline_record_from_exception(exc)
        provider_defer = provider_defer_record_from_exception(client, exc)
        provider_attempts = list(
            _sanitize_model_facing_value(
                list(getattr(client, "last_attempts", []) or []),
                redact_solution_refs=redact_solution_refs,
                limit=1000,
            )
            or []
        )
        if reasoning_capability_unavailable:
            llm_failure_kind = "mini_reasoning_capability_unavailable"
            llm_retryable = True
            llm_terminal = False
            llm_failure_reason = llm_failure_kind
        else:
            classification = classify_llm_exception(exc)
            llm_failure_kind = classification.kind
            llm_retryable = bool(classification.retryable)
            llm_terminal = bool(classification.terminal)
            llm_failure_reason = str(classification.failure_reason or "")
        failed_provider_pre_generation_rejection = bool(
            provider_defer
            and llm_retryable
            and llm_failure_kind in {"rate_limit", "http_429"}
        )
        if provider_call_started > 0.0:
            failed_provider_elapsed_s = max(
                0.0,
                time.monotonic() - provider_call_started,
            )
            provider_call_elapsed_s += failed_provider_elapsed_s
            provider_call_cumulative_elapsed_s += failed_provider_elapsed_s
            provider_call_started = 0.0
        if (
            (
                llm_failure_kind == "provider_dispatch_attempt_limit_exhausted"
                or (
                    provider_dispatch_quantum_spent
                    and llm_retryable
                    and not llm_terminal
                )
            )
            and (
                provider_quantum_cap_active
                or provider_finalizer_continuation_active
            )
            and provider_quantum_authenticated_dispatches_started > 0
        ):
            provider_call_quantum_exhausted = True
            if llm_failure_kind != "provider_dispatch_attempt_limit_exhausted":
                # The admitted physical attempt consumed this scheduler
                # quantum. Preserve its concrete error in ``llm_error`` and
                # provider attempts, but classify the action outcome as a
                # cooperative yield so the durable chain cursor is retained.
                llm_failure_kind = "llm_provider_quantum_exhausted"
                llm_retryable = True
                llm_terminal = False
            if provider_finalizer_continuation_active:
                provider_finalizer_continuation_exhausted = True
                provider_call_quantum_max_retries = max(
                    provider_call_quantum_max_retries,
                    _CONVERSATION_FINALIZER_PROVIDER_QUANTUM_MAX_RETRIES,
                )
            llm_failure_reason = llm_failure_kind
            provider_dispatch_quantum_yield_metric_pending = True
        llm_error_metadata: List[str] = []
        for label, value in (
            ("kind", llm_failure_kind),
            ("reason", llm_failure_reason),
        ):
            text = str(value or "").strip()
            if text and text not in safe_llm_error:
                llm_error_metadata.append(
                    f"{label}="
                    + _prompt_safe_inline_text(
                        text,
                        limit=160,
                        redact_solution_refs=redact_solution_refs,
                    )
                )
        llm_error = (
            f"{safe_llm_error} ({'; '.join(llm_error_metadata)})"
            if llm_error_metadata
            else safe_llm_error
        )
        primitives["trace"](trace_prefix, f"  LLM call failed: {llm_error}")

    def _finalizer_recovery_authority_current() -> bool:
        try:
            _validate_selected_proof_idea_dispatch_context(
                list(current_messages or ()),
                dossier,
            )
        except SelectedProofIdeaDispatchContextError:
            return False
        # These are lifecycle fences, not ordinary stale-candidate checks.
        # Revocation, dispatch detachment, and cancellation must propagate.
        require_hard_timeout_capability_active("Mini finalizer proof recovery")
        if callable(publication_guard):
            publication_guard()
        return True

    def _retain_recovered_finalizer_failure_receipt() -> None:
        nonlocal recovered_finalizer_error
        nonlocal recovered_finalizer_failure_kind
        nonlocal recovered_finalizer_retryable
        nonlocal recovered_finalizer_provider_call_quantum_exhausted
        nonlocal recovered_finalizer_terminal
        nonlocal recovered_finalizer_failure_reason
        nonlocal recovered_finalizer_retry_deadline
        nonlocal recovered_finalizer_provider_attempts
        nonlocal recovered_finalizer_provider_defer

        recovered_finalizer_error = str(llm_error or "")
        recovered_finalizer_failure_kind = str(llm_failure_kind or "")
        recovered_finalizer_retryable = bool(llm_retryable)
        recovered_finalizer_provider_call_quantum_exhausted = bool(
            provider_call_quantum_exhausted
        )
        recovered_finalizer_terminal = bool(llm_terminal)
        recovered_finalizer_failure_reason = str(llm_failure_reason or "")
        recovered_finalizer_retry_deadline = dict(llm_retry_deadline or {})
        recovered_finalizer_provider_attempts = list(provider_attempts or [])
        recovered_finalizer_provider_defer = dict(provider_defer or {})

    accepted_fallback_code = next(
        (
            str(code or "")
            for code in reversed(repair_self_check_codes)
            if str(code or "").strip()
        ),
        "",
    )
    if (
        llm_error
        and accepted_fallback_code
        and repair_self_check_seen
        and repair_self_check_status == "accepted"
        and _finalizer_recovery_authority_current()
    ):
        # Lean's paid acceptance is the authoritative artifact. Any settled
        # provider failure while merely serializing it must not erase it.
        # Cancellation and runtime-capability revocation are re-raised above.
        _retain_recovered_finalizer_failure_receipt()
        content = accepted_fallback_code
        llm_error = None
        llm_failure_kind = ""
        llm_retryable = False
        llm_terminal = False
        llm_failure_reason = ""
        provider_call_quantum_exhausted = False
        provider_finalizer_continuation_exhausted = False
        provider_finalizer_continuation_active = False
        final_no_tools_event = "accepted_try_lean_provider_failure_fallback"
        final_no_tools_used_accepted_proof = True
        _increment_tool_metric(
            "mini_final_no_tools_accepted_proof_fallbacks",
            1,
        )

    banked_mixed_finalizer_authority_current = False
    if (
        llm_error
        and banked_mixed_finalizer_pending
        and banked_mixed_final_content
        and banked_mixed_finalizer_lane_identity
        == _provider_turn_lane_identity(conv, goal_statement_override)
    ):
        banked_mixed_finalizer_authority_current = (
            _finalizer_recovery_authority_current()
        )
    if banked_mixed_finalizer_authority_current:
        # A provider may return a plausible proof beside an ignored tool call.
        # We execute the tool while capacity remains, but the next forced
        # finalizer can fail before the ordinary in-loop fallback runs.  The
        # paid candidate is already in this workspace, so expose it to the
        # caller's normal extraction and Lean check instead of yielding and
        # rolling it back.  This is not proof acceptance: only the caller's
        # independent Lean gate can establish progress or solve the goal.
        banked_resolution = resolve_final_no_tools_output(
            content=banked_mixed_final_content,
            raw_response=None,
            client=None,
            accepted_proof_codes=repair_self_check_codes,
        )
        if (
            not banked_resolution.error
            and _bankable_final_proof_content(banked_resolution.content)
        ):
            _retain_recovered_finalizer_failure_receipt()
            content = banked_resolution.content
            banked_mixed_final_content = ""
            banked_mixed_finalizer_pending = False
            banked_mixed_finalizer_lane_identity = ""
            llm_error = None
            llm_failure_kind = ""
            llm_retryable = False
            llm_terminal = False
            llm_failure_reason = ""
            provider_call_quantum_exhausted = False
            provider_finalizer_continuation_exhausted = False
            provider_finalizer_continuation_active = False
            llm_turn_elapsed_budget_exhausted = False
            final_no_tools_event = (
                "final_no_tools_banked_mixed_proof_provider_failure_fallback"
            )
            final_no_tools_finish_reason = str(
                banked_resolution.finish_reason or ""
            )
            final_no_tools_reasoning_content_chars = int(
                banked_resolution.reasoning_content_chars or 0
            )
            final_no_tools_used_accepted_proof = False

    if (
        provider_dispatch_quantum_yield_metric_pending
        and provider_call_quantum_exhausted
        and llm_error
    ):
        _increment_tool_metric("mini_provider_call_quantum_yields", 1)

    if provider_call_quantum_exhausted and provider_cumulative_wall_exhausted():
        provider_call_quantum_exhausted = False
        record_provider_cumulative_wall_exhausted()

    if (
        repair_self_check_required
        and not repair_self_check_seen
        and not repair_self_check_helper_only_allowed
        and not llm_error
    ):
        status = _set_repair_self_check_gap()
        llm_error = _repair_self_check_gap_error(status) or llm_error

    advisory_repair_continuation = bool(
        repair_self_check_required
        and llm_error
        in {
            "repair_self_check_missing",
            "repair_self_check_no_try_lean_call",
            "repair_self_check_no_accepted_try_lean",
            "repair_self_check_tool_budget_exhausted",
        }
    )
    if advisory_repair_continuation:
        _advance_chain_after_unusable_output()
    persist_provider_continuation = bool(
        (
            resumed_provider_continuation
            and not repair_self_check_seen
            and not authoritative_falsification
            and not proof_disproof_conflict
        )
        or provider_call_quantum_exhausted
        or provider_call_cumulative_wall_exhausted
        or (llm_error and llm_retryable and not llm_terminal)
        or advisory_repair_continuation
        or durable_progress_tool_replay_pending
    )
    if durable_progress_tool_replay_pending and pending_tool_replay:
        helper_registry = getattr(dossier, "verified_helpers", {}) or {}
        resolver = getattr(dossier, "resolve_verified_helper_name", None)
        for raw_name in accepted_try_lean_helper_names:
            helper_name = str(raw_name or "").strip()
            resolved_name = (
                str(resolver(helper_name) or helper_name).strip()
                if callable(resolver)
                else helper_name
            )
            helper = (
                helper_registry.get(resolved_name)
                if isinstance(helper_registry, Mapping)
                else None
            )
            source_hash = str(
                getattr(helper, "source_hash", "") or ""
            ).strip()
            if helper_name and source_hash:
                receipt = {"name": resolved_name, "source_hash": source_hash}
                if receipt not in durable_progress_helper_receipts:
                    durable_progress_helper_receipts.append(receipt)
        durable_progress_tool_continuation_identity = (
            _durable_progress_tool_continuation_identity(
                role=str(getattr(conv, "role", "") or ""),
                target_statement=str(
                    goal_statement_override
                    if goal_statement_override is not None
                    else getattr(conv, "goal_statement", "")
                ),
                pending_tool_replay=pending_tool_replay,
                helper_receipts=durable_progress_helper_receipts,
            )
        )
        durable_progress_tool_continuation_granted = bool(
            durable_progress_tool_continuation_identity
        )
    if persist_provider_continuation:
        setattr(
            conv,
            "_provider_call_quantum_state",
            {
                "schema_version": _PROVIDER_CALL_QUANTUM_STATE_SCHEMA_VERSION,
                "provider_turn_lane_identity": _provider_turn_lane_identity(
                    conv,
                    goal_statement_override,
                ),
                "provider_chain_resume_target_id": str(
                    provider_chain_resume_target_id or ""
                ),
                "invalid_prompt_neutralization_pending": bool(
                    invalid_prompt_neutralization_pending
                ),
                "tool_calls_used": int(tool_calls_used),
                "seen_tool_call_signatures": sorted(seen_tool_call_signatures),
                "max_tool_calls_per_turn": int(max_tool_calls_per_turn),
                "repair_discovery_tool_calls_used": int(
                    repair_discovery_tool_calls_used
                ),
                "repair_verification_tool_calls_used": int(
                    repair_verification_tool_calls_used
                ),
                "repair_discovery_quota_exhausted": bool(
                    repair_discovery_quota_exhausted
                    or repair_discovery_tool_calls_used
                    >= _REPAIR_DISCOVERY_TOOL_CALL_QUOTA
                ),
                "repair_self_check_required": bool(
                    repair_self_check_required
                ),
                "repair_self_check_seen": bool(repair_self_check_seen),
                "repair_self_check_attempted": bool(
                    repair_self_check_attempted
                ),
                "repair_self_check_status": str(
                    repair_self_check_status or ""
                ),
                "repair_self_check_codes": list(repair_self_check_codes),
                "repair_self_check_reminder_sent": bool(
                    repair_self_check_reminder_sent
                ),
                "repair_self_check_final_slot_recovery_reminder_sent": bool(
                    repair_self_check_final_slot_recovery_reminder_sent
                ),
                "pending_tool_replay": [
                    dict(call) for call in pending_tool_replay
                ],
                "pending_tool_replay_is_paid_retry": bool(
                    pending_tool_replay_is_paid_retry
                ),
                "pending_tool_replay_disposition": (
                    "durable_progress_cutpoint"
                    if durable_progress_tool_replay_pending
                    else ""
                ),
                "durable_progress_tool_continuation_identity": str(
                    durable_progress_tool_continuation_identity or ""
                ),
                "durable_progress_tool_continuation_role": str(
                    getattr(conv, "role", "") or ""
                ).strip(),
                "durable_progress_tool_continuation_target": str(
                    goal_statement_override
                    if goal_statement_override is not None
                    else getattr(conv, "goal_statement", "")
                ).strip(),
                "durable_progress_tool_continuation_helper_receipts": list(
                    durable_progress_helper_receipts
                ),
                "tool_infrastructure_receipt_id": str(
                    tool_infrastructure_receipt_id or ""
                ),
                "tool_infrastructure_disposition": str(
                    tool_infrastructure_disposition or ""
                ),
                "deepseek_dsml_reprompted_after_budget": bool(
                    deepseek_dsml_reprompted_after_budget
                ),
                "final_no_tools_policy_reprompted": bool(
                    final_no_tools_policy_reprompted
                ),
                "force_finalize_without_tools": bool(
                    force_finalize_without_tools
                ),
                "final_no_tools_recovery_attempted": bool(
                    final_no_tools_recovery_attempted
                ),
                "final_no_tools_visibility_recovery_pending": bool(
                    final_no_tools_visibility_recovery_pending
                ),
                "repeat_guidance_used": bool(repeat_guidance_used),
                "repeat_recovery_pending": bool(repeat_recovery_pending),
                "tool_repeat_detected": bool(tool_repeat_detected),
                "tool_repeat_action": str(tool_repeat_action or "")[:120],
                "tool_repeat_signature": str(tool_repeat_signature or "")[:256],
                "proof_tool_attempts": int(proof_tool_attempts),
                "consecutive_no_formal_progress": int(
                    consecutive_no_formal_progress
                ),
                "consecutive_search_tool_calls": int(
                    consecutive_search_tool_calls
                ),
                "search_cadence_violation_batches": int(
                    search_cadence_violation_batches
                ),
                "search_cadence_stall_detected": bool(
                    search_cadence_stall_detected
                ),
                "semantic_result_counts": {
                    str(signature or "")[:256]: min(
                        semantic_repeat_cap,
                        _nonnegative_int(count),
                    )
                    for signature, count in list(
                        semantic_result_counts.items()
                    )[:32]
                    if str(signature or "")
                },
                "semantic_no_progress_detected": bool(
                    semantic_no_progress_detected
                ),
                "semantic_no_progress_reason": str(
                    semantic_no_progress_reason or ""
                )[:120],
                "semantic_no_progress_signature": str(
                    semantic_no_progress_signature or ""
                )[:256],
                "semantic_diagnostic_progress_count": int(
                    semantic_diagnostic_progress_count
                ),
                "semantic_diagnostic_best_phase": int(
                    semantic_diagnostic_best_phase
                ),
                "semantic_diagnostic_best_error_kind": str(
                    semantic_diagnostic_best_error_kind or ""
                )[:120],
                "semantic_diagnostic_best_goal_count": int(
                    semantic_diagnostic_best_goal_count
                ),
                "semantic_diagnostic_last_reason": str(
                    semantic_diagnostic_last_reason or ""
                )[:120],
                "semantic_diagnostic_best_signature": str(
                    semantic_diagnostic_best_signature or ""
                )[:256],
                "semantic_diagnostic_best_by_tool": {
                    str(name or "")[:80]: {
                        "phase": int(state.phase),
                        "error_kind": str(state.error_kind or "")[:120],
                        "goal_count": (
                            None
                            if state.goal_count is None
                            else max(0, int(state.goal_count))
                        ),
                        "signature": str(state.signature or "")[:256],
                    }
                    for name, state in list(
                        semantic_diagnostic_best_by_tool.items()
                    )[:8]
                    if str(name or "")
                },
                "partial_try_lean_promotions": int(
                    partial_try_lean_promotions
                ),
                "banked_mixed_final_content": str(
                    banked_mixed_final_content or ""
                )[:100_000],
                "banked_mixed_finalizer_pending": bool(
                    banked_mixed_finalizer_pending
                ),
                "banked_mixed_finalizer_lane_identity": str(
                    banked_mixed_finalizer_lane_identity or ""
                )[:128],
                "provider_call_cumulative_elapsed_s": round(
                    provider_call_cumulative_elapsed_s,
                    6,
                ),
                "provider_call_cumulative_wall_cap_s": float(
                    provider_call_cumulative_wall_cap_s
                ),
                "provider_call_cumulative_deadline_monotonic": float(
                    provider_call_cumulative_deadline_monotonic
                ),
                "provider_call_cumulative_wall_exhausted": bool(
                    provider_call_cumulative_wall_exhausted
                ),
            },
        )
    elif hasattr(conv, "_provider_call_quantum_state"):
        delattr(conv, "_provider_call_quantum_state")

    return ToolLoopResult(
        content=content,
        tool_calls_used=tool_calls_used,
        tool_call_log=tool_call_log,
        llm_error=llm_error,
        llm_failure_kind=str(llm_failure_kind or ""),
        llm_retryable=bool(llm_retryable),
        llm_terminal=bool(llm_terminal),
        llm_failure_reason=str(llm_failure_reason or ""),
        sent_messages=list(sent_messages or []),
        elapsed_s=round(time.monotonic() - started, 3),
        repair_self_check_codes=list(repair_self_check_codes),
        repair_self_check_required=bool(repair_self_check_required),
        repair_self_check_attempted=bool(repair_self_check_attempted),
        repair_self_check_accepted=bool(repair_self_check_seen),
        repair_self_check_status=str(repair_self_check_status or ""),
        repair_self_check_missing_kind=str(repair_self_check_status or ""),
        repair_self_check_budget_exhausted=bool(repair_self_check_budget_exhausted),
        repair_self_check_helper_only_allowed=bool(
            repair_self_check_helper_only_allowed
        ),
        repair_discovery_tool_calls_used=int(
            repair_discovery_tool_calls_used
        ),
        repair_verification_tool_calls_used=int(
            repair_verification_tool_calls_used
        ),
        llm_retry_count=int(llm_retry_count),
        llm_retry_deadline=dict(llm_retry_deadline or {}),
        provider_defer=dict(provider_defer or {}),
        provider_attempts=list(provider_attempts or []),
        recovered_finalizer_error=str(recovered_finalizer_error or ""),
        recovered_finalizer_failure_kind=str(
            recovered_finalizer_failure_kind or ""
        ),
        recovered_finalizer_retryable=bool(recovered_finalizer_retryable),
        recovered_finalizer_provider_call_quantum_exhausted=bool(
            recovered_finalizer_provider_call_quantum_exhausted
        ),
        recovered_finalizer_terminal=bool(recovered_finalizer_terminal),
        recovered_finalizer_failure_reason=str(
            recovered_finalizer_failure_reason or ""
        ),
        recovered_finalizer_retry_deadline=dict(
            recovered_finalizer_retry_deadline or {}
        ),
        recovered_finalizer_provider_attempts=list(
            recovered_finalizer_provider_attempts or []
        ),
        recovered_finalizer_provider_defer=dict(
            recovered_finalizer_provider_defer or {}
        ),
        provider_protocol_event=str(provider_protocol_event or ""),
        provider_protocol_original_content=str(provider_protocol_original_content or ""),
        tool_state_updates=int(tool_state_updates),
        tool_state_closures=int(tool_state_closures),
        tool_state_update_statuses=list(tool_state_update_statuses),
        llm_turn_elapsed_budget_exhausted=bool(
            llm_turn_elapsed_budget_exhausted
        ),
        llm_turn_elapsed_task_unsettled=bool(llm_turn_elapsed_task_unsettled),
        llm_turn_elapsed_budget_s=float(max_turn_elapsed_f or 0.0),
        request_timeout_override_s=effective_request_timeout_s,
        operation_timeout_override_s=effective_operation_timeout_s,
        provider_timeout_lease_partitioned=bool(
            provider_timeout_lease_partitioned
        ),
        tool_repeat_detected=bool(tool_repeat_detected),
        tool_repeat_action=str(tool_repeat_action or ""),
        tool_repeat_signature=str(tool_repeat_signature or ""),
        proof_tool_attempts=int(proof_tool_attempts),
        consecutive_no_formal_progress=int(consecutive_no_formal_progress),
        consecutive_search_tool_calls=int(consecutive_search_tool_calls),
        search_cadence_violation_batches=int(search_cadence_violation_batches),
        search_cadence_stall_detected=bool(search_cadence_stall_detected),
        semantic_no_progress_detected=bool(semantic_no_progress_detected),
        semantic_no_progress_reason=str(semantic_no_progress_reason or ""),
        semantic_no_progress_signature=str(
            semantic_no_progress_signature or ""
        ),
        semantic_diagnostic_progress_count=int(
            semantic_diagnostic_progress_count
        ),
        semantic_diagnostic_best_phase=int(semantic_diagnostic_best_phase),
        semantic_diagnostic_best_error_kind=str(
            semantic_diagnostic_best_error_kind or ""
        ),
        semantic_diagnostic_best_goal_count=int(
            semantic_diagnostic_best_goal_count
        ),
        semantic_diagnostic_last_reason=str(
            semantic_diagnostic_last_reason or ""
        ),
        semantic_diagnostic_best_signature=str(
            semantic_diagnostic_best_signature or ""
        ),
        partial_try_lean_promotions=int(partial_try_lean_promotions),
        accepted_try_lean_helper_names=list(
            accepted_try_lean_helper_names
        ),
        durable_progress_tool_replay_pending=bool(
            durable_progress_tool_replay_pending
            and pending_tool_replay
        ),
        durable_progress_tool_replay_count=(
            len(pending_tool_replay)
            if durable_progress_tool_replay_pending
            else 0
        ),
        durable_progress_tool_replay_exhausted=bool(
            durable_progress_tool_replay_exhausted
        ),
        durable_progress_tool_replay_predecessor_identity=str(
            durable_progress_tool_replay_predecessor_identity or ""
        ),
        durable_progress_tool_continuation_identity=str(
            durable_progress_tool_continuation_identity or ""
        ),
        durable_progress_tool_continuation_granted=bool(
            durable_progress_tool_continuation_granted
            and durable_progress_tool_replay_pending
            and pending_tool_replay
        ),
        final_no_tools_event=str(final_no_tools_event or ""),
        final_no_tools_finish_reason=str(final_no_tools_finish_reason or ""),
        final_no_tools_reasoning_content_chars=int(
            final_no_tools_reasoning_content_chars or 0
        ),
        final_no_tools_used_accepted_proof=bool(
            final_no_tools_used_accepted_proof
        ),
        authoritative_falsification=bool(authoritative_falsification),
        proof_disproof_conflict=bool(proof_disproof_conflict),
        authoritative_falsification_target=str(
            authoritative_falsification_target or ""
        ),
        authoritative_falsification_certificate_hash=str(
            authoritative_falsification_certificate_hash or ""
        ),
        authoritative_falsification_environment_hash=str(
            authoritative_falsification_environment_hash or ""
        ),
        in_turn_tool_history_compactions=int(in_turn_tool_history_compactions),
        in_turn_tool_history_compacted_messages=int(
            in_turn_tool_history_compacted_messages
        ),
        in_turn_tool_history_compacted_tool_rounds=int(
            in_turn_tool_history_compacted_tool_rounds
        ),
        in_turn_tool_history_compacted_chars=int(
            in_turn_tool_history_compacted_chars
        ),
        provider_calls_completed=int(provider_calls_completed),
        provider_dispatches_started=int(provider_dispatches_started),
        failed_provider_pre_generation_rejection=bool(
            failed_provider_pre_generation_rejection
        ),
        provider_call_quantum_exhausted=bool(provider_call_quantum_exhausted),
        provider_finalizer_continuation_exhausted=bool(
            provider_finalizer_continuation_exhausted
        ),
        provider_call_elapsed_s=round(provider_call_elapsed_s, 3),
        provider_call_quantum_max_retries=int(
            provider_call_quantum_max_retries
        ),
        provider_call_cumulative_elapsed_s=round(
            provider_call_cumulative_elapsed_s,
            3,
        ),
        provider_call_cumulative_wall_cap_s=float(
            provider_call_cumulative_wall_cap_s
        ),
        provider_call_cumulative_wall_exhausted=bool(
            provider_call_cumulative_wall_exhausted
        ),
        paid_tool_infrastructure_disposition=str(
            paid_tool_infrastructure_disposition or ""
        ),
        paid_tool_continuation_identity=str(
            paid_tool_continuation_identity or ""
        ),
        paid_tool_continuation_granted=bool(
            paid_tool_continuation_granted
        ),
    )


async def call_llm_with_tools_one_round(*args: Any, **kwargs: Any) -> ToolLoopResult:
    """Run one turn under the isolated worker's process-level deadline lease.

    An elapsed or abnormally cancelled turn deliberately leaves its lease
    armed.  The parent then terminates the worker after a bounded cleanup
    grace, so a resistant task or descendant cannot survive into a later turn
    or block ``asyncio.run`` shutdown.  Outside a supervised CLI worker the
    lease is a no-op and the long-standing cooperative API remains available.
    """

    lease = begin_process_deadline(
        deadline_monotonic=_tool_loop_process_deadline_monotonic(kwargs),
        label="mini_session_tool_turn",
    )
    try:
        result = await _call_llm_with_tools_one_round_impl(*args, **kwargs)
    except asyncio.CancelledError:
        # Repeated external cancellation can interrupt asyncio's own
        # cancellation drain before the wrapped task settles.  Fail closed;
        # shared-process parallel cancellation is rejected by the CLI.
        lease.abandon("tool_turn_external_cancellation")
        raise
    except BaseException:
        lease.close()
        raise
    turn_deadline_exhausted = bool(
        getattr(result, "llm_turn_elapsed_budget_exhausted", False)
    )
    provider_deadline_exhausted = bool(
        getattr(result, "provider_call_cumulative_wall_exhausted", False)
    )
    deadline_task_unsettled = bool(
        getattr(result, "llm_turn_elapsed_task_unsettled", False)
    )
    if turn_deadline_exhausted or provider_deadline_exhausted:
        if deadline_task_unsettled:
            lease.abandon(
                "llm_turn_elapsed_task_unsettled"
                if turn_deadline_exhausted
                else "llm_provider_deadline_task_unsettled"
            )
        else:
            lease.settle_timeout()
    else:
        lease.close()
    return result
