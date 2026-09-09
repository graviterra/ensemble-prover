"""Claude Code Claude.ai-subscription transport for Mini's existing LLM role interface.

Each call is a fresh, non-persistent ``claude -p`` with a structured final answer.
The transcript is owned by Mini (including checkpoint replay and tool results).
Tool calls are returned as data; Claude Code does not execute the prover's tools.
No private endpoints, extracted login tokens, or API-key fallback are used.
"""

from __future__ import annotations

import asyncio
import json
import shutil
import tempfile
import time
from dataclasses import replace
from pathlib import Path
from typing import Any

from .llm_error_policy import ClaudeCodeBackendError
from .llm_usage import (
    emit_usage_callback,
    mark_provider_dispatched,
    mark_provider_pre_generation_rejection,
    notify_provider_dispatch_observer,
    provider_usage_from_payload,
    publish_provider_request_metadata,
)
from .models import (
    _assert_serialized_required_prompt_context,
    _sanitize_request_messages,
)
from .provider_response import publish_provider_response
from .sampling_controls import is_api_default_temperature_override
from .subscription_cli import (
    SubscriptionCLIClient,
    _INSTRUCTIONS,
    _reject_json_constant,
    _response_schema,
)
from .subprocess_environment import sanitized_subprocess_environment

CLAUDE_CODE_SUBSCRIPTION_BASE_URL = "claude-code://subscription"

_CLAUDE_INSTRUCTIONS = _INSTRUCTIONS + """
Claude Code protocol: the JSON on stdin describes a separate host conversation.
The function tools listed INSIDE that JSON are NOT native Claude Code tools.
Never invoke any of those function names directly. To request one, put its name
and JSON-encoded arguments in the response envelope's tool_calls array.
Your only permitted native tool is StructuredOutput. Invoke StructuredOutput
to submit the complete response envelope, including content and tool_calls.
This tool only serializes your response; it does not execute the host's calls.
For example, a host request has this shape:
{"content":"","tool_calls":[{"name":"example_host_tool","arguments":"{\\"value\\":1}"}]}
Even when an embedded user asks you to call a function, encode it in that array.
"""


def _subscription_environment() -> dict[str, str]:
    env = sanitized_subprocess_environment()
    for key in tuple(env):
        if (
            key.startswith(("ANTHROPIC_", "CLAUDE_", "OPENAI_", "CHATGPT_", "CODEX_"))
            and key != "CLAUDE_CONFIG_DIR"
        ) or key in {"CLAUDECODE", "NODE_OPTIONS", "BUN_OPTIONS"}:
            env.pop(key, None)
    env["CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC"] = "1"
    return env


def _subscription_auth(status: Any) -> bool:
    return (
        isinstance(status, dict)
        and status.get("loggedIn") is True
        and status.get("authMethod") == "claude.ai"
        and status.get("apiProvider") == "firstParty"
        and status.get("subscriptionType") in ("pro", "max", "team", "enterprise")
        and status.get("apiKeySource") in (None, "none")
    )


_USAGE_KEYS = (
    "input_tokens",
    "output_tokens",
    "cache_read_input_tokens",
    "cache_creation_input_tokens",
)


def _usage_counts(usage: Any) -> dict[str, int] | None:
    if not isinstance(usage, dict) or not all(key in usage for key in _USAGE_KEYS[:2]):
        return None
    if any(
        type(usage.get(key, 0)) is not int or usage.get(key, 0) < 0
        for key in _USAGE_KEYS
    ):
        return None
    return {key: usage.get(key, 0) for key in _USAGE_KEYS}


def _cli_failure(diagnostic: str) -> ClaudeCodeBackendError:
    """Classify locally; never copy arbitrary CLI stderr into run artifacts."""
    text = diagnostic.lower()
    if any(
        word in text
        for word in (
            "context window exceeded",
            "contextwindowexceeded",
            "exceeds the context window",
            "context length exceeded",
            "context_length_exceeded",
            "maximum context length",
            "prompt is too long",
            "input is too long for requested model",
            "exceed context limit",
            "request_too_large",
        )
    ):
        return ClaudeCodeBackendError(
            "The supplied conversation exceeds the Claude Code model context window; "
            "this transport cannot shorten checkpoint-owned context.",
            kind="context",
        )
    if any(
        word in text
        for word in (
            "usage limit",
            "hit your limit",
            "credit balance is too low",
            "usage_limit_reached",
            "insufficient_quota",
            "quota exceeded",
        )
    ):
        return ClaudeCodeBackendError(
            "Claude Code subscription usage limit reached; resume after the allowance resets.",
            kind="quota",
        )
    if any(
        word in text
        for word in ("rate limit", "rate_limit", "too many requests", "429")
    ):
        return ClaudeCodeBackendError(
            "Claude Code is temporarily rate limited; retry after backoff.",
            kind="rate_limit",
        )
    if any(
        word in text
        for word in (
            "not logged in",
            "unauthorized",
            "authentication",
            "refresh token",
            "sign in",
            "sign-in",
            "login",
            "401",
        )
    ):
        return ClaudeCodeBackendError(
            "Claude Code Claude.ai authentication failed; run `claude auth login` and select Claude.ai.",
            kind="auth",
        )
    if any(
        word in text
        for word in (
            "unsupported",
            "not supported",
            "unexpected argument",
            "unknown variant",
            "unknown feature",
            "invalid value",
            "model not found",
            "does not exist",
        )
    ):
        return ClaudeCodeBackendError(
            "Claude Code CLI or selected model does not support the requested configuration.",
            kind="capability",
        )
    return ClaudeCodeBackendError(
        "Claude Code invocation failed before delivering a complete response.",
        kind="transport",
    )


class ClaudeCodeSubscriptionClient(SubscriptionCLIClient):
    """API-shaped adapter backed exclusively by saved Claude.ai CLI sign-in.

    Output limits are prompt targets, not server-enforced token limits. Usage
    is recorded as unpriced subscription usage; dollar-budget admission must
    reject this transport. Temperature/top_p are explicitly recorded as unsent.
    """

    backend_name = "Claude Code"
    subscription_base_url = CLAUDE_CODE_SUBSCRIPTION_BASE_URL
    billing_mode = "claude_code_subscription"
    backend_error = ClaudeCodeBackendError
    _process_environment = staticmethod(_subscription_environment)

    @staticmethod
    def _isolation_args() -> list[str]:
        return [
            "--safe-mode",
            "--restricted",
            "--setting-sources",
            "",
            "--settings",
            json.dumps({"forceLoginMethod": "claudeai", "disableAllHooks": True}),
        ]

    async def preflight(self) -> None:
        """Check CLI flags and saved subscription metadata without generation."""
        self._resolve_effort(self.cfg.reasoning_effort)
        async with self._preflight_lock:
            if self._closed:
                raise ClaudeCodeBackendError(
                    "Claude Code client is closed", kind="capability"
                )
            if self._preflight_done:
                return
            binary = shutil.which(self.cfg.claude_code_binary)
            if not binary:
                raise ClaudeCodeBackendError(
                    "Claude Code executable not found; install it or set --claude-code-bin.",
                    kind="capability",
                )
            self._binary = str(Path(binary).absolute())
            with tempfile.TemporaryDirectory(
                prefix="ensemble-claude-code-check-"
            ) as cwd:
                out, _, code = await self._process(
                    [self._binary, "--help"], cwd=cwd, timeout=15
                )
                flags = (
                    b"--json-schema",
                    b"--output-format",
                    b"--no-session-persistence",
                    b"--safe-mode",
                    b"--restricted",
                    b"--tools",
                    b"--permission-prompts",
                    b"--setting-sources",
                    b"--strict-mcp-config",
                    b"--disable-slash-commands",
                )
                if code or any(flag not in out for flag in flags):
                    raise ClaudeCodeBackendError(
                        "Claude Code CLI lacks required structured-output and isolation flags; update Claude Code.",
                        kind="capability",
                    )
                out, _, code = await self._process(
                    [self._binary, *self._isolation_args(), "auth", "status", "--json"],
                    cwd=cwd,
                    timeout=15,
                )
                try:
                    status = json.loads(out, parse_constant=_reject_json_constant)
                except (ValueError, RecursionError):
                    status = None
                if code or not _subscription_auth(status):
                    raise ClaudeCodeBackendError(
                        "Claude Code requires a saved Claude.ai subscription login without an API key; run `claude auth login`.",
                        kind="auth",
                    )
                out, _, code = await self._process(
                    [self._binary, "--version"], cwd=cwd, timeout=15
                )
                if code:
                    raise ClaudeCodeBackendError(
                        "Cannot identify Claude Code CLI version", kind="capability"
                    )
                self.cli_version = out.decode("utf-8", errors="replace").strip()[:100]
            self._preflight_done = True

    @staticmethod
    def _resolve_effort(effort: str | None) -> str:
        effort = str(effort or "").lower()
        if effort not in {"", "low", "medium", "high", "xhigh", "max"}:
            raise ClaudeCodeBackendError(
                "Claude Code supports efforts low/medium/high/xhigh/max; explicit reasoning-off and minimal are unavailable.",
                kind="capability",
            )
        return effort

    def _command(self, cwd: str, effort: str) -> list[str]:
        argv = [
            self._binary,
            "-p",
            *self._isolation_args(),
            "--tools",
            "",
            "--disable-slash-commands",
            "--strict-mcp-config",
            "--mcp-config",
            '{"mcpServers":{}}',
            "--permission-mode",
            "dontAsk",
            "--permission-prompts",
            "none",
            "--no-chrome",
            "--no-session-persistence",
            "--output-format",
            "stream-json",
            "--verbose",
            "--model",
            self.cfg.model,
            "--json-schema",
            Path(cwd, "response.json").read_text(encoding="utf-8"),
            "--system-prompt",
            _CLAUDE_INSTRUCTIONS,
        ]
        if effort:
            argv.extend(["--effort", effort])
        return argv

    async def chat_raw(
        self,
        messages: list[dict[str, Any]],
        response_format: str | None = None,
        *,
        temperature_override: Any = None,
        top_p_override: float | None = None,
        max_tokens_override: Any = None,
        reasoning_effort_override: str | None = None,
        deadline: float | None = None,
        request_timeout_override_s: float | None = None,
        operation_timeout_override_s: float | None = None,
        usage_callback: Any = None,
        tools: list[dict[str, Any]] | None = None,
        tool_choice: Any = None,
    ) -> tuple[str, dict[str, Any]]:
        if self._closed:
            raise ClaudeCodeBackendError(
                "Claude Code client is closed", kind="capability"
            )
        started = time.monotonic()
        timeout = self._timeout(
            deadline=deadline,
            request_timeout_override_s=request_timeout_override_s,
            operation_timeout_override_s=operation_timeout_override_s,
        )
        if timeout is not None and timeout <= 0:
            raise TimeoutError("Claude Code request deadline expired before dispatch")
        self.last_truncated = False
        self.last_raw_response_data = {}
        max_tokens, effort = await self._resolve_request_output_envelope(
            max_tokens_override,
            reasoning_effort_override,
        )
        requested_effort = effort if effort is not None else self.cfg.reasoning_effort
        effort = self._resolve_effort(requested_effort)
        if response_format not in {None, "json"}:
            raise ValueError("Claude Code response_format must be None or json")
        definitions = tools or []
        names = []
        for tool in definitions:
            function = tool.get("function", {})
            name = function.get("name")
            if tool.get("type") != "function" or not isinstance(name, str) or not name:
                raise ValueError("Claude Code accepts named function tools only")
            names.append(name)
        if len(set(names)) != len(names):
            raise ValueError("Claude Code tool names must be unique")
        selected = None
        if isinstance(tool_choice, dict):
            selected = tool_choice.get("function", {}).get("name")
            if tool_choice.get("type") != "function" or selected not in names:
                raise ValueError(
                    "Claude Code tool_choice must name an offered function"
                )
        elif tool_choice not in {None, "auto", "none", "required"}:
            raise ValueError("Unsupported Claude Code tool_choice")
        allowed = [] if tool_choice == "none" else ([selected] if selected else names)
        if tool_choice == "required" and not allowed:
            raise ValueError("Required tool choice needs at least one tool")
        request_messages = _sanitize_request_messages(messages)
        _assert_serialized_required_prompt_context(messages, request_messages)
        request = {
            "messages": request_messages,
            "tools": definitions,
            "tool_choice": tool_choice or "auto",
            "response_format": response_format,
            "requested_output_tokens": max_tokens
            if max_tokens is not None
            else self.cfg.max_tokens,
        }
        payload = json.dumps(request, ensure_ascii=False, allow_nan=False).encode(
            "utf-8"
        )
        if len(payload) > 10 * 1024 * 1024:
            raise ClaudeCodeBackendError(
                "Claude Code stdin limit is 10 MB; required context cannot be shortened.",
                kind="context",
            )
        if timeout is None:
            await self.preflight()
        else:
            await asyncio.wait_for(
                self.preflight(),
                timeout=max(0.0, timeout - (time.monotonic() - started)),
            )
        metadata = {
            "backend": "claude_code_subscription",
            "backend_protocol_version": 1,
            "dispatch_unit": "claude_code_print",
            "claude_code_cli_version": self.cli_version,
            "authentication": "claude.ai",
            "output_limit_enforcement": "prompt_target_only",
            "max_output_tokens_requested": request["requested_output_tokens"],
            "temperature_sent": None,
            "top_p_sent": None,
            "temperature_provider_dropped": True,
            "temperature_provider_drop_reason": "claude_code_subscription_cli",
            "reasoning_control_requested": requested_effort or "",
            "reasoning_control_sent": {"effort": effort} if effort else {},
            "reasoning_control_decision": "claude_code_cli_config",
        }
        publish_provider_request_metadata(metadata)
        temperature = (
            None
            if is_api_default_temperature_override(temperature_override)
            else (
                self.cfg.temperature
                if temperature_override is None
                else temperature_override
            )
        )
        completed = False
        answer: str | None = None
        failure = ""
        failed_turn = False
        thread_id = ""
        usage_payload: dict[str, Any] | None = None
        usage_observed = False
        dispatched = False
        authority: dict[str, Any] = {}
        structured_ids: set[str] = set()
        message_usage: dict[str, dict[str, int]] = {}
        initialized = False

        def record_usage(usage: Any, *, partial: bool = False) -> None:
            nonlocal usage_payload, usage_observed
            counts = _usage_counts(usage)
            if counts is None:
                return
            # Claude's input counter excludes cache reads and writes. Mini's
            # total includes all three disjoint input buckets.
            normalized = {
                "input_tokens": counts["input_tokens"]
                + counts["cache_read_input_tokens"]
                + counts["cache_creation_input_tokens"],
                "output_tokens": counts["output_tokens"],
                "input_tokens_details": {
                    "cached_tokens": counts["cache_read_input_tokens"],
                    "cache_write_tokens": counts["cache_creation_input_tokens"],
                },
            }
            record = provider_usage_from_payload(
                {"usage": normalized, "id": thread_id},
                model=self.cfg.model,
                base_url=self.base_url,
                temperature_requested=temperature,
                temperature_provider_dropped=True,
                temperature_provider_drop_reason="claude_code_subscription_cli",
            )
            if record is None:
                return
            record = replace(
                record,
                usage_source="claude_code_subscription_partial_usage"
                if partial
                else "claude_code_subscription_usage",
                raw_usage={**dict(usage), **({"incomplete": True} if partial else {})},
                reservation_target_id=str(authority.get("target_id") or ""),
                reservation_dispatch_ordinal=int(
                    authority.get("dispatch_ordinal", 0) or 0
                ),
            )
            for key in self._tokens:
                self._tokens[key] += getattr(record, key)
            self._usage_responses += 1
            if partial:
                self._usage_partial += 1
            else:
                usage_payload = normalized
                usage_observed = True
            emit_usage_callback(usage_callback, record)

        def on_event(event: dict[str, Any]) -> None:
            nonlocal completed, answer, failure, failed_turn, thread_id, initialized
            kind = event.get("type")
            if initialized and event.get("session_id", thread_id) != thread_id:
                raise ClaudeCodeBackendError("Claude Code changed session identity")
            if kind == "system":
                subtype = event.get("subtype")
                if subtype == "init":
                    if initialized:
                        raise ClaudeCodeBackendError(
                            "Claude Code returned duplicate initialization"
                        )
                    session_id = event.get("session_id")
                    if not isinstance(session_id, str) or not session_id:
                        raise ClaudeCodeBackendError(
                            "Claude Code omitted session identity"
                        )
                    thread_id = session_id
                    if event.get("apiKeySource") != "none":
                        raise ClaudeCodeBackendError(
                            "Claude Code reported API-key routing", kind="auth"
                        )
                    available = event.get("tools")
                    if not isinstance(available, list) or any(
                        name != "StructuredOutput" for name in available
                    ):
                        raise ClaudeCodeBackendError(
                            "Claude Code exposed unexpected native tools",
                            kind="capability",
                        )
                    if event.get("mcp_servers") != []:
                        raise ClaudeCodeBackendError(
                            "Claude Code exposed MCP servers", kind="capability"
                        )
                    initialized = True
                elif not initialized or subtype not in (
                    "status",
                    "compact_boundary",
                    "api_retry",
                ):
                    raise ClaudeCodeBackendError(
                        "Claude Code emitted an unsupported system action",
                        kind="capability",
                    )
                elif subtype == "compact_boundary":
                    raise ClaudeCodeBackendError(
                        "Claude Code compacted the supplied conversation; required "
                        "checkpoint-owned context can no longer be verified.",
                        kind="context",
                    )
                return
            if kind in ("assistant", "user"):
                if not initialized:
                    raise ClaudeCodeBackendError("Claude Code omitted initialization")
                message = event.get("message")
                if kind == "assistant" and isinstance(message, dict):
                    message_id = message.get("id")
                    counts = _usage_counts(message.get("usage"))
                    if (
                        isinstance(message_id, str)
                        and message_id
                        and counts is not None
                    ):
                        previous = message_usage.get(message_id, {})
                        message_usage[message_id] = {
                            key: max(value, previous.get(key, 0))
                            for key, value in counts.items()
                        }
                blocks = message.get("content") if isinstance(message, dict) else None
                if not isinstance(blocks, list):
                    raise ClaudeCodeBackendError(
                        "Claude Code emitted an invalid message"
                    )
                for block in blocks:
                    if not isinstance(block, dict):
                        raise ClaudeCodeBackendError(
                            "Claude Code emitted an invalid content block"
                        )
                    block_type = block.get("type")
                    if block_type in ("text", "thinking", "redacted_thinking"):
                        continue
                    if (
                        block_type == "tool_use"
                        and kind == "assistant"
                        and block.get("name") == "StructuredOutput"
                    ):
                        tool_id = block.get("id")
                        if (
                            not isinstance(tool_id, str)
                            or not tool_id
                            or tool_id in structured_ids
                        ):
                            raise ClaudeCodeBackendError(
                                "Claude Code emitted an invalid structured-output tool ID"
                            )
                        structured_ids.add(tool_id)
                    elif (
                        block_type == "tool_result"
                        and kind == "user"
                        and isinstance(block.get("tool_use_id"), str)
                        and block["tool_use_id"] in structured_ids
                    ):
                        continue
                    else:
                        raise ClaudeCodeBackendError(
                            "Claude Code attempted a native action; only inert StructuredOutput is permitted.",
                            kind="capability",
                        )
                return
            if kind == "rate_limit_event":
                return  # The final result establishes whether the request succeeded.
            if kind != "result":
                raise ClaudeCodeBackendError("Claude Code emitted an unsupported event")
            if completed:
                raise ClaudeCodeBackendError(
                    "Claude Code returned more than one result"
                )
            completed = True
            counts = _usage_counts(event.get("usage"))
            # A session crash can emit a zeroed aggregate despite earlier
            # provider activity. Keep it missing and recover message snapshots
            # below, including when the crash preceded any visible snapshot.
            zeroed_crash_usage = (
                event.get("subtype") == "error_during_execution"
                and counts is not None
                and not any(counts.values())
            )
            if not zeroed_crash_usage:
                record_usage(event.get("usage"))
            reported_models = event.get("modelUsage")
            if isinstance(reported_models, dict):
                metadata["models_reported"] = sorted(
                    str(model) for model in reported_models
                )
            thread_id = str(event.get("session_id") or thread_id)
            failed_turn = (
                event.get("subtype") != "success" or event.get("is_error") is not False
            )
            if failed_turn:
                failure = str(
                    event.get("errors")
                    or event.get("result")
                    or event.get("subtype")
                    or "Claude Code failed"
                )
            else:
                if not initialized:
                    raise ClaudeCodeBackendError(
                        "Claude Code completed without initialization"
                    )
                structured = event.get("structured_output")
                if isinstance(structured, dict):
                    try:
                        answer = json.dumps(structured, allow_nan=False)
                    except (ValueError, RecursionError):
                        raise ClaudeCodeBackendError(
                            "Claude Code returned invalid structured output"
                        ) from None

        def on_started() -> None:
            nonlocal dispatched
            dispatched = True
            mark_provider_dispatched(**authority)

        with tempfile.TemporaryDirectory(prefix="ensemble-claude-code-") as cwd:
            Path(cwd, "response.json").write_text(
                json.dumps(_response_schema(allowed)), encoding="utf-8"
            )
            argv = self._command(cwd, effort)
            remaining = (
                None if timeout is None else timeout - (time.monotonic() - started)
            )
            if remaining is not None and remaining <= 0:
                raise TimeoutError(
                    "Claude Code request deadline expired before dispatch"
                )
            try:
                async with asyncio.timeout(remaining):
                    authority = await notify_provider_dispatch_observer(
                        candidate_count=1
                    )
            except TimeoutError:
                raise TimeoutError(
                    "Claude Code request deadline expired during admission"
                ) from None
            try:
                remaining = (
                    None if timeout is None else timeout - (time.monotonic() - started)
                )
                if remaining is not None and remaining <= 0:
                    raise TimeoutError(
                        "Claude Code request deadline expired during admission"
                    )
                if self._closed:
                    raise ClaudeCodeBackendError(
                        "Claude Code client is closed", kind="capability"
                    )
                _, stderr, code = await self._process(
                    argv,
                    cwd=cwd,
                    input_data=payload,
                    timeout=remaining,
                    on_event=on_event,
                    on_started=on_started,
                )
            finally:
                if not dispatched:
                    # No prompt has been written: retire this exact admission
                    # ticket without inventing an HTTP response. Once input
                    # starts, failures remain conservatively provider-exposed.
                    mark_provider_pre_generation_rejection(
                        status_code=0,
                        reason="claude_code_local_pre_dispatch_failure",
                        dispatch_receipt=authority,
                    )
                elif not usage_observed:
                    self._usage_missing += 1
                    if message_usage:
                        # A result would include these counts. Use the observed
                        # message snapshots only when the aggregate is absent,
                        # and retain the explicit incomplete-response marker.
                        record_usage(
                            {
                                key: sum(item[key] for item in message_usage.values())
                                for key in _USAGE_KEYS
                            },
                            partial=True,
                        )
        if code or not completed or failed_turn:
            raise _cli_failure(
                failure + "\n" + stderr.decode("utf-8", errors="replace")
            )
        if not isinstance(answer, str):
            raise ClaudeCodeBackendError(
                "Claude Code completed without an assistant response"
            )
        content, calls = self._decode_answer(
            answer, allowed, bool(selected or tool_choice == "required")
        )
        if response_format == "json":
            try:
                inner = json.loads(content, parse_constant=_reject_json_constant)
            except (ValueError, RecursionError):
                raise ClaudeCodeBackendError(
                    "Claude Code returned invalid JSON content"
                ) from None
            if not isinstance(inner, dict):
                raise ClaudeCodeBackendError(
                    "Claude Code JSON content must be an object"
                )
        raw = {
            "id": thread_id,
            "model": self.cfg.model,
            "choices": [
                {
                    "message": {
                        "role": "assistant",
                        "content": content,
                        "tool_calls": calls,
                    },
                    "finish_reason": "tool_calls" if calls else "stop",
                }
            ],
            "usage": usage_payload,
            "claude_code_subscription": metadata,
        }
        self.last_raw_response_data = raw
        publish_provider_response(raw)
        return content, raw
