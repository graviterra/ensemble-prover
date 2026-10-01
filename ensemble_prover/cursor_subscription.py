"""Cursor subscription transport.

The examined CLI is unqualified for prover generation. Startup hooks outside
CURSOR_CONFIG_DIR are not suppressed, and internal context compaction is not
reliably suppressed or detected. Model calls and preflight refuse before a
process starts. Ask mode, a tool-prohibition prompt, sandbox enabled, force,
and trust are not isolation. No launch argv is constructed.
"""

from __future__ import annotations

import hashlib
import os
from collections.abc import Mapping
from pathlib import Path
from typing import Any, NoReturn

from .cursor_wire import decode_cursor_stream_event
from .llm_error_policy import CursorBackendError
from .subscription_cli import (
    SubscriptionCLIClient,
    bounded_subscription_transport,
)
from .subprocess_environment import sanitized_subprocess_environment

CURSOR_SUBSCRIPTION_BASE_URL = "cursor://subscription"
_LOGIN_DIR = "cursor"
_BLOCKING = (
    "startup_hooks_outside_cursor_config_dir",
    "context_compaction_not_reliably_suppressed_or_detected",
)
_C0 = (
    "The installed Cursor CLI is unqualified for prover generation. "
    "Startup hooks outside CURSOR_CONFIG_DIR are not suppressed. "
    "Internal context compaction is not reliably suppressed or detected, "
    "so a terminal success would not prove the checkpoint-owned conversation "
    "was preserved. This process did not launch the agent."
)
_DENIED_PREFIXES = (
    "ANTHROPIC_",
    "CHATGPT_",
    "CLAUDE_",
    "CODEX_",
    "CURSOR_",
    "DEEPSEEK_",
    "OPENAI_",
    "OPENROUTER_",
)
_DENIED_EXACT = frozenset(
    {
        "ALL_PROXY",
        "HTTP_PROXY",
        "HTTPS_PROXY",
        "NO_PROXY",
        "NODE_EXTRA_CA_CERTS",
        "NODE_OPTIONS",
        "NODE_PATH",
    }
)
_DENIED_SUFFIXES = ("_API_BASE", "_BASE_URL", "_ENDPOINT", "_HEADER", "_HEADERS")


def cursor_unqualified_explanation(*, executable: str, model: str) -> str:
    shown_executable = str(executable or "").strip() or "(unset)"
    shown_model = str(model or "").strip() or "(unset)"
    return (
        "Selected provider cursor (cursor://subscription) "
        f"executable={shown_executable} model={shown_model}. "
        + _C0
        + " Ask mode, a prompt that forbids tools, sandbox enabled, force, "
        "and trust do not establish isolation. Generation was not started. "
        "No other provider was substituted. Use a different provider, or a "
        "Cursor build that has passed isolation and context-preservation "
        f"checks. blocking_reasons={','.join(_BLOCKING)}."
    )


def cursor_child_environment_denied(name: str) -> bool:
    upper = str(name or "").upper()
    return (
        upper in _DENIED_EXACT
        or upper.startswith(_DENIED_PREFIXES)
        or upper.endswith(_DENIED_SUFFIXES)
    )


def cursor_saved_login_directory(env: Mapping[str, str]) -> str:
    """Saved-login directory. Does not open auth.json.

    Scope follows XDG_CONFIG_HOME or ~/.config, never CURSOR_CONFIG_DIR.
    The observed Linux CLI uses credential-store domain "cursor".
    """

    xdg = str(env.get("XDG_CONFIG_HOME") or "").strip()
    if xdg:
        root = Path(xdg).expanduser()
    else:
        home = str(env.get("HOME") or "").strip()
        root = (Path(home).expanduser() if home else Path.home()) / ".config"
    return str(root / _LOGIN_DIR)


class CursorSubscriptionClient(SubscriptionCLIClient):
    """Saved-login Cursor transport. The examined build never launches."""

    backend_name = "Cursor"
    subscription_base_url = CURSOR_SUBSCRIPTION_BASE_URL
    billing_mode = "cursor_subscription"
    backend_error = CursorBackendError

    def _decode_stream_event(self, line: bytes) -> Any:
        return decode_cursor_stream_event(line)

    def _account_scope_environment(self) -> Mapping[str, str]:
        return os.environ

    def _subscription_account_key(self) -> str:
        directory = cursor_saved_login_directory(self._account_scope_environment())
        identity = self.subscription_base_url + "\n" + directory
        return hashlib.sha256(identity.encode("utf-8")).hexdigest()

    def _process_environment_from(self, base: Mapping[str, str]) -> dict[str, str]:
        filtered = {
            key: value
            for key, value in dict(base).items()
            if not cursor_child_environment_denied(key)
        }
        return sanitized_subprocess_environment(filtered)

    def _process_environment(self) -> dict[str, str]:
        return self._process_environment_from(os.environ)

    def _explicit_reasoning_requested(self) -> bool:
        effort = str(getattr(self.cfg, "reasoning_effort", "") or "").strip()
        return bool(
            getattr(self.cfg, "reasoning_control_required", False)
            or getattr(self.cfg, "thinking_enabled", False)
            or effort
        )

    def validate_requested_controls(self) -> None:
        super().validate_requested_controls()
        if self._explicit_reasoning_requested():
            raise self.backend_error(
                "Cursor has no evidenced reasoning on/off or effort control. "
                "provider-default leaves the account model default unlabeled. "
                "No reasoning flag is sent. Remove the explicit reasoning "
                "request, or use a provider with an evidenced control.",
                kind="capability",
            )

    def readiness_diagnostic(self) -> dict[str, Any]:
        return {
            "provider": "cursor",
            "transport": CURSOR_SUBSCRIPTION_BASE_URL,
            "model": self.cfg.model,
            "executable": str(getattr(self.cfg, "cursor_binary", "") or ""),
            "billing_mode": self.billing_mode,
            "generation_qualified": False,
            "launched": False,
            "blocking_reasons": list(_BLOCKING),
            "output_limit_enforcement": "unavailable",
            "hard_output_limit": False,
            "reasoning_control": (
                "unsupported_explicit"
                if self._explicit_reasoning_requested()
                else "provider_default_unlabeled"
            ),
            "auth_scope": "xdg_saved_login_store",
            "auth_scope_ignores": "CURSOR_CONFIG_DIR",
        }

    def _unqualified_backend_error(self) -> CursorBackendError:
        return CursorBackendError(
            cursor_unqualified_explanation(
                executable=str(getattr(self.cfg, "cursor_binary", "") or ""),
                model=str(self.cfg.model),
            ),
            kind="compatibility",
        )

    def _reject_non_text_attachments(self, messages: Any) -> None:
        if not isinstance(messages, list) or any(
            not isinstance(message, dict) for message in messages
        ):
            raise self.backend_error(
                "Cursor requests must be a list of object messages. " + _C0,
                kind="capability",
            )
        for message in messages:
            content = message.get("content")
            if content is None or isinstance(content, str):
                continue
            parts = content if isinstance(content, list) else [content]
            if any(
                not (
                    isinstance(item, dict)
                    and item.get("type") == "text"
                    and isinstance(item.get("text"), str)
                )
                for item in parts
            ):
                raise self.backend_error(
                    "Cursor rejects image and document attachments before dispatch. "
                    "They are not flattened or discarded. " + _C0,
                    kind="capability",
                )

    def generation_command(self) -> NoReturn:
        raise self._unqualified_backend_error()

    async def preflight(self) -> None:
        self.validate_requested_controls()
        if self._closed:
            raise self.backend_error("Cursor client is closed", kind="capability")
        self._binary = str(getattr(self.cfg, "cursor_binary", "") or "")
        raise self._unqualified_backend_error()

    @bounded_subscription_transport
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
        del (
            response_format,
            temperature_override,
            top_p_override,
            max_tokens_override,
            deadline,
            request_timeout_override_s,
            operation_timeout_override_s,
            usage_callback,
            tools,
            tool_choice,
        )
        if self._closed:
            raise self.backend_error("Cursor client is closed", kind="capability")
        if str(reasoning_effort_override or "").strip():
            raise self.backend_error(
                "Cursor has no evidenced reasoning effort control. The override was not encoded as a CLI flag.",
                kind="capability",
            )
        self._reject_non_text_attachments(messages)
        raise self._unqualified_backend_error()

    async def chat_n(
        self,
        messages: list[dict[str, Any]],
        n: int,
        response_format: str | None = None,
        **kwargs: Any,
    ) -> list[str]:
        await self.chat_raw(messages, response_format, **kwargs)
        raise AssertionError(
            f"Cursor chat_raw returned for n={n} on an unqualified build"
        )
