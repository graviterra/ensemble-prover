"""Cursor CLI NDJSON state for one subscription invocation.

``SubscriptionCLIClient`` reads stdout, JSON-decodes each object, then calls
``on_event`` and ``on_progress``. This module is that decoder. It does not
spawn ``agent``, read credentials, or report that isolation passed.

``accept`` consumes one object from ``on_event``. ``on_progress`` must return
``renews_inactivity_lease`` for that same event and must not call ``accept``
again. A thinking delta, an assistant delta, or a non-streaming assistant
message can renew the inactivity lease only for a new text, timestamp, and
event-kind identity. Initialization, the user echo, heartbeats, duplicate
flushes, and repeated echoes cannot. Identities are fixed-size digests in a
hard-capped set; exceeding the cap fails the stream instead of forgetting one.

``complete(returncode)`` returns one immutable receipt after a single login
initialization, one session, a successful terminal result, and exit code 0.
``result_text`` is only the terminal ``result`` string. Thinking text,
assistant deltas, and flushes stay out of that string. Host-envelope
validation stays in ``CursorSubscriptionClient._decode_answer``.

The observed profile records the installed event names and leaves context
rewrite markers, cache-read overlap, and internal call counts unproven, so
it cannot produce a receipt. ``feed`` and ``finish_stream`` apply the same
rules to raw NDJSON fragments. The shared reader already splits lines, so an
adapter uses ``accept`` for that path and does not feed those bytes again.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Callable, NoReturn, TypeGuard, TypeVar

from .llm_error_policy import CursorBackendError
from .subscription_cli import _MAX_STREAM_BYTES, _reject_json_constant

_T = TypeVar("_T")
_MAX_COUNT = 2**63 - 1
_MAX_ID_CHARS = 128
_MAX_MODEL_CHARS = 256
_MAX_PERMISSION_CHARS = 64
_MAX_MARKER_CHARS = 64
_MAX_BLOCKS = 1024
# Do not evict; a full set fails the stream so an older replay cannot renew.
_MAX_REPLAY_HISTORY = 65536
_USAGE_FIELDS = ("inputTokens", "outputTokens", "cacheReadTokens", "cacheWriteTokens")
_TOKEN_FIELDS = frozenset(_USAGE_FIELDS)
_LEASE_PROGRESS = frozenset({"assistant_delta", "assistant_message", "thinking_delta"})
_PROGRESS_CLASSES = _LEASE_PROGRESS | frozenset(
    {
        "initialization",
        "user_echo",
        "duplicate_flush",
        "assistant_echo",
        "thinking_echo",
        "thinking_completed",
        "heartbeat",
        "terminal_result",
    }
)
_NATIVE_BLOCK_TYPES = frozenset(
    {
        "tool_use",
        "tool_call",
        "tool_result",
        "function_call",
    }
)
OBSERVED_CURSOR_STREAM_SCHEMA_ID = "cursor-agent-stream-json-observed"

__all__ = [
    "CursorBackendError",
    "CursorStreamProfile",
    "CursorUsageReceipt",
    "CursorWireDecoder",
    "CursorWireEffect",
    "CursorWireReceipt",
    "decode_cursor_stream_event",
    "OBSERVED_CURSOR_STREAM_SCHEMA_ID",
    "observed_cursor_stream_profile",
]


def _json_object(pairs: list[tuple[Any, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise ValueError("duplicate JSON key")
        value[key] = item
    return value


def decode_cursor_stream_event(raw: bytes | str) -> Any:
    """Decode one Cursor stdout JSON value and reject duplicate keys."""

    return json.loads(
        raw,
        parse_constant=_reject_json_constant,
        object_pairs_hook=_json_object,
    )


def _valid_schema_id(value: object) -> bool:
    if type(value) is not str or not 1 <= len(value) <= 80 or not value.isascii():
        return False
    if value[0] not in "abcdefghijklmnopqrstuvwxyz0123456789":
        return False
    return all(
        character.isdigit() or character.islower() or character in "._:-"
        for character in value
    )


def _valid_marker_part(value: object, *, empty_ok: bool) -> bool:
    if (
        type(value) is not str
        or len(value) > _MAX_MARKER_CHARS
        or not value.isascii()
        or any(character.isspace() for character in value)
    ):
        return False
    return bool(value) or empty_ok


def _valid_field_name(value: object) -> bool:
    if type(value) is not str or not 1 <= len(value) <= 64 or not value.isascii():
        return False
    return value[0].isalpha() and all(
        character.isalnum() or character == "_" for character in value
    )


def _valid_bounded_id(value: object) -> TypeGuard[str]:
    return (
        type(value) is str
        and 1 <= len(value) <= _MAX_ID_CHARS
        and value.isascii()
        and not any(character.isspace() for character in value)
    )


def _valid_model(value: object) -> bool:
    return (
        type(value) is str
        and bool(value.strip())
        and len(value) <= _MAX_MODEL_CHARS
        and "\n" not in value
        and "\r" not in value
        and "\x00" not in value
    )


def _valid_permission(value: object) -> bool:
    return (
        type(value) is str
        and bool(value)
        and len(value) <= _MAX_PERMISSION_CHARS
        and "\n" not in value
        and "\r" not in value
        and "\x00" not in value
    )


def _valid_count(value: object) -> bool:
    return type(value) is int and 0 <= value <= _MAX_COUNT


def _bad_usage(detail: str) -> NoReturn:
    raise ValueError(f"Cursor usage receipt is invalid: {detail}")


def _bad_receipt(detail: str) -> NoReturn:
    raise ValueError(f"Cursor wire receipt is invalid: {detail}")


def _advertised(event: dict[str, Any], key: str) -> bool | None:
    if key not in event:
        return None
    value = event[key]
    if type(value) is not list:
        return None
    return bool(value)


@dataclass(frozen=True)
class CursorStreamProfile:
    """Supported-version stream contract. Defaults grant no unproven authority.

    ``input_tokens_include_cache_reads`` is ``None`` until a profile has
    evidence that ``inputTokens`` includes or excludes ``cacheReadTokens``.
    ``reports_internal_call_counts`` stays false until the profile names the
    usage field that carries that count. Isolation is not a field here.
    """

    schema_id: str
    context_rewrite_events: frozenset[tuple[str, str]] = frozenset()
    context_rewrite_prevented: bool = False
    context_rewrite_control_id: str = ""
    input_tokens_include_cache_reads: bool | None = None
    reports_internal_call_counts: bool = False
    internal_call_count_field: str = ""
    require_user_echo: bool = True

    def __post_init__(self) -> None:
        if not _valid_schema_id(self.schema_id):
            raise ValueError("Cursor stream profile schema_id is invalid")
        if (
            type(self.context_rewrite_prevented) is not bool
            or type(self.require_user_echo) is not bool
        ):
            raise ValueError("Cursor stream profile flag is invalid")
        if type(self.reports_internal_call_counts) is not bool:
            raise ValueError("Cursor stream profile flag is invalid")
        if type(self.context_rewrite_events) is not frozenset:
            raise ValueError(
                "Cursor stream profile context markers must be a frozenset"
            )
        for item in self.context_rewrite_events:
            if (
                type(item) is not tuple
                or len(item) != 2
                or not _valid_marker_part(item[0], empty_ok=False)
                or not _valid_marker_part(item[1], empty_ok=True)
            ):
                raise ValueError("Cursor stream profile context marker is invalid")
        overlap = self.input_tokens_include_cache_reads
        if overlap is not None and type(overlap) is not bool:
            raise ValueError("Cursor stream profile cache overlap is unproven")
        if self.context_rewrite_prevented:
            if not _valid_schema_id(self.context_rewrite_control_id):
                raise ValueError("Cursor stream profile context control is unproven")
        elif self.context_rewrite_control_id != "":
            raise ValueError(
                "Cursor stream profile context control requires prevention evidence"
            )
        if self.reports_internal_call_counts:
            if (
                self.internal_call_count_field in _TOKEN_FIELDS
                or not _valid_field_name(self.internal_call_count_field)
            ):
                raise ValueError(
                    "Cursor stream profile internal call count is unproven"
                )
        elif self.internal_call_count_field != "":
            raise ValueError(
                "Cursor stream profile internal call count requires evidence"
            )


def observed_cursor_stream_profile() -> CursorStreamProfile:
    """Installed stream-json shapes with strict defaults.

    Thinking deltas use top-level ``text``. Context-rewrite names were not
    identified, cache overlap is unknown, and internal call counts are not
    in the observed usage object. This profile cannot complete a receipt.
    """

    return CursorStreamProfile(schema_id=OBSERVED_CURSOR_STREAM_SCHEMA_ID)


@dataclass(frozen=True)
class CursorUsageReceipt:
    """Terminal usage only. Normalized totals exist solely when status is complete."""

    status: str
    schema_id: str
    origin: str
    fields: tuple[tuple[str, int], ...]
    cache_read_included_in_input: bool | None
    internal_call_count_in_contract: bool
    input_tokens: int | None = None
    output_tokens: int | None = None
    cache_read_tokens: int | None = None
    cache_write_tokens: int | None = None
    prompt_cache_miss_tokens: int | None = None
    internal_call_count: int | None = None

    def __post_init__(self) -> None:
        if not _valid_schema_id(self.schema_id):
            _bad_usage("schema")
        if type(self.internal_call_count_in_contract) is not bool:
            _bad_usage("calls")
        overlap = self.cache_read_included_in_input
        if overlap is not None and type(overlap) is not bool:
            _bad_usage("overlap")
        if self.origin not in {"absent", "usage_object", "result_fields"}:
            _bad_usage("origin")
        if self.status not in {"absent", "partial", "complete"}:
            _bad_usage("status")
        if type(self.fields) is not tuple:
            _bad_usage("fields")
        seen: list[str] = []
        for item in self.fields:
            if (
                type(item) is not tuple
                or len(item) != 2
                or type(item[0]) is not str
                or item[0] not in _TOKEN_FIELDS
                or not _valid_count(item[1])
            ):
                _bad_usage("fields")
            seen.append(item[0])
        if seen != [key for key in _USAGE_FIELDS if key in seen] or len(seen) != len(
            set(seen)
        ):
            _bad_usage("fields")
        totals = (
            self.input_tokens,
            self.output_tokens,
            self.cache_read_tokens,
            self.cache_write_tokens,
            self.prompt_cache_miss_tokens,
        )
        if self.internal_call_count is not None and not _valid_count(
            self.internal_call_count
        ):
            _bad_usage("calls")
        if (
            not self.internal_call_count_in_contract
            and self.internal_call_count is not None
        ):
            _bad_usage("calls")
        if self.status == "absent":
            if (
                self.fields
                or self.origin != "absent"
                or self.internal_call_count is not None
                or any(item is not None for item in totals)
            ):
                _bad_usage("absent")
            return
        if self.origin == "absent":
            _bad_usage("origin")
        if self.status == "partial":
            if any(item is not None for item in totals):
                _bad_usage("totals")
            return
        if (
            any(type(item) is not int for item in totals[:4])
            or type(overlap) is not bool
        ):
            _bad_usage("totals")
        raw = dict(self.fields)
        if tuple(raw) != _USAGE_FIELDS:
            _bad_usage("fields")
        if (
            raw["inputTokens"] != self.input_tokens
            or raw["outputTokens"] != self.output_tokens
            or raw["cacheReadTokens"] != self.cache_read_tokens
            or raw["cacheWriteTokens"] != self.cache_write_tokens
        ):
            _bad_usage("totals")
        if overlap:
            if (
                self.cache_read_tokens is None
                or self.input_tokens is None
                or self.cache_read_tokens > self.input_tokens
                or self.prompt_cache_miss_tokens
                != self.input_tokens - self.cache_read_tokens
            ):
                _bad_usage("overlap")
        elif self.prompt_cache_miss_tokens is not None:
            _bad_usage("overlap")
        if (
            self.internal_call_count_in_contract
            and type(self.internal_call_count) is not int
        ):
            _bad_usage("calls")


@dataclass(frozen=True)
class CursorWireEffect:
    """One accepted event. Lease renewal is limited to genuine generation classes."""

    renews_inactivity_lease: bool
    phase: str
    progress_class: str

    def __post_init__(self) -> None:
        if type(self.renews_inactivity_lease) is not bool:
            raise ValueError("Cursor wire effect is invalid")
        if self.progress_class not in _PROGRESS_CLASSES or self.phase not in {
            "progress",
            "terminal",
        }:
            raise ValueError("Cursor wire effect is invalid")
        terminal = self.progress_class == "terminal_result"
        if (self.phase == "terminal") != terminal:
            raise ValueError("Cursor wire effect is invalid")
        if self.renews_inactivity_lease and self.progress_class not in _LEASE_PROGRESS:
            raise ValueError("Cursor progress class cannot renew the inactivity lease")


@dataclass(frozen=True)
class CursorWireReceipt:
    """Final invocation record. ``isolation_passed`` cannot be true."""

    schema_id: str
    session_id: str
    result_text: str
    usage: CursorUsageReceipt
    auth_source: str
    reported_model: str | None
    model_identity: str
    request_id: str | None
    reported_permission_mode: str | None
    native_tools_advertised: bool | None
    mcp_servers_advertised: bool | None
    isolation_passed: bool
    context_preservation: str
    context_rewrite_control_id: str
    returncode: int
    input_tokens_include_cache_reads: bool | None
    reports_internal_call_counts: bool

    def __post_init__(self) -> None:
        if self.isolation_passed is not False:
            _bad_receipt("isolation")
        if self.auth_source != "login" or self.returncode != 0:
            _bad_receipt("exit")
        if not _valid_schema_id(self.schema_id) or not _valid_bounded_id(
            self.session_id
        ):
            _bad_receipt("identity")
        if type(self.result_text) is not str:
            _bad_receipt("result")
        try:
            result_size = len(self.result_text.encode("utf-8"))
        except UnicodeEncodeError:
            _bad_receipt("result")
        if result_size > _MAX_STREAM_BYTES:
            _bad_receipt("result")
        if self.context_preservation == "prevented_by_control":
            if not _valid_schema_id(self.context_rewrite_control_id):
                _bad_receipt("context control")
        elif self.context_preservation == "markers_not_observed":
            if self.context_rewrite_control_id != "":
                _bad_receipt("context control")
        else:
            _bad_receipt("context preservation")
        if self.model_identity == "absent":
            if self.reported_model is not None:
                _bad_receipt("model")
        elif self.model_identity == "display_name_unresolved":
            if not _valid_model(self.reported_model):
                _bad_receipt("model")
        else:
            _bad_receipt("model")
        if self.request_id is not None and not _valid_bounded_id(self.request_id):
            _bad_receipt("request")
        if self.reported_permission_mode is not None and not _valid_permission(
            self.reported_permission_mode
        ):
            _bad_receipt("permission")
        if (
            self.native_tools_advertised is not None
            and type(self.native_tools_advertised) is not bool
        ):
            _bad_receipt("tools")
        if (
            self.mcp_servers_advertised is not None
            and type(self.mcp_servers_advertised) is not bool
        ):
            _bad_receipt("tools")
        overlap = self.input_tokens_include_cache_reads
        if overlap is not None and type(overlap) is not bool:
            _bad_receipt("usage")
        if (
            type(self.reports_internal_call_counts) is not bool
            or type(self.usage) is not CursorUsageReceipt
        ):
            _bad_receipt("usage")
        if (
            self.usage.schema_id != self.schema_id
            or self.usage.cache_read_included_in_input != overlap
            or self.usage.internal_call_count_in_contract
            != self.reports_internal_call_counts
        ):
            _bad_receipt("usage")


class CursorWireDecoder:
    """One Cursor stdout stream. Not safe to share across invocations."""

    def __init__(
        self,
        profile: CursorStreamProfile | None = None,
        *,
        max_event_bytes: int | None = None,
    ) -> None:
        if profile is None:
            profile = observed_cursor_stream_profile()
        if type(profile) is not CursorStreamProfile:
            raise ValueError("Cursor stream profile is invalid")
        limit = _MAX_STREAM_BYTES if max_event_bytes is None else max_event_bytes
        if type(limit) is not int or not 1 <= limit <= _MAX_STREAM_BYTES:
            raise ValueError("Cursor event size limit is invalid")
        self._profile = profile
        self._max_event_bytes = limit
        self._pending = bytearray()
        self._phase = "awaiting_init"
        self._closed = False
        self._failed: CursorBackendError | None = None
        self._renews = False
        self._receipt: CursorWireReceipt | None = None
        self._session_id = ""
        self._reported_model: str | None = None
        self._model_identity = "absent"
        self._permission: str | None = None
        self._native_tools: bool | None = None
        self._mcp_servers: bool | None = None
        self._request_id: str | None = None
        self._usage: CursorUsageReceipt | None = None
        self._result_text = ""
        self._user_echoes = 0
        self._saw_assistant_delta = False
        self._seen_replay: set[bytes] = set()
        self._terminal_ok = False

    @property
    def phase(self) -> str:
        return self._phase

    @property
    def failed(self) -> bool:
        return self._failed is not None

    @property
    def receipt(self) -> CursorWireReceipt | None:
        return self._receipt

    @property
    def renews_inactivity_lease(self) -> bool:
        """Lease bit for the event just accepted. ``on_progress`` returns this."""

        return self._renews

    def _invoke(self, call: Callable[[], _T]) -> _T:
        try:
            return call()
        except (TypeError, UnicodeEncodeError):
            self._fail(
                CursorBackendError(
                    "Cursor emitted a malformed event",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )

    def accept(self, event: dict[str, Any]) -> CursorWireEffect:
        """Record one object from the shared reader's ``on_event`` callback."""

        self._check_open()
        return self._invoke(lambda: self._accept_open(event))

    def _accept_open(self, event: dict[str, Any]) -> CursorWireEffect:
        if self._pending:
            self._fail(
                CursorBackendError(
                    "Cursor stream ended with an incomplete NDJSON fragment"
                )
            )
        return self._accept_event(event)

    def feed(self, chunk: bytes) -> tuple[CursorWireEffect, ...]:
        """Accept every complete NDJSON line in an arbitrary stdout fragment."""

        self._check_open()
        return self._invoke(lambda: self._feed_chunk(chunk))

    def _feed_chunk(self, chunk: bytes) -> tuple[CursorWireEffect, ...]:
        if type(chunk) is not bytes:
            self._fail(CursorBackendError("Cursor emitted invalid JSONL"))
        if len(chunk) > _MAX_STREAM_BYTES:
            self._fail(
                CursorBackendError("Cursor response exceeds transport size limit")
            )
        self._pending.extend(chunk)
        effects: list[CursorWireEffect] = []
        while True:
            newline = self._pending.find(b"\n")
            if newline < 0:
                if len(self._pending) > self._max_event_bytes:
                    self._fail(
                        CursorBackendError(
                            "Cursor response exceeds transport size limit"
                        )
                    )
                return tuple(effects)
            raw = bytes(self._pending[:newline])
            if raw.endswith(b"\r"):
                raw = raw[:-1]
            if len(raw) > self._max_event_bytes:
                self._fail(
                    CursorBackendError("Cursor response exceeds transport size limit")
                )
            del self._pending[: newline + 1]
            effects.append(self._accept_event(self._loads(raw)))

    def finish_stream(self) -> tuple[CursorWireEffect, ...]:
        """Accept a final line that had no newline, or reject a partial fragment."""

        self._check_open()
        return self._invoke(self._finish_open)

    def _finish_open(self) -> tuple[CursorWireEffect, ...]:
        if not self._pending:
            return ()
        raw = bytes(self._pending)
        if raw.endswith(b"\r"):
            raw = raw[:-1]
        if len(raw) > self._max_event_bytes:
            self._fail(
                CursorBackendError("Cursor response exceeds transport size limit")
            )
        self._pending.clear()
        return (self._accept_event(self._loads(raw)),)

    def complete(self, returncode: object) -> CursorWireReceipt:
        """Seal the receipt. A second call cannot change or reissue it."""

        self._check_open()
        if self._pending:
            self._fail(
                CursorBackendError(
                    "Cursor stream ended with an incomplete NDJSON fragment",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        if (
            type(returncode) is not int
            or self._phase != "terminal"
            or not self._terminal_ok
            or self._usage is None
        ):
            self._fail(
                CursorBackendError("Cursor exited without a successful terminal result")
            )
        if returncode != 0:
            self._fail(
                CursorBackendError(
                    "Cursor terminal success conflicts with process exit",
                    ambiguous_provider_completion=True,
                )
            )
        if self._profile.require_user_echo and self._user_echoes != 1:
            self._fail(
                CursorBackendError(
                    "Cursor omitted the user echo",
                    ambiguous_provider_completion=True,
                )
            )
        preservation = self._context_preservation()
        if preservation is None:
            self._fail(
                CursorBackendError(
                    "Cursor stream profile does not establish context preservation",
                    kind="compatibility",
                )
            )
        control_id = (
            self._profile.context_rewrite_control_id
            if preservation == "prevented_by_control"
            else ""
        )
        receipt = CursorWireReceipt(
            schema_id=self._profile.schema_id,
            session_id=self._session_id,
            result_text=self._result_text,
            usage=self._usage,
            auth_source="login",
            reported_model=self._reported_model,
            model_identity=self._model_identity,
            request_id=self._request_id,
            reported_permission_mode=self._permission,
            native_tools_advertised=self._native_tools,
            mcp_servers_advertised=self._mcp_servers,
            isolation_passed=False,
            context_preservation=preservation,
            context_rewrite_control_id=control_id,
            returncode=0,
            input_tokens_include_cache_reads=self._profile.input_tokens_include_cache_reads,
            reports_internal_call_counts=self._profile.reports_internal_call_counts,
        )
        self._receipt = receipt
        self._closed = True
        self._phase = "closed"
        self._result_text = ""
        self._usage = None
        self._renews = False
        self._clear_progress_text()
        return receipt

    def _check_open(self) -> None:
        if self._failed is not None:
            raise self._failed
        if self._closed:
            raise CursorBackendError("Cursor stream receipt is already final")

    def _fail(self, exc: CursorBackendError) -> NoReturn:
        self._renews = False
        self._terminal_ok = False
        self._result_text = ""
        self._usage = None
        self._clear_progress_text()
        current = self._failed
        if current is None:
            self._failed = exc
            current = exc
        raise current

    def _clear_progress_text(self) -> None:
        self._seen_replay.clear()

    def _loads(self, raw: bytes) -> dict[str, Any]:
        try:
            event = decode_cursor_stream_event(raw)
        except (ValueError, UnicodeDecodeError, RecursionError):
            self._fail(
                CursorBackendError(
                    "Cursor emitted invalid JSONL",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        if type(event) is not dict:
            self._fail(
                CursorBackendError(
                    "Cursor emitted a non-object event",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        return event

    def _accept_event(self, event: dict[str, Any]) -> CursorWireEffect:
        self._check_open()
        if type(event) is not dict:
            self._fail(CursorBackendError("Cursor emitted a non-object event"))
        kind, subtype = self._pair(event)
        if (kind, subtype) in self._profile.context_rewrite_events:
            self._fail(
                CursorBackendError(
                    "Cursor rewrote the supplied conversation; required checkpoint-owned "
                    "context can no longer be verified.",
                    kind="context",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        if kind == "tool_call":
            self._fail(
                CursorBackendError(
                    "Cursor attempted a native tool call; host tools must stay in the response envelope.",
                    kind="capability",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        if self._phase == "terminal":
            if kind == "result":
                self._fail(
                    CursorBackendError(
                        "Cursor returned more than one terminal result",
                        ambiguous_provider_completion=True,
                    )
                )
            self._fail(
                CursorBackendError(
                    "Cursor emitted events after the terminal result",
                    ambiguous_provider_completion=True,
                )
            )
        if kind == "system" and subtype == "init":
            return self._accept_init(event)
        if self._phase == "awaiting_init":
            self._fail(
                CursorBackendError("Cursor emitted an event before initialization")
            )
        self._require_session(event)
        if (kind == "heartbeat" and subtype == "") or (
            kind == "system" and subtype == "heartbeat"
        ):
            self._optional_timestamp(event, "Cursor emitted an unexpected event")
            return self._effect("heartbeat")
        if kind == "user" and subtype == "":
            return self._accept_user(event)
        if kind == "assistant" and subtype == "":
            return self._accept_assistant(event)
        if kind == "thinking" and subtype in {"delta", "completed"}:
            return self._accept_thinking(event, subtype)
        if kind == "result":
            return self._accept_result(event, subtype)
        self._fail(
            CursorBackendError(
                "Cursor emitted an unexpected event", kind="compatibility"
            )
        )

    def _accept_init(self, event: dict[str, Any]) -> CursorWireEffect:
        if self._phase != "awaiting_init":
            self._fail(
                CursorBackendError("Cursor returned more than one initialization")
            )
        session = event.get("session_id")
        if not _valid_bounded_id(session):
            self._fail(
                CursorBackendError("Cursor initialization omitted session identity")
            )
        if "apiKeySource" not in event:
            self._fail(
                CursorBackendError(
                    "Cursor initialization omitted auth source; login was not proved.",
                    kind="auth",
                )
            )
        if event.get("apiKeySource") != "login":
            self._fail(
                CursorBackendError(
                    "Cursor reported a non-login auth source.",
                    kind="auth",
                )
            )
        if "model" in event:
            model = event["model"]
            if type(model) is not str:
                self._fail(
                    CursorBackendError("Cursor emitted a malformed initialization")
                )
            if not _valid_model(model):
                self._fail(
                    CursorBackendError("Cursor emitted a malformed initialization")
                )
            reported_model = model
            identity = "display_name_unresolved"
        else:
            reported_model = None
            identity = "absent"
        permission = None
        if "permissionMode" in event:
            permission = event.get("permissionMode")
            if not _valid_permission(permission):
                self._fail(
                    CursorBackendError("Cursor emitted a malformed initialization")
                )
        if "cwd" in event:
            cwd = event.get("cwd")
            if type(cwd) is not str:
                self._fail(
                    CursorBackendError("Cursor emitted a malformed initialization")
                )
            self._check_size(cwd)
        native_tools = _advertised(event, "tools")
        mcp_servers = _advertised(event, "mcp_servers")
        self._session_id = session
        self._reported_model = reported_model
        self._model_identity = identity
        self._permission = permission
        self._native_tools = native_tools
        self._mcp_servers = mcp_servers
        self._phase = "progress"
        return self._effect("initialization")

    def _accept_user(self, event: dict[str, Any]) -> CursorWireEffect:
        if self._user_echoes:
            self._fail(CursorBackendError("Cursor emitted more than one user echo"))
        message = event.get("message")
        if type(message) is not dict or message.get("role") != "user":
            self._fail(CursorBackendError("Cursor emitted a malformed user echo"))
        self._content_text(message)
        self._user_echoes += 1
        return self._effect("user_echo")

    def _accept_assistant(self, event: dict[str, Any]) -> CursorWireEffect:
        message = event.get("message")
        if type(message) is not dict or message.get("role") != "assistant":
            self._fail(CursorBackendError("Cursor emitted a malformed assistant event"))
        text = self._content_text(message)
        timestamp_present = "timestamp_ms" in event
        call_present = "model_call_id" in event
        timestamp = self._optional_timestamp(
            event, "Cursor emitted a malformed assistant event"
        )
        if call_present:
            call_id = event.get("model_call_id")
            if not _valid_bounded_id(call_id):
                self._fail(
                    CursorBackendError("Cursor emitted a malformed assistant event")
                )
            if not timestamp_present:
                self._fail(
                    CursorBackendError("Cursor emitted a conflicting assistant event")
                )
            self._saw_assistant_delta = True
            return self._effect("duplicate_flush")
        if timestamp_present:
            if self._replayed("assistant_delta", text, timestamp):
                return self._effect("assistant_echo")
            self._saw_assistant_delta = True
            return self._effect("assistant_delta", renew=text != "")
        if self._saw_assistant_delta:
            return self._effect("duplicate_flush")
        if self._replayed("assistant_message", text, None):
            return self._effect("assistant_echo")
        return self._effect("assistant_message", renew=text != "")

    def _accept_thinking(self, event: dict[str, Any], subtype: str) -> CursorWireEffect:
        if subtype == "completed":
            if "text" in event:
                text = event.get("text")
                if type(text) is not str:
                    self._fail(
                        CursorBackendError("Cursor emitted a malformed thinking event")
                    )
                self._check_size(text)
            if "timestamp_ms" in event:
                self._optional_timestamp(
                    event, "Cursor emitted a malformed thinking event"
                )
            return self._effect("thinking_completed")
        if "text" not in event or type(event.get("text")) is not str:
            self._fail(CursorBackendError("Cursor emitted a malformed thinking event"))
        text = event["text"]
        self._check_size(text)
        timestamp = self._optional_timestamp(
            event, "Cursor emitted a malformed thinking event"
        )
        if self._replayed("thinking_delta", text, timestamp):
            return self._effect("thinking_echo")
        return self._effect("thinking_delta", renew=text != "")

    def _accept_result(self, event: dict[str, Any], subtype: str) -> CursorWireEffect:
        if (
            subtype == "success"
            and event.get("is_error") is False
            and type(event.get("result")) is str
        ):
            result_text = event["result"]
            self._check_size(result_text)
            for key in ("duration_ms", "duration_api_ms"):
                if key in event and not _valid_count(event.get(key)):
                    self._fail(
                        CursorBackendError(
                            "Cursor returned a conflicting terminal result"
                        )
                    )
            request_id = self._optional_id(
                event, "request_id", "Cursor returned a conflicting terminal result"
            )
            usage = self._usage_from_result(event)
            self._result_text = result_text
            self._request_id = request_id
            self._usage = usage
            self._phase = "terminal"
            self._terminal_ok = True
            return self._effect("terminal_result")
        if subtype == "success" or event.get("is_error") is False:
            self._fail(
                CursorBackendError("Cursor returned a conflicting terminal result")
            )
        self._fail(CursorBackendError("Cursor returned a non-success terminal result"))

    def _usage_from_result(self, event: dict[str, Any]) -> CursorUsageReceipt:
        profile = self._profile
        call_field = (
            profile.internal_call_count_field
            if profile.reports_internal_call_counts
            else ""
        )
        has_usage = "usage" in event
        has_tokens = any(key in event for key in _USAGE_FIELDS)
        has_call = bool(call_field) and call_field in event
        if not has_usage and not has_tokens and not has_call:
            return self._usage_receipt(
                status="absent", origin="absent", fields=(), call_count=None
            )
        if has_usage:
            usage = event.get("usage")
            if type(usage) is not dict:
                self._fail(
                    CursorBackendError("Cursor reported malformed terminal usage")
                )
            for key in _USAGE_FIELDS:
                self._require_same_count(event, usage, key)
            if call_field:
                self._require_same_count(event, usage, call_field)
            container: dict[str, Any] = usage
            origin = "usage_object"
        else:
            container = event
            origin = "result_fields"
        parsed: list[tuple[str, int]] = []
        for key in _USAGE_FIELDS:
            if key in container:
                parsed.append((key, self._token(container[key])))
        call_count = None
        if call_field:
            if call_field in container:
                call_count = self._token(container[call_field])
        overlap = profile.input_tokens_include_cache_reads
        tokens_complete = tuple(key for key, _value in parsed) == _USAGE_FIELDS
        call_ready = not profile.reports_internal_call_counts or call_count is not None
        if tokens_complete and overlap is not None and call_ready:
            raw = dict(parsed)
            if overlap and raw["cacheReadTokens"] > raw["inputTokens"]:
                self._fail(
                    CursorBackendError("Cursor reported conflicting terminal usage")
                )
            miss = raw["inputTokens"] - raw["cacheReadTokens"] if overlap else None
            return self._usage_receipt(
                status="complete",
                origin=origin,
                fields=tuple(parsed),
                call_count=call_count,
                input_tokens=raw["inputTokens"],
                output_tokens=raw["outputTokens"],
                cache_read_tokens=raw["cacheReadTokens"],
                cache_write_tokens=raw["cacheWriteTokens"],
                prompt_cache_miss_tokens=miss,
            )
        return self._usage_receipt(
            status="partial",
            origin=origin,
            fields=tuple(parsed),
            call_count=call_count,
        )

    def _usage_receipt(
        self,
        *,
        status: str,
        origin: str,
        fields: tuple[tuple[str, int], ...],
        call_count: int | None,
        input_tokens: int | None = None,
        output_tokens: int | None = None,
        cache_read_tokens: int | None = None,
        cache_write_tokens: int | None = None,
        prompt_cache_miss_tokens: int | None = None,
    ) -> CursorUsageReceipt:
        profile = self._profile
        return CursorUsageReceipt(
            status=status,
            schema_id=profile.schema_id,
            origin=origin,
            fields=fields,
            cache_read_included_in_input=profile.input_tokens_include_cache_reads,
            internal_call_count_in_contract=profile.reports_internal_call_counts,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cache_read_tokens=cache_read_tokens,
            cache_write_tokens=cache_write_tokens,
            prompt_cache_miss_tokens=prompt_cache_miss_tokens,
            internal_call_count=(
                call_count if profile.reports_internal_call_counts else None
            ),
        )

    def _require_same_count(
        self, event: dict[str, Any], usage: dict[str, Any], key: str
    ) -> None:
        if key not in event:
            return
        if key not in usage:
            self._fail(CursorBackendError("Cursor reported conflicting terminal usage"))
        if not _valid_count(event[key]) or not _valid_count(usage[key]):
            self._fail(CursorBackendError("Cursor reported malformed terminal usage"))
        if event[key] != usage[key]:
            self._fail(CursorBackendError("Cursor reported conflicting terminal usage"))

    def _token(self, value: Any) -> int:
        if not _valid_count(value):
            self._fail(CursorBackendError("Cursor reported malformed terminal usage"))
        return value

    def _replayed(self, kind: str, text: str, timestamp: int | None) -> bool:
        try:
            token = hashlib.sha256(
                json.dumps(
                    (kind, timestamp, text),
                    ensure_ascii=False,
                    separators=(",", ":"),
                    allow_nan=False,
                ).encode("utf-8")
            ).digest()
        except (TypeError, ValueError, UnicodeEncodeError):
            self._fail(CursorBackendError("Cursor replay identity cannot be bounded"))
        if token in self._seen_replay:
            return True
        if len(self._seen_replay) >= _MAX_REPLAY_HISTORY:
            self._fail(CursorBackendError("Cursor replay identity cannot be bounded"))
        self._seen_replay.add(token)
        return False

    def _content_text(self, message: dict[str, Any]) -> str:
        content = message.get("content")
        if type(content) is not list or not content or len(content) > _MAX_BLOCKS:
            self._fail(CursorBackendError("Cursor emitted a malformed message"))
        parts: list[str] = []
        for block in content:
            if type(block) is not dict:
                self._fail(CursorBackendError("Cursor emitted a malformed message"))
            block_type = block.get("type")
            if type(block_type) is str and block_type in _NATIVE_BLOCK_TYPES:
                self._fail(
                    CursorBackendError(
                        "Cursor attempted a native tool call; host tools must stay in the response envelope.",
                        kind="capability",
                        ambiguous_provider_completion=self._terminal_ok,
                    )
                )
            if block_type != "text":
                self._fail(
                    CursorBackendError(
                        "Cursor emitted an unsupported message block",
                        kind="compatibility",
                    )
                )
            text = block.get("text")
            if type(text) is not str:
                self._fail(CursorBackendError("Cursor emitted a malformed message"))
            self._check_size(text)
            parts.append(text)
        combined = "".join(parts)
        self._check_size(combined)
        return combined

    def _check_size(self, text: str) -> None:
        try:
            size = len(text.encode("utf-8"))
        except UnicodeEncodeError:
            self._fail(
                CursorBackendError(
                    "Cursor emitted a malformed event",
                    ambiguous_provider_completion=self._terminal_ok,
                )
            )
        if size > self._max_event_bytes:
            self._fail(
                CursorBackendError(
                    "Cursor event content exceeds the transport size limit"
                )
            )

    def _require_session(self, event: dict[str, Any]) -> None:
        if "session_id" not in event or not _valid_bounded_id(event.get("session_id")):
            self._fail(CursorBackendError("Cursor event omitted session identity"))
        if event.get("session_id") != self._session_id:
            self._fail(
                CursorBackendError(
                    "Cursor event session does not match the active session"
                )
            )

    def _pair(self, event: dict[str, Any]) -> tuple[str, str]:
        kind = event.get("type")
        if type(kind) is not str or not _valid_marker_part(kind, empty_ok=False):
            self._fail(
                CursorBackendError(
                    "Cursor emitted an unexpected event", kind="compatibility"
                )
            )
        if "subtype" not in event:
            return kind, ""
        subtype = event.get("subtype")
        if type(subtype) is not str or not _valid_marker_part(subtype, empty_ok=False):
            self._fail(
                CursorBackendError(
                    "Cursor emitted an unexpected event", kind="compatibility"
                )
            )
        return kind, subtype

    def _optional_timestamp(self, event: dict[str, Any], detail: str) -> int | None:
        if "timestamp_ms" not in event:
            return None
        value = event.get("timestamp_ms")
        if not _valid_count(value):
            self._fail(CursorBackendError(detail))
        return value

    def _optional_id(self, event: dict[str, Any], key: str, detail: str) -> str | None:
        if key not in event:
            return None
        value = event.get(key)
        if not _valid_bounded_id(value):
            self._fail(CursorBackendError(detail))
        return value

    def _effect(self, progress_class: str, *, renew: bool = False) -> CursorWireEffect:
        phase = "terminal" if self._phase == "terminal" else "progress"
        effect = CursorWireEffect(
            renews_inactivity_lease=renew,
            phase=phase,
            progress_class=progress_class,
        )
        self._renews = renew
        return effect

    def _context_preservation(self) -> str | None:
        if self._profile.context_rewrite_prevented:
            return "prevented_by_control"
        if self._profile.context_rewrite_events:
            return "markers_not_observed"
        return None
