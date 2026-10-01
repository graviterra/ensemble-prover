"""Admit one local chat request and send it once.

The constructor stores a binding. prepare_resources installs the shared
coordinator and the run ledger. request opens those records, reserves wall
time after admission, and returns one normalized chat response.
"""

from __future__ import annotations

import asyncio
import hashlib
import inspect
import json
import math
import os
from pathlib import Path
import secrets
import time
from typing import Any

import httpx

from .budget import LocalComputeLedger
from .capacity import CapacityCoordinator
from .config import freeze_request, load_private_worker_snapshot, require_auth_available
from .errors import LocalInferenceError
from .protocol import (
    LocalProtocolError,
    SSEAssembler,
    SealedChat,
    build_chat_request,
    loads_strict,
    seal_chat_response,
)
from .network_policy import require_inference_target
from .protocol_config import reasoning_request_body
from .roles import BINDING_KEYS
from .seams import (
    register_profile,
    release_if_not_dispatched,
    reserve_budget_for_admitted_permit,
)
from .strictload import atomic_write_json, durable_mutation, read_json_object

_MARKER = "resource_marker.json"
_MARKER_BYTES = 8192
_MARKER_FIELDS = frozenset(
    {
        "schema_version",
        "installation_id",
        "scope_id",
        "coordinator_id",
        "budget_id",
        "profile_hash",
        "initial_ceilings",
    }
)
_PREPARED = frozenset(BINDING_KEYS) | {"coordinator_id", "resource_marker"}
_POLL_S = 0.02
_USAGE = ("prompt_tokens", "completion_tokens", "total_tokens")


def prepare_resources(
    binding: dict[str, Any],
    *,
    allow_create: bool,
    max_dispatches: int | None = None,
    max_requested_output_tokens: int | None = None,
    max_observed_request_wall_s: int | None = None,
) -> dict[str, Any]:
    """Open a conserved grant or explicitly create one bounded by its profile."""
    if type(allow_create) is not bool:
        raise LocalInferenceError("invalid_field", "allow_create")
    cloned, resolved = _load_binding(binding)
    root, budget_root = _path(cloned["coordinator_root"]), _path(cloned["budget_root"])
    marker_path = budget_root / _MARKER
    _reject_symlink(marker_path)
    identity, limits = _limits(resolved)
    overrides = {
        "dispatches": max_dispatches,
        "requested_output_tokens": max_requested_output_tokens,
        "observed_request_wall_ms": (
            None
            if max_observed_request_wall_s is None
            else _positive_limit(max_observed_request_wall_s) * 1000
        ),
    }
    ceiling = _profile_ceilings(limits)
    for key, value in overrides.items():
        if value is not None:
            if _positive_limit(value) > ceiling[key]:
                raise LocalInferenceError("probe_budget_mismatch")
            ceiling[key] = value

    def reopen() -> dict[str, Any]:
        prepared = _resume(cloned, resolved, root, budget_root, marker_path)
        recorded = prepared["resource_marker"]["initial_ceilings"]
        if any(
            value is not None and value != recorded[key]
            for key, value in overrides.items()
        ):
            raise LocalInferenceError("probe_budget_mismatch")
        return prepared

    if marker_path.is_file():
        return reopen()
    if not allow_create or "resource_marker" in cloned:
        raise LocalInferenceError("coordinator_unavailable")
    # Serialize lifecycle initialization separately from coordinator/ledger locks.
    with durable_mutation(budget_root.parent / ".runtime_initialization"):
        if marker_path.is_file():
            return reopen()
        if budget_root.exists():
            if not (budget_root / "ledger.json").is_file():
                raise LocalInferenceError("ledger_lost")
            # A partial first install can recover only an unused grant. Once
            # activity exists, the missing marker loses the capacity incarnation
            # binding; creating a fresh coordinator would erase unknown work.
            state = LocalComputeLedger.open(budget_root).snapshot()
            if (
                state["reservations"]
                or state["extensions"]
                or any(state["consumed"].values())
                or any(state["reserved"].values())
            ):
                raise LocalInferenceError("ledger_lost")
        return _install(cloned, resolved, root, budget_root, identity, ceiling)


def _positive_limit(value: Any) -> int:
    if type(value) is not int or value < 1:
        raise LocalInferenceError("invalid_field", "budget_limit")
    return value


def _profile_ceilings(limits: Any) -> dict[str, int]:
    return {
        "dispatches": limits.max_local_dispatches,
        "requested_output_tokens": limits.max_local_requested_output_tokens,
        "observed_request_wall_ms": limits.max_local_observed_request_wall_s * 1000,
    }


def _check_ledger_grant(ledger: LocalComputeLedger, initial: dict[str, int]) -> None:
    state = ledger.snapshot()
    expected = dict(initial)
    for extension in state["extensions"]:
        for key in expected:
            expected[key] += extension[key]
    if state["ceilings"] != expected:
        raise LocalInferenceError("ledger_identity_mismatch")


class LocalRuntime:
    """One role binding. Construction does not create files or open a socket."""

    def __init__(self, binding: dict[str, Any]) -> None:
        cloned, resolved = _load_binding(binding)
        self._binding = cloned
        self._resolved = resolved
        self._incarnation = "i" + secrets.token_hex(8)

    def require_resources(self) -> tuple[CapacityCoordinator, LocalComputeLedger]:
        """Open the marked coordinator and ledger. Missing state is not recreated."""

        binding = self._binding
        if "resource_marker" not in binding or "coordinator_id" not in binding:
            raise LocalInferenceError("coordinator_unavailable")
        root = _path(binding["coordinator_root"])
        budget_root = _path(binding["budget_root"])
        marker_path = budget_root / _MARKER
        _reject_symlink(marker_path)
        if not marker_path.is_file():
            raise LocalInferenceError("ledger_lost")
        marker = read_json_object(
            marker_path, max_bytes=_MARKER_BYTES, corrupt_code="corrupt_coordinator"
        )
        if marker != binding["resource_marker"]:
            raise LocalInferenceError("coordinator_unavailable")
        identity, _ignored = _limits(self._resolved)
        coordinator = CapacityCoordinator.open(
            root,
            installation_id=identity.installation_id,
            scope_id=identity.scope_id,
        )
        if coordinator.coordinator_id() != binding["coordinator_id"]:
            raise LocalInferenceError("coordinator_unavailable")
        ledger = LocalComputeLedger.open(budget_root)
        ledger.require_resume_identity(
            ledger_id=binding["budget_id"],
            profile_hash=self._resolved.profile_hash,
        )
        _check_ledger_grant(ledger, marker["initial_ceilings"])
        return coordinator, ledger

    async def request(
        self,
        http_client: Any,
        messages: Any,
        tools: Any = None,
        tool_choice: Any = None,
        max_tokens: int | None = None,
        temperature: Any = None,
        top_p: Any = None,
        reasoning_effort: str | None = None,
        deadline: float | None = None,
        request_timeout_s: float | None = None,
        before_dispatch: Any = None,
        on_dispatched: Any = None,
    ) -> httpx.Response:
        if getattr(http_client, "trust_env", True) is not False:
            raise LocalInferenceError("proxy_inheritance_forbidden")
        if not callable(getattr(http_client, "send", None)):
            raise LocalInferenceError("invalid_field", "http_client")
        coordinator, ledger = self.require_resources()
        ready = self._ready(
            messages,
            tools=tools,
            tool_choice=tool_choice,
            max_tokens=max_tokens,
            temperature=temperature,
            top_p=top_p,
            reasoning_effort=reasoning_effort,
            deadline=deadline,
            request_timeout_s=request_timeout_s,
            before_dispatch=before_dispatch,
            on_dispatched=on_dispatched,
        )
        require_inference_target(ready["url"])
        attempt = _Attempt(coordinator, ledger, self._incarnation, ready)
        try:
            await self._admit(attempt)
            self._reserve(attempt)
            await self._dispatch(attempt)
            return self._finish(attempt, *await self._exchange(http_client, attempt))
        except BaseException as exc:
            attempt.cancelled = isinstance(exc, asyncio.CancelledError)
            self._cleanup(attempt)
            _publish_progress(
                attempt,
                (
                    "failed"
                    if attempt.settled
                    else (
                        "cancelled"
                        if attempt.cancelled and not attempt.transport_started
                        else (
                            "completion_unknown"
                            if attempt.transport_started
                            else "failed"
                        )
                    )
                ),
            )
            raise

    def _ready(self, messages: Any, **kwargs: Any) -> dict[str, Any]:
        role = self._resolved.roles[self._binding["role"]]
        document = self._resolved.document
        endpoint = document.endpoints[role.endpoint_id]
        policy = document.deployments[role.deployment_id].protocol
        deadline = _real(kwargs["deadline"], "deadline", positive=False)
        request_timeout_s = _real(
            kwargs["request_timeout_s"], "request_timeout_s", positive=True
        )
        if deadline is not None and time.monotonic() >= deadline:
            raise LocalInferenceError("deadline_exceeded")
        _callbacks(kwargs["before_dispatch"], kwargs["on_dispatched"])
        output = _output_limit(role, kwargs["max_tokens"])
        wired_tools = _wire_tools(role, kwargs["tools"], kwargs["tool_choice"])
        temperature = _axis(
            role.sampling.temperature, kwargs["temperature"], "temperature"
        )
        top_p = _axis(role.sampling.top_p, kwargs["top_p"], "top_p")
        effort = _effort(role, kwargs["reasoning_effort"])
        reasoning_body = reasoning_request_body(policy, role.reasoning_mode, effort)
        chat = build_chat_request(
            dialect=role.dialect,
            model=role.model,
            messages=messages,
            context_tokens=role.context_tokens,
            max_output_tokens=output,
            tools=wired_tools,
            tool_choice=kwargs["tool_choice"] if wired_tools is not None else None,
            temperature=temperature,
            top_p=top_p,
            sampling_supported=not _sampling_disabled(role),
            reasoning_mode=role.reasoning_mode,
            reasoning_body=reasoning_body or None,
            reasoning_control_evidence="configured" if reasoning_body else None,
            history_replay_fields=policy.history_replay_fields,
            require_history_replay=policy.require_history_replay,
            template_overhead_tokens=policy.template_overhead_tokens,
            output_includes_reasoning=_reasoning_output(role),
            stream=policy.streaming.enabled,
            usage_request_supported=policy.streaming.usage_request == "include_usage",
            max_argument_depth=policy.limits.max_argument_depth,
            max_tool_calls=policy.limits.max_tool_calls,
        )
        plain = chat.as_dict()["payload"]
        body = json.dumps(
            plain, ensure_ascii=False, separators=(",", ":"), allow_nan=False
        ).encode("utf-8")
        frozen = freeze_request(
            self._resolved,
            self._binding["role"],
            requested_output_tokens=output,
            reserved_prompt_tokens=chat.token_evidence["estimated_tokens"],
        )
        schemas = list(plain["tools"]) if "tools" in plain else []
        names = tuple(item["function"]["name"] for item in schemas)
        choice = plain.get("tool_choice", "auto")
        # Keep an immutable contract from the validated wire request, independent
        # of caller-owned tool dictionaries that may change while queued.
        tool_choice = (
            ("named", choice["function"]["name"])
            if isinstance(choice, dict)
            else (choice, None)
        )
        token = _bearer(endpoint.auth)
        headers = {"Content-Type": "application/json"}
        if token is not None:
            headers["Authorization"] = "Bearer " + token
        base = (
            endpoint.base_url[:-1]
            if endpoint.base_url.endswith("/")
            else endpoint.base_url
        )
        return {
            "frozen": frozen,
            "owner": "run_" + self._binding["budget_id"],
            "group": role.capacity_group,
            "endpoint_id": role.endpoint_id,
            "url": base + "/chat/completions",
            "headers": headers,
            "body": body,
            "fingerprint": hashlib.sha256(body).hexdigest(),
            "pseudo": _pseudo(role),
            "stream": policy.streaming.enabled,
            "max_bytes": policy.limits.max_response_bytes,
            "max_events": policy.limits.max_stream_events,
            "require_done": policy.streaming.require_done,
            "max_calls": policy.limits.max_tool_calls,
            "deadline": deadline,
            "request_timeout_s": request_timeout_s,
            "before_dispatch": kwargs["before_dispatch"],
            "on_dispatched": kwargs["on_dispatched"],
            "history_fields": policy.history_replay_fields,
            "require_history": policy.require_history_replay,
            "tool_choice": tool_choice,
            "seal": {
                "expected_model": frozen.model,
                "allowed_tool_names": names,
                "allowed_model_aliases": policy.model_aliases,
                "allowed_tool_schemas": schemas,
                "argument_encoding": policy.argument_encoding,
                "max_arguments_bytes": policy.limits.max_arguments_bytes,
                "max_argument_depth": policy.limits.max_argument_depth,
                "max_tool_calls": policy.limits.max_tool_calls,
            },
        }

    async def _admit(self, attempt: "_Attempt") -> None:
        attempt.coordinator.acquire(
            group=attempt.group,
            endpoint_id=attempt.endpoint_id,
            dispatch_id=attempt.dispatch_id,
            owner_run=attempt.owner,
            attempt_id=attempt.attempt_id,
            process_incarnation=attempt.incarnation,
            request_fingerprint=attempt.fingerprint,
            now_s=_now(),
        )
        attempt.acquired = True
        _publish_progress(attempt, "queued")
        while True:
            attempt.coordinator.expire_due(_now())
            permit = attempt.coordinator.get_permit(attempt.dispatch_id)
            if permit["state"] == "admitted":
                self._remember_deadline(attempt)
                _past_deadline(attempt.deadline)
                return
            if permit["state"] != "queued":
                code = (
                    "deadline_exceeded"
                    if permit["state"] == "expired_before_dispatch"
                    else "queue_timeout"
                )
                raise LocalInferenceError(code)
            _past_deadline(attempt.deadline)
            _publish_progress(attempt, "queued")
            await asyncio.sleep(_POLL_S)

    def _remember_deadline(self, attempt: "_Attempt") -> None:
        if attempt.admit_deadline_s is not None:
            return
        live = attempt.coordinator.inspect(attempt.group)["request_timeout_s"]
        if type(live) is not int or isinstance(live, bool) or live < 1:
            raise LocalInferenceError("invalid_field", "request_timeout_s")
        permits = attempt.coordinator.snapshot()["groups"][attempt.group][
            "permits"
        ].values()
        permit = next(
            item for item in permits if item["dispatch_id"] == attempt.dispatch_id
        )
        remaining = permit["request_deadline_s"] - time.time()
        admitted_at = time.monotonic()
        attempt.admit_deadline_s = admitted_at + remaining
        if attempt.request_timeout_s is not None:
            attempt.request_deadline_s = admitted_at + attempt.request_timeout_s

    def _reserve(self, attempt: "_Attempt") -> None:
        self._arm_timeout(attempt)
        requested_ms = max(1, math.ceil(attempt.timeout_s * 1000))
        permit = attempt.coordinator.get_permit(attempt.dispatch_id)
        view = reserve_budget_for_admitted_permit(
            attempt.ledger,
            permit,
            attempt.frozen,
            owner=attempt.owner,
            requested_wall_ms=requested_ms,
            expected_capacity_group=attempt.group,
        )
        attempt.reserved = True
        attempt.granted_ms = view["granted_wall_ms"]
        self._arm_timeout(attempt)

    async def _dispatch(self, attempt: "_Attempt") -> None:
        callback_timed_out = False
        try:
            await asyncio.wait_for(
                _await_callback(attempt.before_dispatch), attempt.timeout_s
            )
        except TimeoutError:
            callback_timed_out = True
        if callback_timed_out:
            raise LocalInferenceError("deadline_exceeded")
        self._ensure_admitted(attempt)
        self._arm_timeout(attempt)
        attempt.ledger.mark_dispatched(attempt.dispatch_id, owner=attempt.owner)
        attempt.budget_marked = True
        attempt.coordinator.mark_dispatched(
            attempt.dispatch_id,
            owner_run=attempt.owner,
            request_fingerprint=attempt.fingerprint,
            now_s=_now(),
        )
        attempt.dispatched = True
        _sync_callback(attempt.on_dispatched)
        self._arm_timeout(attempt)
        attempt.started = time.monotonic()

    def _ensure_admitted(self, attempt: "_Attempt") -> None:
        attempt.coordinator.expire_due(_now())
        permit = attempt.coordinator.get_permit(attempt.dispatch_id)
        if permit["state"] == "admitted":
            return
        code = (
            "deadline_exceeded"
            if permit["state"] == "expired_before_dispatch"
            else "queue_timeout"
        )
        raise LocalInferenceError(code)

    def _arm_timeout(self, attempt: "_Attempt") -> None:
        now = time.monotonic()
        limits: list[float] = []
        if attempt.granted_ms is not None:
            limits.append(attempt.granted_ms / 1000.0)
        if attempt.admit_deadline_s is not None:
            limits.append(attempt.admit_deadline_s - now)
        live = attempt.coordinator.inspect(attempt.group)["request_timeout_s"]
        if type(live) is int and not isinstance(live, bool) and live > 0:
            limits.append(float(live))
        if attempt.request_deadline_s is not None:
            limits.append(attempt.request_deadline_s - now)
        if attempt.deadline is not None:
            limits.append(attempt.deadline - now)
        timeout = min(limits) if limits else 0.0
        if timeout <= 0:
            raise LocalInferenceError("deadline_exceeded")
        attempt.timeout_s = timeout

    async def _exchange(self, http_client: Any, attempt: "_Attempt") -> tuple[int, Any]:
        require_inference_target(attempt.url)
        outbound = httpx.Request(
            "POST", attempt.url, headers=attempt.headers, content=attempt.body
        )
        outbound.extensions["timeout"] = httpx.Timeout(attempt.timeout_s).as_dict()

        async def run() -> tuple[int, Any]:
            attempt.transport_started = True
            _publish_progress(attempt, "generating")
            response = await http_client.send(
                outbound, stream=True, auth=None, follow_redirects=False
            )
            try:
                if response.status_code != 200:
                    return response.status_code, None
                if attempt.stream:
                    _reject_length(response, attempt.max_bytes)
                    assembler = SSEAssembler(
                        max_bytes=attempt.max_bytes,
                        max_events=attempt.max_events,
                        require_done=attempt.require_done,
                        max_tool_calls=attempt.max_calls,
                        defer_semantic_errors=True,
                    )
                    async for chunk in response.aiter_bytes():
                        assembler.feed(chunk)
                    try:
                        payload = assembler.finish()
                    except LocalProtocolError:
                        if assembler.completion_observed:
                            self._settle(attempt)
                        raise
                    return 200, payload
                return 200, await _read_capped(response, attempt.max_bytes)
            finally:
                await response.aclose()

        failure = None
        try:
            return await asyncio.wait_for(run(), attempt.timeout_s)
        except (TimeoutError, httpx.TimeoutException):
            failure = LocalInferenceError("deadline_exceeded")
        except (httpx.HTTPError, OSError):
            failure = LocalInferenceError("completion_unknown")
        # Do not retain raw HTTP exceptions containing URLs/body/header data.
        raise failure from None

    def _finish(self, attempt: "_Attempt", status: int, payload: Any) -> httpx.Response:
        if status == 429 or 300 <= status < 500:
            self._settle(attempt)
            raise LocalInferenceError(
                "rate_limited" if status == 429 else "request_rejected"
            )
        if status != 200 or payload is None:
            raise LocalInferenceError("completion_unknown")
        _publish_progress(attempt, "validating")
        if type(payload) is bytes:
            invalid_utf8 = False
            try:
                payload = payload.decode("utf-8")
            except UnicodeError:
                invalid_utf8 = True
            if invalid_utf8:
                raise LocalProtocolError("invalid_response", "response is not UTF-8")
        if type(payload) is str:
            payload = loads_strict(payload, code="invalid_response")
        # A terminal envelope establishes completion independently of whether
        # its mathematics, tool arguments, refusal, or truncation is acceptable.
        if _terminal_completion(payload):
            self._settle(attempt)
        sealed = seal_chat_response(payload, **attempt.seal)
        _validate_tool_choice(sealed, attempt.tool_choice)
        history = _history(sealed, attempt.history_fields, attempt.require_history)
        if not attempt.settled:
            self._settle(attempt)
        _publish_progress(attempt, "finished")
        return _normalized(sealed, history, attempt.pseudo)

    def _settle(self, attempt: "_Attempt") -> None:
        millis = _elapsed_ms(attempt.started)
        attempt.coordinator.complete(
            attempt.dispatch_id,
            owner_run=attempt.owner,
            request_fingerprint=attempt.fingerprint,
            now_s=_now(),
        )
        attempt.ledger.settle_observed_wall(
            attempt.dispatch_id,
            owner=attempt.owner,
            milliseconds=millis,
            receipt=attempt.receipt,
            completion_known=True,
        )
        attempt.settled = True

    def _cleanup(self, attempt: "_Attempt") -> None:
        if attempt.settled or not attempt.acquired:
            return
        now = _now()
        if not attempt.transport_started:
            self._release_before_send(attempt, now)
            return
        permit = attempt.coordinator.get_permit(attempt.dispatch_id)
        view = attempt.ledger.reservation(attempt.dispatch_id)
        millis = _elapsed_ms(attempt.started)
        if permit["state"] == "completed":
            if view["state"] == "dispatched":
                attempt.ledger.settle_observed_wall(
                    attempt.dispatch_id,
                    owner=attempt.owner,
                    milliseconds=millis,
                    receipt=attempt.receipt,
                    completion_known=True,
                )
            return
        if view["state"] == "dispatched":
            attempt.ledger.observe_wall(
                attempt.dispatch_id,
                owner=attempt.owner,
                milliseconds=millis,
                receipt=attempt.receipt,
            )
            attempt.ledger.mark_unknown(attempt.dispatch_id, owner=attempt.owner)
        elif view["state"] == "unknown":
            attempt.ledger.observe_wall(
                attempt.dispatch_id,
                owner=attempt.owner,
                milliseconds=millis,
                receipt=attempt.receipt,
            )
        if permit["state"] == "dispatched":
            if attempt.cancelled:
                attempt.coordinator.cancel(
                    attempt.dispatch_id, owner_run=attempt.owner, now_s=now
                )
            else:
                attempt.coordinator.note_heartbeat_expired(
                    attempt.dispatch_id,
                    owner_run=attempt.owner,
                    now_s=now,
                )
        elif attempt.cancelled and permit["state"] == "completion_unknown":
            attempt.coordinator.cancel(
                attempt.dispatch_id, owner_run=attempt.owner, now_s=now
            )
        elif not attempt.cancelled and permit["state"] == "cancel_requested":
            attempt.coordinator.note_heartbeat_expired(
                attempt.dispatch_id,
                owner_run=attempt.owner,
                now_s=now,
            )

    def _release_before_send(self, attempt: "_Attempt", now: int) -> None:
        if attempt.budget_marked:
            permit = attempt.coordinator.get_permit(attempt.dispatch_id)
            if permit["state"] in {"queued", "admitted"}:
                attempt.coordinator.cancel(
                    attempt.dispatch_id, owner_run=attempt.owner, now_s=now
                )
            elif permit["state"] in {
                "dispatched",
                "cancel_requested",
                "completion_unknown",
            }:
                attempt.coordinator.complete(
                    attempt.dispatch_id,
                    owner_run=attempt.owner,
                    request_fingerprint=attempt.fingerprint,
                    now_s=now,
                )
            # No HTTP send began. Close the conservative dispatch grant without
            # refunding tokens/dispatches or leaving an unresolvable reservation.
            attempt.ledger.settle_observed_wall(
                attempt.dispatch_id,
                owner=attempt.owner,
                milliseconds=0,
                receipt=attempt.receipt,
                completion_known=True,
            )
            attempt.settled = True
            return
        if attempt.reserved:
            release_if_not_dispatched(
                capacity=attempt.coordinator,
                budget=attempt.ledger,
                dispatch_id=attempt.dispatch_id,
                now_s=now,
            )
            return
        permit = attempt.coordinator.get_permit(attempt.dispatch_id)
        if permit["state"] in {"queued", "admitted"}:
            attempt.coordinator.cancel(
                attempt.dispatch_id, owner_run=attempt.owner, now_s=now
            )


def _validate_tool_choice(sealed: SealedChat, choice: tuple[str, str | None]) -> None:
    """Enforce request selection on the entire validated batch before exposure."""
    mode, name = choice
    calls = sealed.tool_calls
    violates = (
        (mode == "none" and bool(calls))
        or (mode == "required" and not calls)
        or (
            mode == "named"
            and (not calls or any(call["name"] != name for call in calls))
        )
    )
    if violates:
        raise LocalProtocolError(
            "malformed_tool_batch",
            "response does not satisfy the requested tool choice",
        )


class _Attempt:
    def __init__(
        self, coordinator, ledger, incarnation: str, ready: dict[str, Any]
    ) -> None:
        self.coordinator = coordinator
        self.ledger = ledger
        self.incarnation = incarnation
        self.dispatch_id = "d" + secrets.token_hex(8)
        self.attempt_id = "a" + secrets.token_hex(8)
        self.receipt = "w-" + self.dispatch_id
        self.frozen = ready["frozen"]
        self.owner = ready["owner"]
        self.group = ready["group"]
        self.endpoint_id = ready["endpoint_id"]
        self.url = ready["url"]
        self.headers = ready["headers"]
        self.body = ready["body"]
        self.fingerprint = ready["fingerprint"]
        self.pseudo = ready["pseudo"]
        self.stream = ready["stream"]
        self.max_bytes = ready["max_bytes"]
        self.max_events = ready["max_events"]
        self.require_done = ready["require_done"]
        self.max_calls = ready["max_calls"]
        self.deadline = ready["deadline"]
        self.request_timeout_s = ready["request_timeout_s"]
        self.before_dispatch = ready["before_dispatch"]
        self.on_dispatched = ready["on_dispatched"]
        self.history_fields = ready["history_fields"]
        self.require_history = ready["require_history"]
        self.seal = ready["seal"]
        self.tool_choice = ready["tool_choice"]
        self.acquired = False
        self.reserved = False
        self.budget_marked = False
        self.dispatched = False
        self.transport_started = False
        self.progress_started = time.monotonic()
        self.progress_status = ""
        self.progress_at = 0.0
        self.settled = False
        self.cancelled = False
        self.started: float | None = None
        self.granted_ms: int | None = None
        self.admit_deadline_s: float | None = None
        self.request_deadline_s: float | None = None
        self.timeout_s = 0.0


def _terminal_completion(payload: Any) -> bool:
    if type(payload) is not dict:
        return False
    choices = payload.get("choices")
    if type(choices) is not list or len(choices) != 1 or type(choices[0]) is not dict:
        return False
    choice = choices[0]
    finish = choice.get("finish_reason")
    index = choice.get("index", 0)
    return (
        type(index) is int
        and index == 0
        and type(finish) is str
        and finish
        in {
            "stop",
            "tool_calls",
            "length",
            "content_filter",
            "function_call",
        }
    )


def _publish_progress(attempt: _Attempt, status: str) -> None:
    now = time.monotonic()
    if attempt.progress_status == status and now - attempt.progress_at < 1:
        return
    attempt.progress_status, attempt.progress_at = status, now
    try:
        from ..llm_usage import publish_provider_request_metadata
        from ..provider_progress import PROGRESS_KEY, progress_snapshot

        report = attempt.coordinator.inspect(attempt.group)
        queue = report["queue"]
        observation = progress_snapshot(
            {
                "backend": "local_inference",
                "status": status,
                "elapsed_s": now - attempt.progress_started,
                "queue_position": (
                    queue.index(attempt.dispatch_id) + 1
                    if attempt.dispatch_id in queue
                    else 0
                ),
                "queued_requests": report["occupancy"]["queued"],
                "inflight_requests": report["occupancy"]["group_inflight"],
                "unknown_requests": len(report["completion_unknown_dispatch_ids"]),
            }
        )
        if observation is not None:
            publish_provider_request_metadata({PROGRESS_KEY: observation})
    except Exception:
        # Observability is advisory; it cannot change admission or settlement.
        return


def _load_binding(binding: dict[str, Any]):
    if type(binding) is not dict:
        raise LocalInferenceError("invalid_field", "binding")
    cloned = None
    try:
        cloned = json.loads(json.dumps(binding, allow_nan=False))
    except (TypeError, ValueError, RecursionError):
        pass
    if cloned is None:
        raise LocalInferenceError("invalid_field", "binding")
    keys = set(cloned)
    if keys not in (
        set(BINDING_KEYS),
        set(BINDING_KEYS) | {"coordinator_id"},
        _PREPARED,
    ):
        raise LocalInferenceError("invalid_field", "binding")
    if type(cloned.get("snapshot")) is not dict:
        raise LocalInferenceError("invalid_field", "snapshot")
    resolved = load_private_worker_snapshot(cloned["snapshot"])
    if type(cloned.get("role")) is not str or cloned["role"] not in resolved.roles:
        raise LocalInferenceError("unknown_role")
    if not _is_hex(cloned.get("budget_id"), 32):
        raise LocalInferenceError("invalid_field", "budget_id")
    for field in ("coordinator_root", "budget_root"):
        value = cloned.get(field)
        if type(value) is not str or value.strip() == "" or "\x00" in value:
            raise LocalInferenceError("invalid_field", field)
    if "coordinator_id" in cloned and not _is_hex(cloned["coordinator_id"], 64):
        raise LocalInferenceError("coordinator_unavailable")
    if "resource_marker" in cloned:
        _expect_marker(
            cloned["resource_marker"],
            resolved,
            cloned["budget_id"],
            cloned.get("coordinator_id"),
        )
    return cloned, resolved


def _limits(resolved):
    identity = resolved.document.coordinator
    limits = resolved.document.run_budget
    if identity is None or limits is None:
        raise LocalInferenceError("coordinator_required")
    return identity, limits


def _expect_marker(marker, resolved, budget_id: str, coordinator_id) -> None:
    identity, limits = _limits(resolved)
    if type(marker) is not dict or set(marker) != _MARKER_FIELDS:
        raise LocalInferenceError("corrupt_coordinator")
    if (
        type(marker.get("schema_version")) is not int
        or marker.get("schema_version") != 1
    ):
        raise LocalInferenceError("corrupt_coordinator")
    if (
        marker.get("installation_id") != identity.installation_id
        or marker.get("scope_id") != identity.scope_id
    ):
        raise LocalInferenceError("coordinator_scope_conflict")
    initial = marker.get("initial_ceilings")
    cap = _profile_ceilings(limits)
    if (
        type(initial) is not dict
        or set(initial) != set(cap)
        or any(
            type(value) is not int or not 1 <= value <= cap[key]
            for key, value in initial.items()
        )
    ):
        raise LocalInferenceError("corrupt_coordinator")
    if (
        marker.get("budget_id") != budget_id
        or marker.get("profile_hash") != resolved.profile_hash
    ):
        raise LocalInferenceError("ledger_identity_mismatch")
    if (
        not _is_hex(marker.get("coordinator_id"), 64)
        or marker.get("coordinator_id") != coordinator_id
    ):
        raise LocalInferenceError("coordinator_unavailable")


def _resume(
    cloned, resolved, root: Path, budget_root: Path, marker_path: Path
) -> dict[str, Any]:
    marker = read_json_object(
        marker_path, max_bytes=_MARKER_BYTES, corrupt_code="corrupt_coordinator"
    )
    _expect_marker(marker, resolved, cloned["budget_id"], marker.get("coordinator_id"))
    if (
        "coordinator_id" in cloned
        and cloned["coordinator_id"] != marker["coordinator_id"]
    ):
        raise LocalInferenceError("coordinator_unavailable")
    if "resource_marker" in cloned and cloned["resource_marker"] != marker:
        raise LocalInferenceError("coordinator_unavailable")
    identity, _ignored = _limits(resolved)
    coordinator = CapacityCoordinator.open(
        root,
        installation_id=identity.installation_id,
        scope_id=identity.scope_id,
    )
    if coordinator.coordinator_id() != marker["coordinator_id"]:
        raise LocalInferenceError("coordinator_unavailable")
    ledger = LocalComputeLedger.open(budget_root)
    ledger.require_resume_identity(
        ledger_id=cloned["budget_id"], profile_hash=resolved.profile_hash
    )
    _check_ledger_grant(ledger, marker["initial_ceilings"])
    return _attach(cloned, marker)


def _install(
    cloned, resolved, root: Path, budget_root: Path, identity, ceilings
) -> dict[str, Any]:
    open_coordinator = (
        CapacityCoordinator.open
        if "coordinator_id" in cloned
        else CapacityCoordinator.initialize
    )
    coordinator = open_coordinator(
        root,
        installation_id=identity.installation_id,
        scope_id=identity.scope_id,
    )
    if (
        "coordinator_id" in cloned
        and cloned["coordinator_id"] != coordinator.coordinator_id()
    ):
        raise LocalInferenceError("coordinator_unavailable")
    try:
        ledger = LocalComputeLedger.create(
            budget_root,
            ledger_id=cloned["budget_id"],
            profile_hash=resolved.profile_hash,
            max_dispatches=ceilings["dispatches"],
            max_requested_output_tokens=ceilings["requested_output_tokens"],
            max_observed_request_wall_s=ceilings["observed_request_wall_ms"] // 1000,
        )
    except LocalInferenceError as exc:
        if exc.code != "budget_exists":
            raise
        ledger = LocalComputeLedger.open(budget_root)
    ledger.require_resume_identity(
        ledger_id=cloned["budget_id"], profile_hash=resolved.profile_hash
    )
    _check_ledger_grant(ledger, ceilings)
    register_profile(coordinator, resolved.document)
    marker = {
        "schema_version": 1,
        "installation_id": identity.installation_id,
        "scope_id": identity.scope_id,
        "coordinator_id": coordinator.coordinator_id(),
        "budget_id": cloned["budget_id"],
        "profile_hash": resolved.profile_hash,
        "initial_ceilings": dict(ceilings),
    }
    return _attach(cloned, _publish_marker(budget_root, marker))


def _publish_marker(directory: Path, marker: dict[str, Any]) -> dict[str, Any]:
    path = directory / _MARKER
    with durable_mutation(directory):
        if path.is_symlink():
            raise LocalInferenceError("symlink_forbidden")
        if path.is_file():
            current = read_json_object(
                path, max_bytes=_MARKER_BYTES, corrupt_code="corrupt_coordinator"
            )
            if current != marker:
                raise LocalInferenceError("coordinator_unavailable")
            return current
        atomic_write_json(path, marker, max_bytes=_MARKER_BYTES)
    return marker


def _attach(binding: dict[str, Any], marker: dict[str, Any]) -> dict[str, Any]:
    fresh = {key: binding[key] for key in BINDING_KEYS}
    fresh["snapshot"] = json.loads(json.dumps(binding["snapshot"]))
    fresh["coordinator_id"] = marker["coordinator_id"]
    fresh["resource_marker"] = json.loads(json.dumps(marker))
    return fresh


def _path(value: str) -> Path:
    path = Path(value)
    _reject_symlink(path)
    return path


def _reject_symlink(path: Path) -> None:
    try:
        linked = path.is_symlink()
    except OSError:
        raise LocalInferenceError("symlink_forbidden") from None
    if linked:
        raise LocalInferenceError("symlink_forbidden")


def _is_hex(value: Any, size: int) -> bool:
    return (
        type(value) is str
        and len(value) == size
        and all(ch in "0123456789abcdef" for ch in value)
    )


def _pseudo(role) -> str:
    if role.billing_kind == "owned_compute":
        kind = "owned-compute"
    elif role.billing_kind == "metered":
        kind = "metered"
    else:
        raise LocalInferenceError("invalid_field", "billing")
    return f"local://{kind}/{role.deployment_fingerprint}"


def _bearer(auth) -> str | None:
    if auth.kind != "env":
        return None
    require_auth_available(auth, os.environ)
    token = os.environ[auth.name]
    if type(token) is not str or any(ord(ch) < 33 or ord(ch) == 127 for ch in token):
        raise LocalInferenceError("credential_unavailable")
    return token


def _output_limit(role, max_tokens) -> int:
    if max_tokens is None:
        return role.max_output_tokens
    if type(max_tokens) is not int:
        raise LocalInferenceError("invalid_field", "max_tokens")
    if max_tokens < 1 or max_tokens > role.max_output_tokens:
        raise LocalInferenceError("output_allowance_exceeded")
    return max_tokens


def _wire_tools(role, tools, tool_choice):
    if role.tools == "native_required":
        # Capability admission does not force every turn to offer tools. Final
        # text, answer discovery, and formalization may deliberately omit them.
        if tools is None or (type(tools) in (list, tuple) and not tools):
            if tool_choice is not None and tool_choice != "none":
                raise LocalInferenceError("invalid_field", "tool_choice")
            return None
        if type(tools) not in (list, tuple):
            raise LocalInferenceError("invalid_field", "tools")
        return list(tools)
    if role.tools in {"text_only", "disabled"}:
        if tools is not None or tool_choice is not None:
            raise LocalInferenceError("invalid_field", "tools")
        return None
    raise LocalInferenceError("invalid_field", "tools")


def _axis(axis, supplied, field: str):
    if axis.policy == "forbidden":
        if supplied is not None:
            raise LocalInferenceError("invalid_field", field)
        return None
    if axis.policy == "fixed":
        number = _configured_number(axis.value)
        if supplied is not None and not _same_number(supplied, number):
            raise LocalInferenceError("invalid_field", field)
        return number
    if supplied is None:
        return None
    if not _same_number(supplied, supplied):
        raise LocalInferenceError("invalid_field", field)
    return supplied


def _configured_number(value):
    if type(value) is str and "." not in value and value.isdigit():
        return int(value)
    if type(value) is not str or "." not in value:
        raise LocalInferenceError("invalid_field", "sampling")
    number = json.loads(value)
    if type(number) is bool or type(number) not in (int, float):
        raise LocalInferenceError("invalid_field", "sampling")
    return number


def _same_number(supplied, configured) -> bool:
    if (
        type(supplied) is bool
        or type(supplied) not in (int, float)
        or not math.isfinite(supplied)
    ):
        return False
    return supplied == configured


def _sampling_disabled(role) -> bool:
    return (
        role.sampling.temperature.policy == "forbidden"
        and role.sampling.top_p.policy == "forbidden"
    )


def _effort(role, requested):
    if requested is not None and requested != role.reasoning_effort:
        raise LocalInferenceError("reasoning_conflict")
    return role.reasoning_effort


def _reasoning_output(role):
    if role.output_limit_includes_reasoning == "true":
        return True
    if role.output_limit_includes_reasoning == "false":
        return False
    if role.output_limit_includes_reasoning == "unknown":
        return None
    raise LocalInferenceError("invalid_field", "output_limit_includes_reasoning")


def _real(value, field: str, *, positive: bool):
    if value is None:
        return None
    converted = None
    if type(value) in (int, float):
        try:
            converted = float(value)
        except OverflowError:
            pass
    if converted is None or not math.isfinite(converted):
        raise LocalInferenceError("invalid_field", field)
    if positive and converted <= 0:
        raise LocalInferenceError("invalid_field", field)
    return converted


def _past_deadline(deadline) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise LocalInferenceError("deadline_exceeded")


def _callbacks(before_dispatch, on_dispatched) -> None:
    if before_dispatch is not None and not callable(before_dispatch):
        raise LocalInferenceError("invalid_field", "before_dispatch")
    if on_dispatched is not None and not callable(on_dispatched):
        raise LocalInferenceError("invalid_field", "on_dispatched")


async def _await_callback(callback) -> None:
    if callback is None:
        return
    result = callback()
    if not inspect.isawaitable(result):
        raise LocalInferenceError("invalid_field", "before_dispatch")
    await result


def _sync_callback(callback) -> None:
    if callback is None:
        return
    result = callback()
    if inspect.isawaitable(result):
        if inspect.iscoroutine(result):
            result.close()
        raise LocalInferenceError("invalid_field", "on_dispatched")


def _history(sealed, fields, required: bool) -> dict[str, str]:
    found = {}
    for key in fields:
        if key not in sealed.reasoning_fields:
            if required:
                raise LocalProtocolError(
                    "history_replay_required", "declared history field is absent"
                )
            continue
        value = sealed.reasoning_fields[key]
        if type(value) is not str:
            raise LocalProtocolError(
                "invalid_response", "reasoning field is not a string"
            )
        found[key] = value
    return found


def _normalized(sealed, history: dict[str, str], pseudo: str) -> httpx.Response:
    message = {"role": "assistant", "content": sealed.text, **history}
    if sealed.tool_calls:
        message["tool_calls"] = [
            {
                "id": call["id"],
                "type": "function",
                "function": {"name": call["name"], "arguments": call["arguments_json"]},
            }
            for call in sealed.tool_calls
        ]
    body = {
        "model": sealed.model,
        "choices": [
            {
                "index": 0,
                "message": message,
                "finish_reason": sealed.finish_reason,
            }
        ],
    }
    if sealed.usage:
        usage = {key: sealed.usage[key] for key in _USAGE if key in sealed.usage}
        if usage:
            body["usage"] = usage
    encoded = json.dumps(body, ensure_ascii=False).encode("utf-8")
    return httpx.Response(
        200,
        headers={"content-type": "application/json"},
        content=encoded,
        request=httpx.Request("POST", pseudo),
        extensions={
            "local_sealed_chat": sealed,
            "local_history_fields": dict(history),
        },
    )


async def _read_capped(response: httpx.Response, limit: int) -> bytes:
    _reject_length(response, limit)
    chunks, total = [], 0
    async for chunk in response.aiter_bytes():
        total += len(chunk)
        if total > limit:
            raise LocalProtocolError(
                "stream_overflow", "response exceeds the byte limit"
            )
        chunks.append(chunk)
    return b"".join(chunks)


def _reject_length(response: httpx.Response, limit: int) -> None:
    header = response.headers.get("content-length")
    if header is not None and (
        len(header) > 12 or (header.isdigit() and int(header) > limit)
    ):
        raise LocalProtocolError("stream_overflow", "response exceeds the byte limit")


def _elapsed_ms(started) -> int:
    if started is None:
        return 0
    return max(0, int((time.monotonic() - started) * 1000))


def _now() -> int:
    return int(time.time())
