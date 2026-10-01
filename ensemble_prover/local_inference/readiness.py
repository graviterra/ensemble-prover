"""Operator readiness, resource recovery, and bounded conformance checks.

``project_readiness`` reads a resolved profile and an optional saved receipt.
It does not contact an endpoint, create a coordinator, or create a budget.
``run_conformance_probe`` is the explicit check. It spends a new finite setup
ledger through ``prepare_resources`` and ``LocalRuntime.request``. A passing
receipt expires and does not establish later behavior. Context limits, reasoning
controls, and output limits stay unknown unless separately observed. Mini tools
are not executed.

The setup record uses a fresh ``budget_id``. ``prepare_resources`` creates the
ledger at explicit probe ceiling keywords and the snapshot profile hash, never
at a larger profile run budget. Existing coordinator identity is preserved.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from .budget import LocalComputeLedger
from .capacity import CapacityCoordinator
from .config import ResolvedLocalRun, load_private_worker_snapshot, public_manifest
from .errors import LocalInferenceError
from .protocol import LocalProtocolError, SealedChat, build_chat_request
from .protocol_config import reasoning_request_body
from .strictload import canonical_json, content_hash

_STATEMENT = "This check records one bounded exchange. It expires and does not establish later behavior."
_KIND = "local_conformance_receipt"
_PASS = "bounded_pass"
_FUTURE = "not_established"
_ADMISSION = "bounded_evidence_only"
_TOOL = "check_lean"
_PROBE_CODE = "conformance-probe-\u03b1"
_USER = (
    "Protocol conformance check. This is not a mathematics task. "
    f"Call the {_TOOL} tool exactly once. Set code to the exact token {_PROBE_CODE}. "
    "Do not call another tool."
)
_TOOL_RESULT = "conformance-probe: call observed; tool was not executed"
_EXPECTED = {"code": _PROBE_CODE}
_REASONS = {
    "retain_unknown": "retain_unknown",
    "completion_evidence_lost": "release_capacity_unresolved",
}
_RESULTS = frozenset(
    {"bounded_pass", "predispatch_rejected", "incompatible", "incomplete"}
)
_UNKNOWN = (
    "context_limit_enforcement",
    "reasoning_control_enforcement",
    "output_limit_honored",
    "stream_completion",
)
_HEX32 = re.compile(r"^[0-9a-f]{32}$")
_HEX64 = re.compile(r"^[0-9a-f]{64}$")
_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]{0,63}$")
_SAFE_CODE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_MAX_TIME = 10**12
_DAY = 24 * 60 * 60


def conformance_tools() -> list[dict[str, Any]]:
    """Return detached Mini tool schemas a native prover can send."""

    from ensemble_prover.certify_counterexample_tool import CERTIFY_COUNTEREXAMPLE_TOOL
    from ensemble_prover.lean_compute_tool import COMPUTE_EXAMPLES_TOOL
    from ensemble_prover.mini_prover import (
        CHECK_LEAN_TOOL,
        SEARCH_MATHLIB_TOOL,
        SEARCH_THEOREMS_TOOL,
    )
    from ensemble_prover.mini_research import NATIVE_TOOLS
    from ensemble_prover.proof_tools import APPLY_DECL_TO_ACTIVE_GOAL_TOOL
    from ensemble_prover.skeleton_tool import TRY_SKELETON_TOOL
    from ensemble_prover.try_lean_tool import TRY_LEAN_TOOL

    loaded = json.loads(
        canonical_json(
            [
                SEARCH_MATHLIB_TOOL,
                SEARCH_THEOREMS_TOOL,
                CHECK_LEAN_TOOL,
                TRY_LEAN_TOOL,
                CERTIFY_COUNTEREXAMPLE_TOOL,
                COMPUTE_EXAMPLES_TOOL,
                TRY_SKELETON_TOOL,
                APPLY_DECL_TO_ACTIVE_GOAL_TOOL,
                *NATIVE_TOOLS,
            ]
        )
    )
    names = [item["function"]["name"] for item in loaded]
    if _TOOL not in names or len(names) != len(set(names)):
        raise LocalInferenceError("invalid_field", "tools")
    return loaded


def project_readiness(
    resolved: ResolvedLocalRun, *, now_s: int, receipt: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Project saved facts. A catalog refresh does not call a model or create a ledger."""

    now = _int(now_s, 0, _MAX_TIME - 1, "now_s")
    body = public_manifest(resolved)
    body["network"] = "not_contacted"
    body["readiness"] = {
        name: _role_view(resolved, name, now, _accepted(receipt, resolved, name, now))
        for name in resolved.roles
    }
    return _public(body, _forbidden(resolved))


def inspect_resources(
    *,
    coordinator_root: str | Path,
    installation_id: str,
    scope_id: str,
    group: str,
    budget_root: str | Path | None = None,
) -> dict[str, Any]:
    """Count queued and unknown reservations without paths, endpoint URLs, or auth names."""

    root = _path(coordinator_root, "coordinator_root")
    coordinator = CapacityCoordinator.open(
        root, installation_id=installation_id, scope_id=scope_id
    )
    report = coordinator.inspect(group)
    held = report["capacity_held_dispatch_ids"]
    cancel_requested = [
        dispatch_id
        for dispatch_id in held
        if coordinator.get_permit(dispatch_id)["state"] == "cancel_requested"
    ]
    budget = (
        None
        if budget_root is None
        else _budget_inspect(_path(budget_root, "budget_root"))
    )
    body = {
        "kind": "local_resource_inspect",
        "result": "inspected",
        "group": report["group"],
        "counts": {
            "queued": report["occupancy"]["queued"],
            "group_inflight": report["occupancy"]["group_inflight"],
            "completion_unknown": len(report["completion_unknown_dispatch_ids"]),
            "cancel_requested": len(cancel_requested),
            "capacity_held": len(held),
            "budget_unknown_reservations": (
                None if budget is None else budget["unknown_count"]
            ),
            "budget_dispatches_consumed": (
                None if budget is None else budget["dispatches_consumed"]
            ),
            "budget_requested_output_tokens_consumed": (
                None if budget is None else budget["output_consumed"]
            ),
            "sum_of_measured_request_wall_ms": (
                None if budget is None else budget["measured_wall_ms"]
            ),
        },
        "queue_dispatch_ids": list(report["queue"]),
        "completion_unknown_dispatch_ids": list(
            report["completion_unknown_dispatch_ids"]
        ),
        "cancel_requested_dispatch_ids": cancel_requested,
        "budget_unknown_dispatch_ids": [] if budget is None else budget["unknown_ids"],
        "unmeasured_wall_dispatch_ids": (
            [] if budget is None else budget["unmeasured_ids"]
        ),
    }
    forbidden = [str(root)]
    if budget_root is not None:
        forbidden.append(str(_path(budget_root, "budget_root")))
    return _public(body, tuple(forbidden))


def reconcile_unresolved(
    *,
    coordinator_root: str | Path,
    budget_root: str | Path,
    installation_id: str,
    scope_id: str,
    dispatch_id: str,
    operator_id: str,
    reason: str,
    now_s: int,
) -> dict[str, Any]:
    """Record one exact unresolved dispatch. Lost completion evidence is not completion."""

    if type(reason) is not str or reason not in _REASONS:
        raise LocalInferenceError("reconcile_decision_rejected")
    now = _int(now_s, 0, _MAX_TIME - 1, "now_s")
    roots = (
        _path(coordinator_root, "coordinator_root"),
        _path(budget_root, "budget_root"),
    )
    coordinator = CapacityCoordinator.open(
        roots[0], installation_id=installation_id, scope_id=scope_id
    )
    ledger = LocalComputeLedger.open(roots[1])
    before = ledger.snapshot()
    reservation = ledger.reservation(dispatch_id)
    permit = coordinator.get_permit(dispatch_id)
    if permit["owner_run"] != reservation["owner"]:
        raise LocalInferenceError("dispatch_conflict")
    # A killed worker cannot run its normal cleanup. Materialize deadline
    # uncertainty here, then mirror it into the ledger without inventing a
    # wall measurement or refunding any part of the dispatched envelope.
    coordinator.expire_due(now)
    permit = coordinator.get_permit(dispatch_id)
    if permit["state"] not in {"completion_unknown", "cancel_requested"}:
        raise LocalInferenceError("permit_not_unresolved")
    if reservation["state"] == "dispatched":
        reservation = ledger.mark_unknown(dispatch_id, owner=reservation["owner"])
    if reservation["state"] != "unknown":
        raise LocalInferenceError("reservation_not_unknown")
    recorded = ledger.record_unresolved(
        dispatch_id, owner=reservation["owner"], operator_id=operator_id
    )
    permit = coordinator.reconcile(
        dispatch_id, operator_id=operator_id, decision=_REASONS[reason], now_s=now
    )
    after = ledger.snapshot()
    _reject_refund(before, after)
    if (
        reservation["observed_request_wall_ms"] is None
        and recorded["observed_request_wall_ms"] is not None
    ):
        raise LocalInferenceError("invalid_completion_evidence")
    if permit["state"] == "completed" or permit["outcome"] == "completed":
        raise LocalInferenceError("invalid_completion_evidence")
    return _public(
        {
            "kind": "local_resource_reconcile",
            "result": "reconciled",
            "dispatch_id": dispatch_id,
            "reason": reason,
            "operator_id": operator_id,
            "capacity_state": permit["state"],
            "capacity_outcome": permit["outcome"],
            "capacity_uncertainty": permit["uncertainty"],
            "called_completed": False,
            "budget_state": recorded["state"],
            "completion_known": False,
            "observed_request_wall_ms": recorded["observed_request_wall_ms"],
            "token_usage_known": False,
            "requested_output_tokens_consumed": after["consumed"][
                "requested_output_tokens"
            ],
            "dispatches_consumed": after["consumed"]["dispatches"],
            "refunded": False,
            "budget_reset": False,
        },
        tuple(str(path) for path in roots),
    )


def settle_clear_response(
    *,
    coordinator_root: str | Path,
    budget_root: str | Path,
    installation_id: str,
    scope_id: str,
    dispatch_id: str,
    milliseconds: int,
    wall_receipt: str,
    now_s: int,
) -> dict[str, Any]:
    """Settle one observed request clock from a clear response receipt."""

    millis = _int(milliseconds, 1, 1_000_000_000 * 1000, "milliseconds")
    now = _int(now_s, 0, _MAX_TIME - 1, "now_s")
    roots = (
        _path(coordinator_root, "coordinator_root"),
        _path(budget_root, "budget_root"),
    )
    coordinator = CapacityCoordinator.open(
        roots[0], installation_id=installation_id, scope_id=scope_id
    )
    ledger = LocalComputeLedger.open(roots[1])
    before = ledger.snapshot()
    reservation = ledger.reservation(dispatch_id)
    permit = coordinator.get_permit(dispatch_id)
    if permit["owner_run"] != reservation["owner"]:
        raise LocalInferenceError("dispatch_conflict")
    if (
        permit["outcome"] == "capacity_released_unresolved"
        or permit["state"] == "released"
    ):
        raise LocalInferenceError("invalid_completion_evidence")
    if reservation["state"] == "completed" and permit["state"] == "completed":
        if (
            reservation["observed_request_wall_ms"] != millis
            or before["reservations"][dispatch_id]["wall_receipt"] != wall_receipt
        ):
            raise LocalInferenceError("wall_receipt_conflict")
        recorded = reservation
    else:
        recorded = ledger.settle_observed_wall(
            dispatch_id,
            owner=reservation["owner"],
            milliseconds=millis,
            receipt=wall_receipt,
            completion_known=True,
        )
        if permit["state"] != "completed":
            permit = coordinator.complete(
                dispatch_id,
                owner_run=permit["owner_run"],
                request_fingerprint=permit["request_fingerprint"],
                now_s=now,
            )
    after = ledger.snapshot()
    _reject_refund(before, after)
    if recorded["observed_request_wall_ms"] != millis:
        raise LocalInferenceError("wall_receipt_conflict")
    return _public(
        {
            "kind": "local_wall_settlement",
            "result": "settled",
            "dispatch_id": dispatch_id,
            "completion_known": True,
            "observed_request_wall_ms": recorded["observed_request_wall_ms"],
            "token_usage_known": False,
            "capacity_state": permit["state"],
            "requested_output_tokens_consumed": after["consumed"][
                "requested_output_tokens"
            ],
            "dispatches_consumed": after["consumed"]["dispatches"],
            "refunded": False,
            "budget_reset": False,
        },
        tuple(str(path) for path in roots),
    )


async def run_conformance_probe(
    spec: Mapping[str, Any],
    *,
    http_client: Any,
    max_output_tokens: int,
    max_dispatches: int,
    max_requested_output_tokens: int,
    max_observed_request_wall_s: int,
    request_timeout_s: int,
    now_s: int,
    expires_at_s: int,
    allow_create: bool,
    required_controls: Sequence[str] = ("native_tool_call",),
    deadline: Any = None,
    coordinator_id: str | None = None,
    runtime_factory: Any = None,
    prepare: Any = None,
) -> dict[str, Any]:
    """Run the explicit tool call, synthetic result, and final text check."""

    if type(allow_create) is not bool or not allow_create:
        raise LocalInferenceError("probe_budget_required")
    output = _int(max_output_tokens, 1, 512, "max_output_tokens")
    dispatches = _int(max_dispatches, 2, 2, "max_dispatches")
    output_budget = _int(
        max_requested_output_tokens,
        output * 2,
        output * 2,
        "max_requested_output_tokens",
    )
    timeout = _int(request_timeout_s, 1, 120, "request_timeout_s")
    wall = _int(
        max_observed_request_wall_s, timeout * 2, 600, "max_observed_request_wall_s"
    )
    now = _int(now_s, 0, _MAX_TIME - 1, "now_s")
    expires = _int(
        expires_at_s, now + 1, min(_MAX_TIME - 1, now + _DAY), "expires_at_s"
    )
    if type(required_controls) is str or not isinstance(required_controls, Sequence):
        raise LocalInferenceError("invalid_field", "required_controls")
    if coordinator_id is not None and (
        type(coordinator_id) is not str or _HEX64.fullmatch(coordinator_id) is None
    ):
        raise LocalInferenceError("invalid_field", "coordinator_id")
    bound_coordinator = _optional_hex(spec, "coordinator_id")
    if coordinator_id is None:
        coordinator_id = bound_coordinator
    elif bound_coordinator is not None and bound_coordinator != coordinator_id:
        raise LocalInferenceError("coordinator_unavailable")
    resolved = _load(spec)
    role_name = spec.get("role")
    role = resolved.roles.get(role_name) if type(role_name) is str else None
    if role is None:
        raise LocalInferenceError("unknown_role")
    if output > role.max_output_tokens:
        raise LocalInferenceError("output_allowance_exceeded")
    roots = (
        _path(spec.get("coordinator_root"), "coordinator_root"),
        _path(spec.get("budget_root"), "budget_root"),
    )
    forbidden = _forbidden(resolved, *roots)
    identity = _identity(resolved, role.role, now, expires)
    blocked = _required_control(role, required_controls)
    if blocked is not None:
        return _receipt(
            identity,
            forbidden,
            result="predispatch_rejected",
            code=blocked[0],
            field=blocked[1],
        )
    tools = conformance_tools()
    identity["schema_hash"] = content_hash(tools)
    try:
        temperature, top_p = _samples(role)
        _encode(
            resolved,
            role.role,
            [{"role": "user", "content": _USER}],
            tools,
            _named_choice(),
            output,
            temperature,
            top_p,
        )
    except LocalProtocolError as exc:
        return _receipt(
            identity,
            forbidden,
            result="predispatch_rejected",
            code=_safe_code(exc),
            field=_safe_field(exc),
        )
    except LocalInferenceError as exc:
        return _receipt(
            identity,
            forbidden,
            result="predispatch_rejected",
            code=exc.code,
            field=exc.safe_ids[0] if exc.safe_ids else None,
        )
    budget_id = _budget_id(spec)
    prepared = _open_resources(
        spec,
        budget_id=budget_id,
        coordinator_id=coordinator_id,
        prepare=prepare,
        max_dispatches=dispatches,
        max_requested_output_tokens=output_budget,
        max_observed_request_wall_s=wall,
    )
    binding = spec if prepared is None else prepared
    ledger_root = _path(
        _pick(binding, "budget_root", spec.get("budget_root")), "budget_root"
    )
    coordinator_root = _path(
        _pick(binding, "coordinator_root", spec.get("coordinator_root")),
        "coordinator_root",
    )
    _verify_fresh_ledger(
        resolved,
        ledger_root,
        budget_id=budget_id,
        max_dispatches=dispatches,
        max_requested_output_tokens=output_budget,
        max_observed_request_wall_s=wall,
    )
    found = _opened_coordinator(resolved, coordinator_root)
    expected = (
        coordinator_id
        if coordinator_id is not None
        else _optional_hex(binding, "coordinator_id")
    )
    if expected is not None and expected != found:
        raise LocalInferenceError("coordinator_unavailable")
    identity["coordinator_id"] = found
    identity["budget_id"] = budget_id
    runtime = _runtime(binding, runtime_factory)
    calls: list[dict[str, Any]] = []
    contacted = False
    messages: list[dict[str, Any]] = [{"role": "user", "content": _USER}]
    choice: Any = _named_choice()
    for phase in ("tool", "final"):
        if phase == "final":
            replay = _replay(resolved, role.role, calls[-1]["sealed"])
            if replay is None:
                return _finish(
                    identity,
                    forbidden,
                    calls,
                    ledger_root,
                    contacted,
                    result="incompatible",
                    code="missing_reasoning_replay",
                    field="reasoning_content",
                )
            messages = _continuation(calls[-1]["sealed"], replay)
            choice = "none"
            try:
                _encode(
                    resolved,
                    role.role,
                    messages,
                    tools,
                    choice,
                    output,
                    temperature,
                    top_p,
                )
            except (LocalProtocolError, LocalInferenceError) as exc:
                return _finish(
                    identity,
                    forbidden,
                    calls,
                    ledger_root,
                    contacted,
                    result="incompatible",
                    code=_safe_code(exc),
                    field=_safe_field(exc),
                )
        started = False

        def on_dispatched() -> None:
            nonlocal started
            started = True

        try:
            response = await runtime.request(
                http_client,
                messages,
                tools=tools,
                tool_choice=choice,
                max_tokens=output,
                temperature=temperature,
                top_p=top_p,
                reasoning_effort=role.reasoning_effort,
                deadline=deadline,
                request_timeout_s=timeout,
                on_dispatched=on_dispatched,
            )
        except (LocalInferenceError, LocalProtocolError) as exc:
            if started:
                return _finish(
                    identity,
                    forbidden,
                    calls,
                    ledger_root,
                    True,
                    result="incomplete",
                    code="completion_unknown",
                )
            if calls:
                return _finish(
                    identity,
                    forbidden,
                    calls,
                    ledger_root,
                    contacted,
                    result="incompatible",
                    code=_safe_code(exc),
                    field=_safe_field(exc),
                )
            if isinstance(exc, LocalProtocolError):
                return _receipt(
                    identity,
                    forbidden,
                    result="predispatch_rejected",
                    code=_safe_code(exc),
                    field=_safe_field(exc),
                )
            raise
        except Exception:
            if started or calls:
                return _finish(
                    identity,
                    forbidden,
                    calls,
                    ledger_root,
                    True,
                    result="incomplete",
                    code="completion_unknown",
                )
            raise
        contacted = True
        sealed = (
            getattr(response, "extensions", {}).get("local_sealed_chat")
            if getattr(response, "extensions", None) is not None
            else None
        )
        if type(sealed) is not SealedChat:
            return _finish(
                identity,
                forbidden,
                calls,
                ledger_root,
                True,
                result="incomplete",
                code="completion_unknown",
            )
        record = _call_record(phase, sealed)
        record["sealed"] = sealed
        calls.append(record)
        failed = (phase == "tool" and not record["arguments_matched"]) or (
            phase == "final" and not record["final_text"]
        )
        if failed:
            return _finish(
                identity,
                forbidden,
                calls,
                ledger_root,
                True,
                result="incompatible",
                code="unexpected_tool_batch" if phase == "tool" else "unexpected_final",
            )
    return _finish(
        identity, forbidden, calls, ledger_root, True, result=_PASS, code=None
    )


def _named_choice() -> dict[str, Any]:
    return {"type": "function", "function": {"name": _TOOL}}


def _finish(
    identity: dict[str, Any],
    forbidden: Sequence[str],
    calls: Sequence[Mapping[str, Any]],
    ledger_root: Path,
    contacted: bool,
    *,
    result: str,
    code: str | None,
    field: str | None = None,
) -> dict[str, Any]:
    public_calls = [
        {key: value for key, value in call.items() if key != "sealed"} for call in calls
    ]
    ledger = _ledger_view(ledger_root)
    if result == _PASS and not (
        len(public_calls) == 2
        and public_calls[0].get("arguments_matched") is True
        and public_calls[1].get("final_text") is True
        and all(call["tool_executed"] is False for call in public_calls)
        and ledger is not None
        and ledger["dispatches_consumed"] >= len(public_calls)
        and ledger["unsettled_dispatch_ids"] == []
    ):
        result = "incompatible"
        if ledger is not None and ledger["dispatches_consumed"] < len(public_calls):
            code = "budget_not_charged"
    return _receipt(
        identity,
        forbidden,
        result=result,
        code=code,
        field=field,
        calls=public_calls,
        ledger=ledger,
        contacted=contacted,
    )


def _receipt(
    identity: Mapping[str, Any],
    forbidden: Sequence[str],
    *,
    result: str,
    code: str | None,
    field: str | None = None,
    calls: Sequence[Mapping[str, Any]] | None = None,
    ledger: Mapping[str, Any] | None = None,
    contacted: bool = False,
) -> dict[str, Any]:
    known = bool(calls) and all(
        call.get("usage_status") == "reported" for call in calls or ()
    )
    body: dict[str, Any] = {
        "kind": _KIND,
        "result": result,
        "state": _state(result),
        "admission": _ADMISSION if result == _PASS else "none",
        "future_reliability": _FUTURE,
        "guarantees_future_behavior": False,
        "statement": _STATEMENT,
        "network": "contacted" if contacted else "not_contacted",
        "tool_executed": False,
        "mathematical_work": False,
        "fit_guarantee": False,
        "requested_tool": _TOOL,
        "provider_token_usage": (
            None if not known else [call.get("usage") for call in calls or ()]
        ),
        "calls": list(calls or ()),
        "ledger": None if ledger is None else dict(ledger),
        **dict(identity),
    }
    if code is not None:
        body["code"] = code
    if field is not None:
        body["field"] = field
    return _public(body, forbidden)


def _identity(
    resolved: ResolvedLocalRun, role_name: str, now: int, expires: int
) -> dict[str, Any]:
    role = resolved.roles[role_name]
    return {
        "profile_hash": resolved.profile_hash,
        "selection_hash": resolved.selection_hash,
        "deployment_fingerprint": role.deployment_fingerprint,
        "schema_hash": None,
        "role": role.role,
        "deployment_id": role.deployment_id,
        "observed_at_s": now,
        "expires_at_s": expires,
    }


def _state(result: str) -> str:
    if result == _PASS:
        return "ready"
    if result == "incomplete":
        return "degraded"
    if result in {"predispatch_rejected", "incompatible"}:
        return "incompatible"
    return "protocol_unverified"


def _valid_usage(value: Any) -> bool:
    return (
        type(value) is dict
        and bool(value)
        and set(value) <= {"prompt_tokens", "completion_tokens", "total_tokens"}
        and all(type(item) is int and 0 <= item <= 2**63 - 1 for item in value.values())
    )


def _valid_evidence(receipt: Mapping[str, Any]) -> bool:
    calls = receipt.get("calls")
    if type(calls) is not list or len(calls) > 2:
        return False
    for index, call in enumerate(calls):
        if type(call) is not dict or set(call) != {
            "phase",
            "finish_reason",
            "usage_status",
            "usage",
            "tool_executed",
            "arguments_matched",
            "final_text",
            "reasoning_fields",
        }:
            return False
        if (
            call["phase"] != ("tool" if index == 0 else "final")
            or call["tool_executed"] is not False
        ):
            return False
        if (
            type(call["arguments_matched"]) is not bool
            or type(call["final_text"]) is not bool
        ):
            return False
        fields = call["reasoning_fields"]
        if (
            type(fields) is not list
            or len(fields) > 8
            or any(
                type(field) is not str or not _NAME.fullmatch(field) for field in fields
            )
        ):
            return False
        if call["usage_status"] == "reported":
            if not _valid_usage(call["usage"]):
                return False
        elif call["usage_status"] != "unknown" or call["usage"] is not None:
            return False
    reported_usage = (
        [call["usage"] for call in calls]
        if calls and all(call["usage_status"] == "reported" for call in calls)
        else None
    )
    if receipt.get("provider_token_usage") != reported_usage:
        return False
    if receipt.get("result") == _PASS:
        if (
            len(calls) != 2
            or calls[0]["finish_reason"] != "tool_calls"
            or calls[0]["arguments_matched"] is not True
        ):
            return False
        if calls[1]["finish_reason"] != "stop" or calls[1]["final_text"] is not True:
            return False
        ledger = receipt.get("ledger")
        if (
            type(ledger) is not dict
            or type(ledger.get("dispatches_consumed")) is not int
            or ledger["dispatches_consumed"] < 2
        ):
            return False
        if (
            ledger.get("unmeasured_wall_dispatch_ids") != []
            or ledger.get("unsettled_dispatch_ids") != []
            or ledger.get("refunded") is not False
            or ledger.get("reset") is not False
        ):
            return False
    return True


def _accepted(
    receipt: Mapping[str, Any] | None,
    resolved: ResolvedLocalRun,
    role_name: str,
    now: int,
) -> Mapping[str, Any] | None:
    if type(receipt) is not dict or not _same_deployment(
        receipt, resolved, role_name, now
    ):
        return None
    if not _valid_evidence(receipt):
        return None
    schema_hash = receipt.get("schema_hash")
    if type(schema_hash) is str and schema_hash != content_hash(conformance_tools()):
        return None
    if receipt.get("result") == _PASS:
        if (
            type(schema_hash) is not str
            or receipt.get("admission") != _ADMISSION
            or receipt.get("tool_executed") is not False
        ):
            return None
    elif receipt.get("result") not in {
        "predispatch_rejected",
        "incompatible",
        "incomplete",
    }:
        return None
    return receipt


def _same_deployment(
    receipt: Mapping[str, Any], resolved: ResolvedLocalRun, role_name: str, now: int
) -> bool:
    role = resolved.roles[role_name]
    observed, expires = receipt.get("observed_at_s"), receipt.get("expires_at_s")
    return (
        receipt.get("kind") == _KIND
        and type(receipt.get("result")) is str
        and receipt.get("result") in _RESULTS
        and receipt.get("future_reliability") == _FUTURE
        and receipt.get("guarantees_future_behavior") is False
        and receipt.get("mathematical_work") is False
        and receipt.get("fit_guarantee") is False
        and receipt.get("tool_executed") is False
        and receipt.get("profile_hash") == resolved.profile_hash
        and receipt.get("selection_hash") == resolved.selection_hash
        and receipt.get("deployment_fingerprint") == role.deployment_fingerprint
        and receipt.get("role") == role.role
        and type(observed) is int
        and type(expires) is int
        and 0 <= observed <= now < expires <= observed + _DAY
    )


def _role_view(
    resolved: ResolvedLocalRun,
    role_name: str,
    now: int,
    receipt: Mapping[str, Any] | None,
) -> dict[str, Any]:
    role = resolved.roles[role_name]
    deployment = resolved.document.deployments[role.deployment_id]
    unknown = list(_UNKNOWN)
    identity = {}
    for name, item in deployment.identity.items():
        if item.source == "configured" and item.value is not None:
            identity[name] = {"source": "configured", "value": item.value}
        else:
            identity[name] = {"source": "unknown"}
            unknown.append(name)
    configured: dict[str, Any] = {
        "model": {"source": "configured", "value": role.model},
        "context_tokens": {"source": "configured", "value": role.context_tokens},
        "max_output_tokens": {"source": "configured", "value": role.max_output_tokens},
        "tools": {"source": "configured", "value": role.tools},
        "reasoning_mode": {"source": "configured", "value": role.reasoning_mode},
        "output_limit_includes_reasoning": {
            "source": "configured",
            "value": role.output_limit_includes_reasoning,
        },
        "execution": {"source": "configured", "value": role.execution},
        "identity": identity,
    }
    if role.reasoning_effort is None:
        configured["reasoning_effort"] = {"source": "unknown"}
        unknown.append("reasoning_effort")
    else:
        configured["reasoning_effort"] = {
            "source": "configured",
            "value": role.reasoning_effort,
        }
    probed: dict[str, Any] = {}
    state, expires, code, field = "protocol_unverified", None, None, None
    if receipt is not None:
        state = _state(str(receipt.get("result")))
        expires = receipt.get("expires_at_s")
        code = (
            receipt.get("code")
            if type(receipt.get("code")) is str and _NAME.fullmatch(receipt["code"])
            else None
        )
        field = (
            receipt.get("field")
            if type(receipt.get("field")) is str and _NAME.fullmatch(receipt["field"])
            else None
        )
        calls = receipt.get("calls")
        if receipt.get("result") == _PASS and type(calls) is list:
            probed = {
                "native_tool_call": True,
                "tool_result_continuation": True,
                "final_text": True,
                "tool_executed": False,
                "requested_tool": _TOOL,
            }
        usage = receipt.get("provider_token_usage")
        if (
            type(usage) is list
            and usage
            and all(type(item) is dict and item for item in usage)
        ):
            probed["provider_token_usage"] = usage
        else:
            unknown.append("provider_token_usage")
    else:
        unknown.append("provider_token_usage")
    return {
        "state": state,
        "future_reliability": _FUTURE,
        "evidence_expires_at_s": expires,
        "statement": (
            _STATEMENT if receipt is not None else "No current conformance evidence."
        ),
        "code": code,
        "field": field,
        "observed_at_s": now,
        "sources": {
            "configured": configured,
            "discovered": {},
            "probed": probed,
            "unknown": sorted(set(unknown)),
        },
    }


def _required_control(role: Any, required: Sequence[str]) -> tuple[str, str] | None:
    checks = {
        "native_tool_call": role.tools == "native_required",
        "named_tool_choice": role.tools == "native_required",
        "reasoning_on": role.reasoning_mode == "on",
        "reasoning_off": role.reasoning_mode == "off",
        "temperature": role.sampling.temperature.policy != "forbidden",
        "hard_output_limit": False,
        "context_enforcement": False,
        "streaming_completion": False,
    }
    for name in ("native_tool_call", *required):
        if type(name) is not str or name not in checks or not checks[name]:
            safe = (
                name
                if type(name) is str and _NAME.fullmatch(name)
                else "required_controls"
            )
            return ("unsupported_control", safe)
    return None


def _encode(
    resolved: ResolvedLocalRun,
    role_name: str,
    messages: Sequence[Mapping[str, Any]],
    tools: Sequence[Mapping[str, Any]],
    tool_choice: Any,
    max_output_tokens: int,
    temperature: Any,
    top_p: Any,
) -> None:
    role = resolved.roles[role_name]
    policy = resolved.document.deployments[role.deployment_id].protocol
    body = reasoning_request_body(policy, role.reasoning_mode, role.reasoning_effort)
    build_chat_request(
        dialect=role.dialect,
        model=role.model,
        messages=messages,
        context_tokens=role.context_tokens,
        max_output_tokens=max_output_tokens,
        tools=tools,
        tool_choice=tool_choice,
        temperature=temperature,
        top_p=top_p,
        sampling_supported=True,
        reasoning_mode=role.reasoning_mode,
        reasoning_body=body or None,
        reasoning_control_evidence="configured" if body else None,
        history_replay_fields=policy.history_replay_fields,
        require_history_replay=policy.require_history_replay,
        template_overhead_tokens=policy.template_overhead_tokens,
        output_includes_reasoning={"true": True, "false": False}.get(
            role.output_limit_includes_reasoning
        ),
    )


def _samples(role: Any) -> tuple[Any, Any]:
    return _fixed(role.sampling.temperature, "temperature"), _fixed(
        role.sampling.top_p, "top_p"
    )


def _fixed(axis: Any, field: str) -> Any:
    if axis.policy != "fixed":
        return None
    text = axis.value
    if type(text) is not str:
        raise LocalInferenceError("invalid_field", field)
    if "." not in text:
        return int(text)
    number = float(text)
    if number != number or number in {float("inf"), float("-inf")}:
        raise LocalInferenceError("invalid_field", field)
    return number


def _replay(
    resolved: ResolvedLocalRun, role_name: str, sealed: SealedChat
) -> dict[str, str] | None:
    policy = resolved.document.deployments[
        resolved.roles[role_name].deployment_id
    ].protocol
    found: dict[str, str] = {}
    for field in policy.history_replay_fields:
        value = sealed.reasoning_fields.get(field)
        if type(value) is str and value.strip():
            found[field] = value
        elif policy.require_history_replay:
            return None
    if policy.require_history_replay and set(found) != set(
        policy.history_replay_fields
    ):
        return None
    return found


def _continuation(
    sealed: SealedChat, replay: Mapping[str, str]
) -> list[dict[str, Any]]:
    call = sealed.tool_calls[0]
    assistant: dict[str, Any] = {
        "role": "assistant",
        "content": sealed.text,
        "tool_calls": [
            {
                "id": call["id"],
                "type": "function",
                "function": {"name": call["name"], "arguments": call["arguments_json"]},
            }
        ],
    }
    assistant.update(dict(replay))
    return [
        {"role": "user", "content": _USER},
        assistant,
        {"role": "tool", "tool_call_id": call["id"], "content": _TOOL_RESULT},
    ]


def _call_record(phase: str, sealed: SealedChat) -> dict[str, Any]:
    status, usage = _usage(sealed)
    return {
        "phase": phase,
        "finish_reason": sealed.finish_reason,
        "usage_status": status,
        "usage": usage,
        "tool_executed": False,
        "arguments_matched": phase == "tool" and _matched(sealed),
        "final_text": phase == "final"
        and sealed.finish_reason == "stop"
        and not sealed.tool_calls
        and bool(sealed.text.strip()),
        "reasoning_fields": sorted(
            key
            for key, value in dict(sealed.reasoning_fields).items()
            if type(value) is str and value.strip()
        ),
    }


def _matched(sealed: SealedChat) -> bool:
    if (
        not sealed.arguments_schema_validated
        or sealed.finish_reason != "tool_calls"
        or len(sealed.tool_calls) != 1
    ):
        return False
    call = sealed.tool_calls[0]
    return (
        call.get("name") == _TOOL
        and call.get("arguments") == _EXPECTED
        and type(call.get("id")) is str
        and bool(call.get("id"))
        and type(call.get("arguments_json")) is str
    )


def _usage(sealed: SealedChat) -> tuple[str, dict[str, int] | None]:
    if sealed.usage_status != "reported" or sealed.usage is None:
        return "unknown", None
    body = {
        key: value
        for key, value in dict(sealed.usage).items()
        if key in {"prompt_tokens", "completion_tokens", "total_tokens"}
        and type(value) is int
        and value >= 0
    }
    return ("reported", body) if body else ("unknown", None)


def _open_resources(
    spec: Mapping[str, Any],
    *,
    budget_id: str,
    coordinator_id: str | None,
    prepare: Any,
    **ceilings: int,
) -> Any:
    record = {
        "snapshot": spec["snapshot"],
        "role": spec["role"],
        "coordinator_root": str(spec["coordinator_root"]),
        "budget_root": str(spec["budget_root"]),
        "budget_id": budget_id,
    }
    if coordinator_id is not None:
        record["coordinator_id"] = coordinator_id
    opener = prepare if prepare is not None else _default_prepare
    return opener(record, allow_create=True, **ceilings)


def _default_prepare(
    record: Mapping[str, Any], allow_create: bool, **ceilings: int
) -> Any:
    try:
        from .runtime import prepare_resources
    except ImportError:
        raise LocalInferenceError("runtime_unavailable") from None
    return prepare_resources(dict(record), allow_create=allow_create, **ceilings)


def _runtime(binding: Any, factory: Any) -> Any:
    if factory is not None:
        return factory(binding)
    try:
        from .runtime import LocalRuntime
    except ImportError:
        raise LocalInferenceError("runtime_unavailable") from None
    return LocalRuntime(binding)


def _verify_fresh_ledger(
    resolved: ResolvedLocalRun,
    budget_root: Path,
    *,
    budget_id: str,
    max_dispatches: int,
    max_requested_output_tokens: int,
    max_observed_request_wall_s: int,
) -> None:
    state = LocalComputeLedger.open(budget_root).snapshot()
    ceilings = state["ceilings"]
    if state["ledger_id"] != budget_id:
        raise LocalInferenceError("ledger_identity_mismatch")
    if state["segments"][-1]["profile_hash"] != resolved.profile_hash:
        raise LocalInferenceError("profile_hash_mismatch")
    if (
        ceilings["dispatches"] != max_dispatches
        or ceilings["requested_output_tokens"] != max_requested_output_tokens
        or ceilings["observed_request_wall_ms"] != max_observed_request_wall_s * 1000
    ):
        raise LocalInferenceError("probe_budget_mismatch")
    if (
        state["consumed"]["dispatches"]
        or state["consumed"]["requested_output_tokens"]
        or state["consumed"]["observed_request_wall_ms"]
        or state["reserved"]["dispatches"]
        or state["extensions"]
    ):
        raise LocalInferenceError("probe_budget_rejected")


def _ledger_view(budget_root: Path) -> dict[str, Any] | None:
    try:
        state = LocalComputeLedger.open(budget_root).snapshot()
    except LocalInferenceError:
        return None
    return {
        "dispatches_consumed": state["consumed"]["dispatches"],
        "requested_output_tokens_consumed": state["consumed"][
            "requested_output_tokens"
        ],
        "sum_of_measured_request_wall_ms": state["consumed"][
            "observed_request_wall_ms"
        ],
        "unmeasured_wall_dispatch_ids": [
            key
            for key, item in state["reservations"].items()
            if item["state"] in {"dispatched", "unknown"}
            and item["wall_receipt"] is None
        ],
        "unsettled_dispatch_ids": [
            key
            for key, item in state["reservations"].items()
            if item["state"] in {"dispatched", "unknown"}
        ],
        "refunded": False,
        "reset": False,
    }


def _budget_inspect(budget_root: Path) -> dict[str, Any]:
    state = LocalComputeLedger.open(budget_root).snapshot()
    return {
        "unknown_count": sum(
            item["state"] == "unknown" for item in state["reservations"].values()
        ),
        "unknown_ids": [
            key
            for key, item in state["reservations"].items()
            if item["state"] == "unknown"
        ],
        "unmeasured_ids": [
            key
            for key, item in state["reservations"].items()
            if item["state"] in {"dispatched", "unknown"}
            and item["wall_receipt"] is None
        ],
        "dispatches_consumed": state["consumed"]["dispatches"],
        "output_consumed": state["consumed"]["requested_output_tokens"],
        "measured_wall_ms": state["consumed"]["observed_request_wall_ms"],
    }


def _opened_coordinator(resolved: ResolvedLocalRun, root: Path) -> str:
    coordinator = resolved.document.coordinator
    if coordinator is None:
        raise LocalInferenceError("coordinator_required")
    return CapacityCoordinator.open(
        root, installation_id=coordinator.installation_id, scope_id=coordinator.scope_id
    ).coordinator_id()


def _load(spec: Mapping[str, Any]) -> ResolvedLocalRun:
    snapshot = spec.get("snapshot") if isinstance(spec, Mapping) else None
    if type(snapshot) is not dict:
        raise LocalInferenceError("snapshot_kind_mismatch")
    return load_private_worker_snapshot(snapshot)


def _budget_id(spec: Mapping[str, Any]) -> str:
    primary = spec.get("budget_id32hex", spec.get("budget_id"))
    alias = spec.get("budget_id")
    if (
        type(primary) is not str
        or _HEX32.fullmatch(primary) is None
        or (alias is not None and alias != primary)
    ):
        raise LocalInferenceError("invalid_field", "budget_id")
    return primary


def _optional_hex(binding: Any, name: str) -> str | None:
    value = (
        binding.get(name)
        if isinstance(binding, Mapping)
        else getattr(binding, name, None)
    )
    if value is None:
        return None
    if type(value) is not str or _HEX64.fullmatch(value) is None:
        raise LocalInferenceError("invalid_field", "coordinator_id")
    return value


def _pick(binding: Any, name: str, fallback: Any) -> Any:
    if isinstance(binding, Mapping) and name in binding:
        return binding[name]
    value = getattr(binding, name, None)
    return fallback if value is None else value


def _reject_refund(before: Mapping[str, Any], after: Mapping[str, Any]) -> None:
    for key in ("dispatches", "requested_output_tokens"):
        if (
            after["consumed"][key] < before["consumed"][key]
            or after["ceilings"][key] != before["ceilings"][key]
        ):
            raise LocalInferenceError("budget_reset_forbidden")
    if after["extensions"] != before["extensions"]:
        raise LocalInferenceError("budget_reset_forbidden")


def _forbidden(resolved: ResolvedLocalRun, *paths: Path) -> tuple[str, ...]:
    values = [str(path) for path in paths]
    for endpoint in resolved.document.endpoints.values():
        values.append(endpoint.base_url)
        if endpoint.auth.name is not None:
            values.append(endpoint.auth.name)
    return tuple(values)


def _public(payload: dict[str, Any], forbidden: Sequence[str]) -> dict[str, Any]:
    encoded = canonical_json(payload)
    for item in forbidden:
        if type(item) is str and len(item) >= 4 and item in encoded:
            raise LocalInferenceError("redaction_failed")
    body = json.loads(encoded)
    if type(body) is not dict:
        raise LocalInferenceError("redaction_failed")
    return body


def _path(value: Any, field: str) -> Path:
    if not isinstance(value, (str, Path)):
        raise LocalInferenceError("invalid_field", field)
    path = Path(value)
    if path.is_symlink():
        raise LocalInferenceError("symlink_forbidden")
    return path


def _int(value: Any, low: int, high: int, field: str) -> int:
    if type(value) is not int or isinstance(value, bool) or value < low or value > high:
        raise LocalInferenceError("invalid_field", field)
    return value


def _safe_code(exc: BaseException) -> str:
    code = getattr(exc, "code", None)
    return (
        code if type(code) is str and _SAFE_CODE.fullmatch(code) else "invalid_request"
    )


def _safe_field(exc: BaseException) -> str | None:
    if isinstance(exc, LocalInferenceError) and exc.safe_ids:
        return exc.safe_ids[0]
    details = getattr(exc, "details", None)
    field = details.get("field") if type(details) is dict else None
    return field if type(field) is str and _NAME.fullmatch(field) else None
