"""Borrow existing Mini proof capacity for bounded, isolated research work.

This module grants no new run budget. The coordinator must durably save the
debit before dispatch, fence concrete provider requests, and retain the parent
cost controller and run deadlines. Conversation indices belong to resumable
proof transcripts and are deliberately independent of this budget transfer.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, replace
import math
from typing import Any

from .mini_session.action import ActionBudget


@dataclass(frozen=True)
class Donor:
    """An uncommitted offer from one existing role's action budget."""

    action_id: str
    client: Any
    role: str
    request_limit: int
    remaining_seconds: float | None
    initial_invocations: int


def _supported_client(client: Any) -> bool:
    from .claude_code_subscription import ClaudeCodeSubscriptionClient
    from .codex_subscription import CodexSubscriptionClient
    from .models import OpenAICompatClient

    # Reconstructing an arbitrary subclass or wrapper can lose authentication,
    # routing, or safety restrictions. Support only the concrete CLI transports.
    return type(client) in {
        OpenAICompatClient, CodexSubscriptionClient, ClaudeCodeSubscriptionClient,
    } and bool(getattr(client, "supports_transport_dispatch_authorization", False))


def clone_research_client(client: Any) -> Any:
    """Create an owned transport without changing its provider or role policy.

    No generation or subscription preflight occurs here. The caller must close
    the returned client, never the donor. A deep copy includes dynamic policy
    attributes that dataclass replacement would silently omit.
    """
    from .models import OpenAICompatClient

    if not _supported_client(client):
        raise ValueError("native research cannot clone this unsupported transport")
    if bool(getattr(client, "_closed", False)) or bool(
        getattr(getattr(client, "client", None), "is_closed", False)
    ):
        raise ValueError("native research cannot clone a closed transport")
    config = copy.deepcopy(client.cfg)
    if type(client) is not OpenAICompatClient:
        return type(client)(config)
    clone = OpenAICompatClient(
        config,
        provider_lane_health_registry=client._provider_lane_health_registry_for_dispatch(),
    )
    # Keep discovered restrictions and route headers while giving research its
    # own response metadata, HTTP tasks, semaphores, and lifetime. Sharing the
    # health registry prevents a new transport from bypassing a provider outage.
    for name in (
        "headers", "_stop", "_chat_tools_require_reasoning_effort_none",
        "_responses_tools_reasoning_required", "_reasoning_disable_rejected",
        "_reasoning_disable_supported", "_responses_unsupported_parameters",
        "_runtime_prompt_budget_cap_tokens", "_tools_capability",
        "_unsupported_payload_parameters", "_MAX_TRANSPORT_ATTEMPTS",
    ):
        if hasattr(client, name):
            setattr(clone, name, copy.deepcopy(getattr(client, name)))
    return clone


def _parent_remaining(session: Any) -> float | None:
    getter = getattr(session, "_run_governor_remaining_s", None)
    if not callable(getter):
        return None
    remaining = getter()
    if remaining is None:
        return None
    if isinstance(remaining, bool):
        raise ValueError("invalid remaining parent time")
    seconds = float(remaining)
    if not math.isfinite(seconds) or seconds <= 0:
        raise ValueError("remaining parent time is exhausted or invalid")
    return seconds


def _donor(session: Any, action: Any, parent_seconds: float | None) -> Donor | None:
    action_id = str(getattr(action, "id", ""))
    role = {"conversation_turn_prove": "prove", "conversation_turn_refine": "refine"}.get(action_id)
    if role is None or getattr(action, "role", None) != role:
        return None
    client = getattr(action, "client", None)
    if not _supported_client(client) or bool(getattr(client, "_closed", False)) or bool(
        getattr(getattr(client, "client", None), "is_closed", False)
    ):
        return None
    budget = getattr(session, "budgets", {}).get(action_id)
    if not isinstance(budget, ActionBudget) or budget.scope != "session" or budget.exhausted():
        return None
    if any(type(value) is not int for value in (
        budget.invocations, budget.max_invocations, budget.max_aggregate_invocations,
    )) or budget.invocations < 0:
        return None
    # The donor must retain its own next proof turn. A sibling sample or
    # a disabled refiner is not a promise that this session can use the result.
    for cap in (budget.max_invocations, budget.max_aggregate_invocations):
        if cap >= 0 and cap - budget.invocations < 2:
            return None
    request_limit = min(6, max(0, int(getattr(action, "max_tool_calls_per_turn", 0))))
    provider_cap = max(0, int(getattr(action, "provider_dispatch_limit", 0)))
    if provider_cap:
        spent = max(
            0,
            int(getattr(session, "provider_dispatches_started_total", 0)),
            int(getattr(session, "provider_calls_completed_total", 0)),
        )
        request_limit = min(request_limit, max(0, provider_cap - spent - 1))
    if request_limit <= 0:
        return None
    deadlines = [] if parent_seconds is None else [parent_seconds]
    # These action envelopes are already hard bounds: the normal factory
    # derives them from hard provider policy, while soft providers get zero.
    # Explicit positive action bounds are enforced even with a soft transport.
    # Borrow conservatively inside either proof/formalization envelope; never
    # invent a hard turn limit from a soft client's request timeout.
    for name in ("llm_turn_elapsed_s", "formalization_llm_turn_elapsed_s"):
        cap = getattr(action, name, 0.0)
        if isinstance(cap, bool) or not isinstance(cap, (int, float)) or not math.isfinite(cap):
            return None
        if cap > 0:
            deadlines.append(float(cap))
    for cap, spent in (
        (budget.max_total_seconds, budget.total_seconds),
        (budget.max_aggregate_seconds, budget.unproductive_seconds),
    ):
        if not math.isfinite(cap) or not math.isfinite(spent) or spent < 0:
            return None
        if cap > 0:
            # Preserve some action-time capacity for the promised next proof.
            remaining = (cap - spent) / 2
            if remaining <= 0:
                return None
            deadlines.append(remaining)
    return Donor(action_id, client, role, request_limit,
                 min(deadlines) if deadlines else None, budget.invocations)


def select_donor(session: Any) -> Donor | None:
    """Read an existing role allocation; never top up a budget to create one."""
    if getattr(session, "terminal_failure_reason", "") or getattr(session, "root_finalized", False):
        return None
    try:
        if hasattr(session, "max_iterations"):
            if (
                type(session.max_iterations) is not int
                or type(getattr(session, "iteration", None)) is not int
                or session.max_iterations - session.iteration < 2
            ):
                return None
        parent_seconds = _parent_remaining(session)
        controller = getattr(session, "cost_controller", None)
        if controller is not None:
            if controller.exhausted():
                return None
            remaining = controller.remaining_usd()
            if remaining is not None and (not math.isfinite(remaining) or remaining <= 0):
                return None
        actions = {getattr(action, "id", ""): action for action in getattr(session, "actions", ())}
        for action_id in ("conversation_turn_prove", "conversation_turn_refine"):
            action = actions.get(action_id)
            if action is not None:
                donor = _donor(session, action, parent_seconds)
                if donor is not None:
                    return donor
    except (TypeError, ValueError, OverflowError, AttributeError):
        return None
    return None


def debit_donor(session: Any, donor: Donor) -> Donor:
    """Debit once and return refreshed bounds; checkpoint before dispatch.

    The caller must use the returned offer, because time may have passed since
    selection. Parent deadlines must also be checked after checkpoint awaits.
    """
    current = select_donor(session)
    if (
        current is None
        or current.action_id != donor.action_id
        or current.client is not donor.client
        or current.role != donor.role
        or current.initial_invocations != donor.initial_invocations
        or current.request_limit != donor.request_limit
    ):
        raise ValueError("native research donor changed or is already spent")
    bounds = [value for value in (donor.remaining_seconds, current.remaining_seconds)
              if value is not None]
    if any(isinstance(value, bool) or not isinstance(value, (int, float))
           or not math.isfinite(value) or value <= 0 for value in bounds):
        raise ValueError("native research donor time limit is invalid")
    budget = session.budgets[donor.action_id]
    cost_continuation = getattr(session, "_cost_budget_continuation_enabled", None)
    money_governed = callable(cost_continuation) and cost_continuation()
    if budget.max_invocations >= 0 and not money_governed:
        # A finite count allocation funds both proof and research. Preserve it
        # across ordinary repair-ticket soft-cap renewals; otherwise those
        # renewals refund the donated invocation. Dollar-governed renewal and
        # explicitly unlimited counts keep their existing authority.
        limits = [budget.max_invocations]
        if budget.max_aggregate_invocations >= 0:
            limits.append(budget.max_aggregate_invocations)
        budget.max_aggregate_invocations = min(limits)
    budget.consume(0.0)
    # Research occupies a real scheduler quantum. Transcript turn identities
    # are separate and remain untouched.
    if hasattr(session, "iteration"):
        session.iteration += 1
    return replace(current, remaining_seconds=min(bounds) if bounds else None)


def charge_elapsed(session: Any, donor: Donor, seconds: float) -> None:
    """Charge elapsed research time without consuming another invocation."""
    if isinstance(seconds, bool) or not isinstance(seconds, (int, float)) or not math.isfinite(seconds) or seconds < 0:
        raise ValueError("research elapsed time must be finite and nonnegative")
    budget = session.budgets.get(donor.action_id)
    if not isinstance(budget, ActionBudget) or budget.invocations <= donor.initial_invocations:
        raise ValueError("native research donor debit is missing or stale")
    total = budget.total_seconds + float(seconds)
    unproductive = budget.unproductive_seconds + float(seconds)
    if not math.isfinite(total) or not math.isfinite(unproductive):
        raise ValueError("research elapsed charge exceeds finite budget accounting")
    budget.total_seconds = total
    budget.unproductive_seconds = unproductive
