"""Phase-specific temperature policy for mini prover LLM calls."""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from .pricing import base_url_matches_provider, provider_for_base_url
from .sampling_controls import (
    API_DEFAULT_TEMPERATURE,
    is_api_default_temperature_override,
)


@dataclass(frozen=True)
class MiniPhaseTemperatures:
    """Opt-in temperature policy for mini prover phases.

    ``sample_temperature`` remains the parallel-sample exploration identity.
    When this policy is enabled, constrained phases such as Lean repair and
    formalization deliberately override hot sample stripes.
    """

    enabled: bool = False
    # Planning is a constrained structured-output phase, not an exploration
    # stripe.  Keep it deterministic; proof/refinement phases own diversity.
    planner: float = 0.10
    initial_proof: float = 0.45
    formalization_helper: float = 0.10
    lean_repair: float = 0.05
    refine: float = 0.25
    route_assembly: float = 0.25
    stagnation_escape: float = 0.85
    use_sample_temperature_for_initial: bool = True

    def __post_init__(self) -> None:
        for field_name in (
            "planner",
            "initial_proof",
            "formalization_helper",
            "lean_repair",
            "refine",
            "route_assembly",
            "stagnation_escape",
        ):
            value = getattr(self, field_name)
            try:
                temp = float(value)
            except Exception as exc:
                raise ValueError(
                    f"MiniPhaseTemperatures.{field_name} must be a finite float"
                ) from exc
            if not math.isfinite(temp):
                raise ValueError(
                    f"MiniPhaseTemperatures.{field_name} must be a finite float"
                )


@dataclass(frozen=True)
class MiniTemperatureContext:
    role: str = "prove"
    action_id: str = ""
    sample_temperature: Optional[float] = None
    selected_work_item_record: Optional[Mapping[str, Any]] = None
    selected_work_type: str = ""
    selected_node_id: str = ""
    repair_turn_active: bool = False
    repair_self_check: bool = False
    repair_ticket_active: bool = False
    pending_repair_ticket: bool = False
    formalization_helper_contract: bool = False
    stagnation_counter: int = 0
    max_stagnation: int = 0
    stagnation_escape: bool = False
    phase_hint: str = ""


@dataclass(frozen=True)
class MiniTemperatureDecision:
    value: Optional[float]
    phase_key: str
    source: str
    reason: str = ""
    sample_temperature: Optional[float] = None
    api_default: bool = False

    def provider_temperature_override(self) -> Any:
        return API_DEFAULT_TEMPERATURE if self.api_default else self.value

    def metadata(self, client: Any = None) -> dict[str, Any]:
        return {
            "temperature_requested": self.value,
            "effective_temperature": self.value,
            "temperature_api_default": bool(self.api_default),
            "temperature_phase_key": self.phase_key,
            "temperature_phase": self.phase_key,
            "temperature_source": self.source,
            "temperature_reason": self.reason,
            "sample_temperature": self.sample_temperature,
            **_static_provider_sampling_metadata(client, self.value),
        }


_FORMALIZATION_WORK_TYPES = frozenset(
    {
        "formalize_missing_obligation",
        "formalize_claim",
        "formalize_bridge",
        "formalize_helper",
        "formalization_helper",
        "formalization_repair",
    }
)


def _finite_temperature(value: Any) -> Optional[float]:
    if value is None:
        return None
    try:
        temp = float(value)
    except Exception:
        return None
    if not math.isfinite(temp):
        return None
    return max(0.0, min(2.0, temp))


def _client_base_url(client: Any) -> str:
    cfg = getattr(client, "cfg", None)
    return str(
        getattr(client, "base_url", "")
        or getattr(cfg, "base_url", "")
        or ""
    )


def _client_model(client: Any) -> str:
    cfg = getattr(client, "cfg", None)
    return str(getattr(cfg, "model", "") or "")


def _client_reasoning_effort(client: Any) -> str:
    cfg = getattr(client, "cfg", None)
    return str(getattr(cfg, "reasoning_effort", "") or "").strip().lower()


def _client_thinking_enabled(client: Any) -> bool:
    cfg = getattr(client, "cfg", None)
    return bool(getattr(cfg, "thinking_enabled", False))


def _sampling_controls_support_static(client: Any) -> Optional[bool]:
    """Mirror provider constraints when statically knowable.

    ``None`` means an aggregate wrapper may select either a supporting or a
    non-supporting backend at runtime, so provider telemetry must come from the
    actual call rather than a pre-call prediction.
    """

    if client is None:
        return True
    members = getattr(client, "members", None)
    if isinstance(members, list) and members:
        support = [
            _sampling_controls_support_static(getattr(member, "client", None))
            for member in members
        ]
        return support[0] if support and all(item == support[0] for item in support) else None
    clients = getattr(client, "clients", None)
    if isinstance(clients, list) and clients:
        support = [_sampling_controls_support_static(child) for child in clients]
        return support[0] if support and all(item == support[0] for item in support) else None
    if _client_thinking_enabled(client):
        return False
    base_url = _client_base_url(client)
    model = _client_model(client).strip().lower()
    provider = provider_for_base_url(base_url)
    if provider is None:
        return None
    if not base_url_matches_provider(base_url, "openai"):
        return "reasoner" not in model
    if not model.startswith("gpt-5"):
        return True
    if model.startswith("gpt-5.1") or model.startswith("gpt-5.2"):
        return _client_reasoning_effort(client) in {"", "none"}
    return False


def _static_provider_sampling_metadata(
    client: Any,
    requested_temperature: Optional[float],
) -> dict[str, Any]:
    if requested_temperature is None:
        return {
            "temperature_sent": None,
            "temperature_provider_dropped": False,
            "temperature_provider_drop_reason": "",
        }
    support = _sampling_controls_support_static(client)
    if support is True:
        return {
            "temperature_sent": requested_temperature,
            "temperature_provider_dropped": False,
            "temperature_provider_drop_reason": "",
        }
    if support is False:
        return {
            "temperature_sent": None,
            "temperature_provider_dropped": True,
            "temperature_provider_drop_reason": "unsupported_sampling_controls",
        }
    return {
        "temperature_sent": None,
        "temperature_provider_dropped": False,
        "temperature_provider_drop_reason": "",
    }


def _work_type(record: Optional[Mapping[str, Any]]) -> str:
    if not isinstance(record, Mapping):
        return ""
    return str(record.get("work_type") or "").strip()


def _record_text(record: Optional[Mapping[str, Any]], *keys: str) -> str:
    if not isinstance(record, Mapping):
        return ""
    return " ".join(str(record.get(key) or "") for key in keys).strip().lower()


def resolve_mini_temperature(
    policy: Optional[MiniPhaseTemperatures],
    context: MiniTemperatureContext,
) -> MiniTemperatureDecision:
    """Resolve one effective LLM temperature for a mini prover call."""

    sample_temperature = _finite_temperature(context.sample_temperature)
    if policy is None or not bool(policy.enabled):
        return MiniTemperatureDecision(
            value=sample_temperature,
            phase_key="legacy_sample",
            source="parallel_sample" if sample_temperature is not None else "api_default",
            reason="phase_policy_disabled",
            sample_temperature=sample_temperature,
            api_default=sample_temperature is None,
        )

    phase_hint = str(context.phase_hint or "").strip()
    role = str(context.role or "").strip()
    action_id = str(context.action_id or "").strip()
    record = context.selected_work_item_record
    work_type = str(context.selected_work_type or _work_type(record)).strip()
    record_text = _record_text(
        record,
        "selection_reason",
        "work_type",
        "source",
        "mapped_action_id",
        "node_id",
    )

    if phase_hint == "planner":
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.planner),
            phase_key="planner",
            source="phase_default",
            reason="recursive_planner",
            sample_temperature=sample_temperature,
        )
    if bool(context.repair_turn_active) or bool(context.repair_self_check):
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.lean_repair),
            phase_key="lean_repair",
            source="phase_override",
            reason="repair_self_check_turn",
            sample_temperature=sample_temperature,
        )
    if bool(context.repair_ticket_active):
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.lean_repair),
            phase_key="lean_repair",
            source="phase_override",
            reason="selected_repair_ticket",
            sample_temperature=sample_temperature,
        )
    if (
        bool(context.formalization_helper_contract)
        or work_type in _FORMALIZATION_WORK_TYPES
        or work_type.startswith("formalize")
    ):
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.formalization_helper),
            phase_key="formalization_helper",
            source="phase_override",
            reason=work_type or "formalization_work",
            sample_temperature=sample_temperature,
        )
    if work_type == "assemble_route" or "route_assembly" in action_id:
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.route_assembly),
            phase_key="route_assembly",
            source="phase_override",
            reason="route_assembly",
            sample_temperature=sample_temperature,
        )
    near_stagnation_limit = (
        int(context.max_stagnation or 0) > 0
        and int(context.stagnation_counter or 0) >= int(context.max_stagnation or 0)
    )
    if (
        "stagnation" in record_text
        or phase_hint == "stagnation_escape"
        or near_stagnation_limit
        or bool(context.stagnation_escape)
    ):
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.stagnation_escape),
            phase_key="stagnation_escape",
            source="phase_default",
            reason="stagnation_escape",
            sample_temperature=sample_temperature,
        )
    if role == "refine":
        return MiniTemperatureDecision(
            value=_finite_temperature(policy.refine),
            phase_key="refine",
            source="phase_override",
            reason="refine_turn",
            sample_temperature=sample_temperature,
        )
    if sample_temperature is not None and bool(policy.use_sample_temperature_for_initial):
        return MiniTemperatureDecision(
            value=sample_temperature,
            phase_key="initial_proof",
            source="parallel_sample",
            reason="plain_initial_sample",
            sample_temperature=sample_temperature,
        )
    return MiniTemperatureDecision(
        value=_finite_temperature(policy.initial_proof),
        phase_key="initial_proof",
        source="phase_default",
        reason="plain_initial_default",
        sample_temperature=sample_temperature,
    )


def mini_temperature_metadata(
    decision: Optional[MiniTemperatureDecision],
    client: Any = None,
) -> dict[str, Any]:
    if decision is None:
        return {}
    return decision.metadata(client=client)


_MISSING_TEMPERATURE_ATTR = object()


def _json_safe_temperature_telemetry(value: Any) -> Any:
    if is_api_default_temperature_override(value):
        return None
    return value


def refresh_temperature_metadata_from_client(
    metadata: Mapping[str, Any],
    client: Any,
) -> dict[str, Any]:
    """Overlay post-call provider sampling telemetry onto phase metadata."""

    refreshed = dict(metadata or {})
    requested = getattr(
        client,
        "last_temperature_requested",
        _MISSING_TEMPERATURE_ATTR,
    )
    if requested is not _MISSING_TEMPERATURE_ATTR:
        requested = _json_safe_temperature_telemetry(requested)
        refreshed["temperature_requested"] = requested
    sent = getattr(client, "last_temperature_sent", _MISSING_TEMPERATURE_ATTR)
    if sent is not _MISSING_TEMPERATURE_ATTR:
        sent = _json_safe_temperature_telemetry(sent)
        refreshed["temperature_sent"] = sent
    dropped = getattr(
        client,
        "last_temperature_provider_dropped",
        _MISSING_TEMPERATURE_ATTR,
    )
    if dropped is not _MISSING_TEMPERATURE_ATTR:
        refreshed["temperature_provider_dropped"] = bool(dropped)
    drop_reason = getattr(
        client,
        "last_temperature_provider_drop_reason",
        _MISSING_TEMPERATURE_ATTR,
    )
    if drop_reason is not _MISSING_TEMPERATURE_ATTR:
        refreshed["temperature_provider_drop_reason"] = str(drop_reason or "")
    for attr, key, default in (
        ("last_reasoning_control_requested", "reasoning_control_requested", ""),
        ("last_reasoning_control_decision", "reasoning_control_decision", ""),
        ("last_reasoning_control_sent", "reasoning_control_sent", {}),
        ("last_reasoning_control_required", "reasoning_control_required", False),
        ("last_reasoning_capability_record", "reasoning_capability_record", {}),
    ):
        value = getattr(client, attr, _MISSING_TEMPERATURE_ATTR)
        if value is _MISSING_TEMPERATURE_ATTR:
            continue
        if isinstance(default, dict):
            refreshed[key] = dict(value or {})
        elif isinstance(default, bool):
            refreshed[key] = bool(value)
        else:
            refreshed[key] = str(value or "")
    return refreshed
