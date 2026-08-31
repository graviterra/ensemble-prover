"""Provider-specific tool-call protocol adapters.

The theorem-proving loops should stay model-agnostic.  This module contains
small compatibility shims for provider wire-format quirks that need to be
normalized before the rest of mini_prover sees them.
"""

from __future__ import annotations

import json
import re
import hashlib
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
from types import SimpleNamespace
from typing import Any, Dict, List, Mapping, Optional, Sequence

from .pricing import (
    OpenRouterReasoningCapabilities,
    base_url_matches_provider,
    ensure_openrouter_reasoning_capabilities_async,
    lookup_openrouter_reasoning_capabilities,
)
from .utils import parse_tool_arguments


DEEPSEEK_FINAL_RAW_NO_TOOLS_METRIC = "deepseek_final_raw_no_tools"
DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC = "deepseek_dsml_content_tool_call"
DEEPSEEK_DSML_TRY_LEAN_SALVAGED_METRIC = "deepseek_dsml_try_lean_salvaged"
DEEPSEEK_DSML_TOOL_AFTER_BUDGET_METRIC = "deepseek_dsml_tool_after_budget"
DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC = "deepseek_text_content_tool_call"
DEEPSEEK_TEXT_TRY_LEAN_SALVAGED_METRIC = "deepseek_text_try_lean_salvaged"
DEEPSEEK_TEXT_TOOL_AFTER_BUDGET_METRIC = "deepseek_text_tool_after_budget"
MINI_FINAL_ACCEPTED_PROOF_FALLBACK_METRIC = (
    "mini_final_no_tools_accepted_proof_fallbacks"
)
MINI_FINAL_EMPTY_OUTPUT_METRIC = "mini_final_no_tools_empty_outputs"
MINI_FINAL_TOKEN_EXHAUSTED_METRIC = "mini_final_no_tools_token_exhaustions"
MINI_FINAL_TRANSCRIPT_ECHO_METRIC = "mini_final_no_tools_transcript_echoes"
# Ordinary proof/refinement turns need enough model-side deliberation to use
# Lean feedback, but the setting must be explicit: provider defaults differ and
# may change independently of Mini's phase contract.  Finalization deliberately
# uses ``low`` elsewhere because it only has to serialize a proof candidate.
MINI_TOOL_REASONING_EFFORT = "medium"

# These are TOTAL provider completion envelopes.  Providers such as OpenAI
# and OpenRouter count hidden reasoning against the same value as visible
# output, so the graph-native values below are only safe when the concrete
# leaf is known not to consume hidden reasoning from that envelope.
_MINI_GRAPH_NATIVE_VISIBLE_OUTPUT_CAPS: Dict[str, int] = {
    "formalize_claim": 4096,
    "formalize_missing_obligation": 4096,
    "materialize_replay_source": 4096,
    "mine_missing_obligation": 4096,
    "prove_claim_variant": 6144,
    "route_replan": 4096,
    "target_integrity_adjudication": 2048,
}
_MINI_DEFAULT_TOTAL_OUTPUT_CAP = 20_480
_MINI_FINAL_VISIBLE_OUTPUT_FLOOR = 32_768
_MINI_GPT_REASONING_TOTAL_OUTPUT_CAP = 32_768
_MINI_QWEN_MANDATORY_REASONING_TOTAL_OUTPUT_CAP = 48_000
_MINI_DEEPSEEK_REASONING_TOTAL_OUTPUT_CAP = 96_000
_MINI_PLANNER_JSON_VISIBLE_FLOOR = 16_384
_MINI_PLANNER_REQUEST_KIND_VISIBLE_FLOORS: Dict[str, int] = {
    "planner_json": _MINI_PLANNER_JSON_VISIBLE_FLOOR,
    "planner_deliberation": _MINI_PLANNER_JSON_VISIBLE_FLOOR,
    "planner_reasoning_recovery": _MINI_PLANNER_JSON_VISIBLE_FLOOR,
    "planner_visibility_recovery": _MINI_PLANNER_JSON_VISIBLE_FLOOR,
}
_MINI_REQUEST_ENVELOPE_SCHEMA_VERSION = 2

_REASONING_EFFORT_RANK = {
    "minimal": 1,
    "low": 2,
    "medium": 3,
    "high": 4,
    "xhigh": 5,
    "max": 6,
}


class MiniReasoningCapabilityUnavailable(RuntimeError):
    """Retryable pre-dispatch failure to freeze a safe reasoning envelope."""

    mini_reasoning_capability_unavailable = True


def mini_reasoning_effort(client: Any, *, minimum: str) -> str:
    """Preserve an operator's configured effort while enforcing a phase floor.

    An explicit role-level off remains authoritative.  Otherwise Mini may ask
    for *more* reasoning for a demanding phase, but never silently asks for
    less than the role configuration.
    """

    cfg = getattr(client, "cfg", None)
    configured = str(getattr(cfg, "reasoning_effort", "") or "").strip().lower()
    floor = str(minimum or "").strip().lower()
    if configured == "none":
        return "none"
    if not configured:
        selected = floor
    elif not floor:
        selected = configured
    elif _REASONING_EFFORT_RANK.get(
        configured, 0
    ) >= _REASONING_EFFORT_RANK.get(floor, 0):
        selected = configured
    else:
        selected = floor
    model = str(getattr(cfg, "model", "") or "").strip().lower().rsplit("/", 1)[-1]
    base_url = str(getattr(cfg, "base_url", "") or "")
    if (
        selected == "max"
        and model.startswith("gpt-5.2")
        and (
            base_url_matches_provider(base_url, "openai")
            or base_url_matches_provider(base_url, "openrouter")
        )
    ):
        # GPT-5.2 names its strongest supported setting ``xhigh``.
        return "xhigh"
    return selected


def mini_model_output_capacity(client: Any, *, fallback: int = 8192) -> int:
    """Return the primary backend's advertised maximum output capacity."""

    cfg = getattr(client, "cfg", None)
    try:
        configured = int(getattr(cfg, "max_tokens", 0) or 0)
    except (TypeError, ValueError):
        configured = 0
    if configured > 0:
        return configured
    model = str(getattr(cfg, "model", "") or "").strip().lower().rsplit("/", 1)[-1]
    if model.startswith("deepseek-v4"):
        return 384_000
    if model.startswith("gpt-5.2"):
        return 128_000
    return max(1, int(fallback))

_DSML_INVOKE_RE = re.compile(
    r"<｜｜DSML｜｜invoke\b(?P<attrs>[^>]*)>(?P<body>.*?)</｜｜DSML｜｜invoke>",
    flags=re.DOTALL,
)
_DSML_PARAMETER_RE = re.compile(
    r"<｜｜DSML｜｜parameter\b(?P<attrs>[^>]*)>(?P<value>.*?)"
    r"</｜｜DSML｜｜parameter>",
    flags=re.DOTALL,
)
_DSML_ATTR_RE = re.compile(r'([A-Za-z_][A-Za-z0-9_-]*)="([^"]*)"')
_SIMPLE_XML_TOOL_CALL_RE = re.compile(
    r"(?ms)^[ \t]*<(?P<name>[A-Za-z_][A-Za-z0-9_]*)>[ \t]*\n?"
    r"(?P<body>.*?)^[ \t]*</(?P=name)>[ \t]*$"
)
_MINI_TEXT_TOOL_NAMES = frozenset(
    {
        "apply_decl_to_goal",
        "certify_counterexample",
        "check_lean",
        "compute_examples",
        "search_mathlib",
        "search_theorems",
        "try_lean",
        "try_skeleton",
    }
)
_MINI_TEXT_TOOL_BARE_ARGUMENT = {
    "apply_decl_to_goal": "decl_name",
    "certify_counterexample": "code",
    "check_lean": "code",
    "search_mathlib": "query",
    "search_theorems": "query",
    "try_lean": "code",
    "try_skeleton": "code",
}
_MINI_TEXT_TOOL_PROPERTIES = {
    "apply_decl_to_goal": frozenset({"statement", "decl_name"}),
    "certify_counterexample": frozenset({"code", "purpose"}),
    "check_lean": frozenset({"code"}),
    "compute_examples": frozenset({"queries", "mode", "purpose"}),
    "search_mathlib": frozenset({"query", "max_results"}),
    "search_theorems": frozenset({"query", "max_results"}),
    "try_lean": frozenset({"code", "purpose"}),
    "try_skeleton": frozenset({"code", "purpose"}),
}
_MINI_TEXT_TOOL_REQUIRED = {
    "apply_decl_to_goal": "decl_name",
    "certify_counterexample": "code",
    "check_lean": "code",
    "compute_examples": "queries",
    "search_mathlib": "query",
    "search_theorems": "query",
    "try_lean": "code",
    "try_skeleton": "code",
}
_MINI_TEXT_TOOL_ALIASES = {
    "apply_decl_to_goal": frozenset({"name"}),
    "compute_examples": frozenset({"query"}),
    "search_mathlib": frozenset({"limit"}),
    "search_theorems": frozenset({"limit"}),
}


def mini_visible_output_reasoning_effort(
    client: Any,
    *,
    default: str,
) -> str:
    """Resolve visible-output effort without sacrificing reasoning ability."""

    policy_factory = getattr(
        client,
        "mini_visible_output_reasoning_policy",
        None,
    )
    if callable(policy_factory):
        # Wrappers must resolve the phase floor against each concrete leaf;
        # using only the primary cfg can silently downgrade or disable a
        # fallback backend's configured reasoning.
        return policy_factory(default)
    return mini_reasoning_effort(client, minimum=default)


def mini_bounded_visible_output_reasoning_effort(
    client: Any,
    *,
    effort: str = "low",
) -> str:
    """Request a small reasoning phase while preserving configured-off mode.

    Tiny structured-output calls must reserve room for visible content.  They
    therefore cannot inherit an operator's high/max proof-search effort the
    way ordinary proof turns do.  Provider adapters remain authoritative for
    translating this phase request to their supported controls (for example,
    disabling DeepSeek reasoning when token budgets are not advertised).
    """

    cfg = getattr(client, "cfg", None)
    configured = str(
        getattr(cfg, "reasoning_effort", "") or ""
    ).strip().lower()
    if configured == "none":
        return "none"
    requested = str(effort or "low").strip().lower()
    return requested or "low"


@dataclass(frozen=True)
class MiniRequestEnvelopeReceipt:
    """Concrete-leaf resolution of one Mini completion request.

    The receipt is operational evidence for cost admission and transport.  It
    is deliberately not part of mathematical proof or certificate identity.
    """

    schema_version: int
    model: str
    base_url: str
    work_type: str
    request_kind: str
    effective_reasoning_effort: str
    reasoning_transport_mode: str
    max_output_tokens: int
    cap_source: str
    operator_override: bool
    reasoning_capability: Mapping[str, Any]
    reasoning_transport_control: Mapping[str, Any]
    digest: str

    def to_record(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "model": str(self.model),
            "base_url": str(self.base_url),
            "work_type": str(self.work_type),
            "request_kind": str(self.request_kind),
            "effective_reasoning_effort": str(
                self.effective_reasoning_effort
            ),
            "reasoning_transport_mode": str(self.reasoning_transport_mode),
            "max_output_tokens": int(self.max_output_tokens),
            "cap_source": str(self.cap_source),
            "operator_override": bool(self.operator_override),
            "reasoning_capability": dict(self.reasoning_capability or {}),
            "reasoning_transport_control": dict(
                self.reasoning_transport_control or {}
            ),
            "digest": str(self.digest),
        }


_MINI_REQUEST_ENVELOPE_RECEIPT: ContextVar[
    Optional[MiniRequestEnvelopeReceipt]
] = ContextVar("mini_request_envelope_receipt", default=None)


@contextmanager
def bind_mini_request_envelope_receipt(
    receipt: Optional[MiniRequestEnvelopeReceipt],
):
    """Bind one immutable receipt to exactly the current async request task."""

    token = _MINI_REQUEST_ENVELOPE_RECEIPT.set(receipt)
    try:
        yield
    finally:
        _MINI_REQUEST_ENVELOPE_RECEIPT.reset(token)


def current_mini_request_envelope_receipt() -> Optional[
    MiniRequestEnvelopeReceipt
]:
    return _MINI_REQUEST_ENVELOPE_RECEIPT.get()


def mini_request_envelope_receipt_is_valid_for(
    receipt: Any,
    client: Any,
    max_output_tokens: Any,
) -> bool:
    """Validate the frozen envelope before applying it to a leaf payload."""

    if not isinstance(receipt, MiniRequestEnvelopeReceipt):
        return False
    record = receipt.to_record()
    claimed_digest = str(record.pop("digest", "") or "")
    computed_digest = hashlib.sha256(
        json.dumps(
            record,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    cfg = getattr(client, "cfg", None)
    model = str(getattr(cfg, "model", "") or "").strip()
    base_url = str(
        getattr(client, "base_url", "")
        or getattr(cfg, "base_url", "")
        or ""
    ).strip()
    return bool(
        claimed_digest == computed_digest
        and receipt.schema_version == _MINI_REQUEST_ENVELOPE_SCHEMA_VERSION
        and receipt.model == model
        and receipt.base_url == base_url
        and int(receipt.max_output_tokens) == int(max_output_tokens or 0)
    )


@dataclass
class MiniRequestEnvelopePolicy:
    """Opaque request policy resolved independently for each concrete leaf."""

    work_type: str = ""
    request_kind: str = "tool_search"
    session_max_tokens_override: Optional[int] = None
    reasoning_mode: str = "floor"
    reasoning_effort: str = ""
    _receipts: Dict[tuple[Any, ...], MiniRequestEnvelopeReceipt] = field(
        default_factory=dict,
        init=False,
        repr=False,
        compare=False,
    )

    def for_request(
        self,
        *,
        request_kind: str,
        reasoning_mode: str,
        reasoning_effort: str,
    ) -> "MiniRequestEnvelopePolicy":
        return replace(
            self,
            request_kind=str(request_kind or "tool_search"),
            reasoning_mode=str(reasoning_mode or "floor"),
            reasoning_effort=str(reasoning_effort or ""),
        )

    def identity_record(self) -> Dict[str, Any]:
        return {
            "schema_version": _MINI_REQUEST_ENVELOPE_SCHEMA_VERSION,
            "work_type": str(self.work_type or ""),
            "request_kind": str(self.request_kind or ""),
            "session_max_tokens_override": _positive_int(
                self.session_max_tokens_override
            ),
            "reasoning_mode": str(self.reasoning_mode or ""),
            "reasoning_effort": str(self.reasoning_effort or ""),
        }

    async def resolve_for(self, client: Any) -> MiniRequestEnvelopeReceipt:
        cfg = getattr(client, "cfg", None)
        model = str(getattr(cfg, "model", "") or "").strip()
        base_url = str(
            getattr(client, "base_url", "")
            or getattr(cfg, "base_url", "")
            or ""
        ).strip()
        if self.reasoning_mode == "bounded":
            effective_effort = mini_bounded_visible_output_reasoning_effort(
                client,
                effort=self.reasoning_effort or "low",
            )
        else:
            effective_effort = mini_reasoning_effort(
                client,
                minimum=self.reasoning_effort,
            )
        # Mirror the direct DeepSeek adapter's required-off rule.  The caller
        # may carry a phase floor such as medium, but the concrete transport
        # still sends thinking=disabled when the role made that control
        # mandatory.
        if (
            base_url_matches_provider(base_url, "deepseek")
            and _mini_deepseek_v4_model(model)
            and not bool(getattr(cfg, "thinking_enabled", False))
            and bool(getattr(cfg, "reasoning_control_required", False))
        ):
            effective_effort = "none"
        # Include every config input used by cap resolution.  ``id(client)``
        # alone is not stable after a short-lived adapter is collected and
        # Python reuses its address within the same request policy.
        cache_key = (
            id(client),
            model,
            base_url,
            str(effective_effort or ""),
            _positive_int(getattr(cfg, "max_tokens", None)),
            _positive_int(
                getattr(cfg, "conversation_max_tokens_override", None)
            ),
            bool(getattr(cfg, "thinking_enabled", False)),
            bool(getattr(cfg, "reasoning_control_required", False)),
            _reasoning_requested_mode(cfg),
        )
        cached = self._receipts.get(cache_key)
        if cached is not None:
            return cached

        capability = None
        if base_url_matches_provider(base_url, "openrouter"):
            # This preflight happens while the request is still outside the
            # cost reservation.  The resulting receipt is reused when the
            # wrapper reaches this leaf, so admission and transport cannot
            # resolve different catalog states.
            if _mini_gpt_oss_120b_model(model):
                # GPT-OSS's provider contract is known independently of the
                # catalog: OpenRouter rejects reasoning-off, and Mini requires
                # at least high reasoning. Do not turn a catalog outage into a
                # proof-search outage for this statically supported route.
                capability = OpenRouterReasoningCapabilities(
                    supports_reasoning=True,
                    supports_max_tokens=False,
                    supports_disable=False,
                    supported_efforts=("high", "max"),
                    default_enabled=True,
                    mandatory=True,
                    source="static_gpt_oss_contract",
                )
            elif (
                mini_openrouter_deepseek_v4_explicit_enable_model(model)
                and not _strict_reasoning_off(cfg)
            ):
                # A fresh catalog record, including an explicit negative,
                # remains authoritative. With no record, exact allowlisted
                # routes use the generic-enable contract without blocking
                # every proof turn on optional catalog infrastructure.
                capability = lookup_openrouter_reasoning_capabilities(
                    base_url,
                    model,
                )
                if capability is None:
                    capability = _static_openrouter_deepseek_v4_capability(model)
            else:
                try:
                    capability = (
                        await ensure_openrouter_reasoning_capabilities_async(
                            base_url,
                            model,
                        )
                    )
                except Exception as exc:
                    # Dated DeepSeek v4 snapshots are not on the exact
                    # explicit-enable allowlist. Visibility recovery still
                    # re-resolves the Policy at invoke after
                    # ``_resolve_planner_output_tokens`` already swallowed this
                    # same outage, so raising here kills the HTTP call that
                    # was supposed to recover a reasoning-only flash miss.
                    family_capability = (
                        _static_openrouter_deepseek_v4_family_capability(model)
                    )
                    if family_capability is not None:
                        capability = family_capability
                    else:
                        # A catalog outage leaves both the reasoning transport
                        # and its shared output envelope unknown. Some routes
                        # consume hidden reasoning even when the request looks
                        # optional, so silently applying a visible-output cap
                        # can erase the final answer. Yield before cost
                        # reservation/transport and retry when a capability
                        # receipt is available.
                        raise MiniReasoningCapabilityUnavailable(
                            "OpenRouter reasoning capability is temporarily "
                            f"unavailable for model={model}"
                        ) from exc
        capability_record = (
            capability.to_record() if capability is not None else {}
        )
        output_tokens, cap_source, transport_mode, operator_override = (
            _resolve_mini_leaf_output_cap(
                cfg=cfg,
                model=model,
                base_url=base_url,
                work_type=self.work_type,
                request_kind=self.request_kind,
                effective_effort=str(effective_effort or ""),
                session_override=self.session_max_tokens_override,
                capability=capability,
            )
        )
        effective_effort, reasoning_transport_control = (
            _resolve_mini_reasoning_transport_control(
                cfg=cfg,
                model=model,
                base_url=base_url,
                effective_effort=str(effective_effort or ""),
                transport_mode=transport_mode,
                output_tokens=output_tokens,
                capability=capability,
            )
        )
        body = {
            "schema_version": _MINI_REQUEST_ENVELOPE_SCHEMA_VERSION,
            "model": model,
            "base_url": base_url,
            "work_type": str(self.work_type or ""),
            "request_kind": str(self.request_kind or ""),
            "effective_reasoning_effort": str(effective_effort or ""),
            "reasoning_transport_mode": transport_mode,
            "max_output_tokens": int(output_tokens),
            "cap_source": cap_source,
            "operator_override": bool(operator_override),
            "reasoning_capability": capability_record,
            "reasoning_transport_control": reasoning_transport_control,
        }
        digest = hashlib.sha256(
            json.dumps(
                body,
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        receipt = MiniRequestEnvelopeReceipt(**body, digest=digest)
        self._receipts[cache_key] = receipt
        return receipt


def _mini_deepseek_v4_model(model: str) -> bool:
    return str(model or "").strip().lower().rsplit("/", 1)[-1].startswith(
        "deepseek-v4-"
    )


_MINI_OPENROUTER_DEEPSEEK_V4_EXPLICIT_ENABLE_MODELS = frozenset(
    {
        "deepseek/deepseek-v4-pro",
        "deepseek/deepseek-v4-pro-0813",
        "~deepseek/deepseek-v4-flash-latest",
    }
)


def mini_openrouter_deepseek_v4_explicit_enable_model(model: str) -> bool:
    """Return models with a stable generic OpenRouter reasoning-on control.

    OpenRouter catalog rows can temporarily omit effort and default-enabled
    metadata for newly versioned DeepSeek routes.  That omission is not a
    negative capability statement: these concrete routes accept the generic
    ``reasoning.enabled=true`` transport.
    """

    name = str(model or "").strip().lower()
    return name in _MINI_OPENROUTER_DEEPSEEK_V4_EXPLICIT_ENABLE_MODELS


def _static_openrouter_deepseek_v4_family_capability(
    model: str,
) -> Optional[OpenRouterReasoningCapabilities]:
    """Return the outage-safe DeepSeek v4 contract for any dated snapshot."""

    if not _mini_deepseek_v4_model(model):
        return None
    return OpenRouterReasoningCapabilities(
        supports_reasoning=True,
        supports_max_tokens=False,
        supports_disable=False,
        supported_efforts=(),
        default_enabled=None,
        mandatory=False,
        source="static_deepseek_v4_family_contract",
    )


def _static_openrouter_deepseek_v4_capability(
    model: str,
) -> Optional[OpenRouterReasoningCapabilities]:
    """Return the outage-safe contract for an exact supported DeepSeek route."""

    if not mini_openrouter_deepseek_v4_explicit_enable_model(model):
        return None
    capability = _static_openrouter_deepseek_v4_family_capability(model)
    if capability is None:
        return None
    return replace(
        capability,
        source="static_deepseek_v4_contract",
    )


def _provider_default_reasoning_requested(cfg: Any) -> bool:
    return _reasoning_requested_mode(cfg) in {"provider-default", "auto"}


def _reasoning_requested_mode(cfg: Any) -> str:
    raw_mode = getattr(cfg, "reasoning_requested_mode", None)
    mode = str(raw_mode or "").strip().lower()
    configured_effort = str(
        getattr(cfg, "reasoning_effort", "") or ""
    ).strip().lower()
    if mode in {"provider-default", "auto"}:
        requested_effort = str(
            getattr(cfg, "reasoning_requested_effort", "") or ""
        ).strip().lower()
        if not requested_effort and bool(
            getattr(cfg, "reasoning_control_required", False)
        ) and not hasattr(cfg, "reasoning_requested_effort"):
            # Programmatic/YAML callers may carry the older required+effort
            # representation without the CLI's explicit-effort stamp.
            requested_effort = configured_effort
        if requested_effort == "none":
            return "off"
        if requested_effort:
            return "on"
        return mode
    if mode:
        return mode
    if configured_effort == "none":
        return "off"
    if configured_effort:
        return "on"
    # Programmatic RoleConfig callers predate the CLI request-mode stamp.
    # With neither an explicit required control nor a requested role effort,
    # their intent is provider-default, not an implicit disable.
    return "provider-default"


def _mini_gpt_oss_120b_model(model: str) -> bool:
    name = str(model or "").strip().lower().rsplit("/", 1)[-1]
    return name.startswith("gpt-oss-120b")


def _mini_openrouter_mandatory_model(model: str) -> bool:
    name = str(model or "").strip().lower().rsplit("/", 1)[-1]
    return name.startswith("qwen3.8-max") or _mini_gpt_oss_120b_model(model)


def _positive_int(value: Any) -> int:
    try:
        parsed = int(value or 0)
    except (TypeError, ValueError):
        return 0
    return parsed if parsed > 0 else 0


def _resolve_mini_leaf_output_cap(
    *,
    cfg: Any,
    model: str,
    base_url: str,
    work_type: str,
    request_kind: str,
    effective_effort: str,
    session_override: Optional[int],
    capability: Any,
) -> tuple[int, str, str, bool]:
    session_cap = _positive_int(session_override)
    role_cap = _positive_int(
        getattr(cfg, "conversation_max_tokens_override", None)
    )
    explicit_cap = session_cap or role_cap
    effort = str(effective_effort or "").strip().lower()
    reasoning_on = effort not in {"", "none"}
    transport_mode = "enabled" if reasoning_on else "disabled"
    mandatory = False

    if base_url_matches_provider(base_url, "openrouter"):
        mandatory = bool(
            (capability is not None and capability.mandatory is True)
            or _mini_openrouter_mandatory_model(model)
        )
        if _mini_deepseek_v4_model(model):
            supports_budget = bool(
                capability is not None and capability.supports_max_tokens
            )
            supports_disable = bool(
                capability is not None and capability.supports_disable
            )
            if _provider_default_reasoning_requested(cfg):
                # Provider-default/auto omits the reasoning control. Reserve
                # headroom for provider-side hidden reasoning without turning
                # Mini's phase effort floor into an explicit disable request.
                reasoning_on = True
                transport_mode = "provider_default"
            elif mandatory:
                reasoning_on = True
                transport_mode = "mandatory"
            elif effort == "none":
                reasoning_on = mandatory or not supports_disable
                transport_mode = (
                    "mandatory" if mandatory else (
                        "unbounded_default" if reasoning_on else "disabled"
                    )
                )
            elif supports_budget:
                reasoning_on = True
                transport_mode = "bounded"
            elif _reasoning_requested_mode(cfg) == "on":
                selected, _relation = _advertised_reasoning_effort_resolution(
                    effort,
                    capability,
                )
                if selected:
                    reasoning_on = True
                    transport_mode = "advertised_effort"
                elif capability is not None and (
                    capability.default_enabled is True
                    or capability.mandatory is True
                ):
                    reasoning_on = True
                    transport_mode = "enabled_unbounded"
                elif (
                    capability is None or capability.supports_reasoning is True
                ) and mini_openrouter_deepseek_v4_explicit_enable_model(model):
                    reasoning_on = True
                    transport_mode = "enabled_unbounded"
                elif _strict_reasoning_on(cfg):
                    raise RuntimeError(
                        "explicit reasoning-on has no advertised enabling "
                        f"transport for OpenRouter model={model}"
                    )
                elif supports_disable:
                    reasoning_on = False
                    transport_mode = "disabled_without_budget"
                else:
                    reasoning_on = True
                    transport_mode = "unbounded_default"
            elif supports_disable:
                # This is exactly what models._apply_reasoning_effort sends
                # for low/medium on routes without a legal token budget.
                reasoning_on = False
                transport_mode = "disabled_without_budget"
            else:
                reasoning_on = True
                transport_mode = "mandatory" if mandatory else "unbounded_default"
        elif mandatory:
            reasoning_on = True
            transport_mode = "mandatory"
    elif base_url_matches_provider(base_url, "deepseek") and _mini_deepseek_v4_model(
        model
    ):
        reasoning_on = effort != "none"
        transport_mode = "enabled" if reasoning_on else "disabled"

    if explicit_cap > 0:
        # Existing operator semantics are an exact request override, not a
        # role-capacity clamp: operators may deliberately raise or lower it.
        return explicit_cap, "operator_override", transport_mode, True

    leaf_name = model.lower().rsplit("/", 1)[-1]
    if _mini_deepseek_v4_model(model) and reasoning_on:
        automatic_cap = _MINI_DEEPSEEK_REASONING_TOTAL_OUTPUT_CAP
        cap_source = "deepseek_reasoning_headroom"
    elif mandatory and reasoning_on:
        automatic_cap = _MINI_QWEN_MANDATORY_REASONING_TOTAL_OUTPUT_CAP
        cap_source = "mandatory_reasoning_headroom"
    elif (
        base_url_matches_provider(base_url, "openrouter")
        and reasoning_on
        and capability is not None
        and capability.supports_reasoning
    ):
        automatic_cap = _MINI_GPT_REASONING_TOTAL_OUTPUT_CAP
        cap_source = "catalog_reasoning_headroom"
    elif leaf_name.startswith("gpt-5") and reasoning_on:
        automatic_cap = _MINI_GPT_REASONING_TOTAL_OUTPUT_CAP
        cap_source = "hidden_reasoning_headroom"
    else:
        automatic_cap = _MINI_GRAPH_NATIVE_VISIBLE_OUTPUT_CAPS.get(
            str(work_type or ""),
            _MINI_DEFAULT_TOTAL_OUTPUT_CAP,
        )
        cap_source = "graph_visible_output" if str(work_type or "") in (
            _MINI_GRAPH_NATIVE_VISIBLE_OUTPUT_CAPS
        ) else "bounded_default"
    if str(request_kind or "") == "final_no_tools":
        automatic_cap = max(automatic_cap, _MINI_FINAL_VISIBLE_OUTPUT_FLOOR)
        cap_source = f"{cap_source}+final_visible_floor"
    planner_visible_floor = _MINI_PLANNER_REQUEST_KIND_VISIBLE_FLOORS.get(
        str(request_kind or "")
    )
    if planner_visible_floor:
        automatic_cap = max(automatic_cap, int(planner_visible_floor))
        cap_source = f"{cap_source}+{request_kind}_visible_floor"
    capacity = _positive_int(getattr(cfg, "max_tokens", None))
    if capacity > 0:
        if (
            leaf_name.startswith("gpt-5.6")
            and planner_visible_floor
        ):
            # GPT-5.6 planner stages receive the role's full advertised model
            # output capacity.  This is independent of the reasoning setting:
            # disabling reasoning must not quietly reinstate an 8K/16K
            # harness-side truncation boundary on the visible plan.
            automatic_cap = capacity
            cap_source = "model_output_capacity"
        else:
            automatic_cap = min(automatic_cap, capacity)
    return max(1, int(automatic_cap)), cap_source, transport_mode, False


def _minimum_advertised_reasoning_effort(
    capability: Any,
    *,
    model: str = "",
) -> str:
    advertised = tuple(
        str(item or "").strip().lower()
        for item in (
            getattr(capability, "supported_efforts", ())
            if capability is not None
            else ()
        )
        if str(item or "").strip().lower() != "none"
    )
    if _mini_gpt_oss_120b_model(model):
        # OpenRouter rejects reasoning-off for GPT-OSS, and proof-search
        # quality requires the high lane. Catalog effort lists have been
        # incomplete in live runs, so never silently downgrade this model.
        return "high"
    preference = (
        "minimal",
        "low",
        "medium",
        "high",
        "max",
        "xhigh",
    )
    return next(
        (
            effort
            for effort in preference
            if effort in advertised
        ),
        "low",
    )


def _advertised_reasoning_effort_resolution(
    requested: str,
    capability: Any,
) -> tuple[str, str]:
    """Resolve an explicit-on effort against the live advertised vocabulary.

    Providers do not share a total effort vocabulary (notably, DeepSeek V4
    currently advertises ``high``/``xhigh`` while Mini also accepts ``max``).
    A strict request may use an explicitly advertised nearest setting, but it
    may never turn reasoning off.  The relation is returned for audit logs.
    """

    clean_requested = str(requested or "medium").strip().lower() or "medium"
    advertised = tuple(
        dict.fromkeys(
            str(item or "").strip().lower()
            for item in (
                getattr(capability, "supported_efforts", ())
                if capability is not None
                else ()
            )
            if str(item or "").strip().lower() not in {"", "none"}
        )
    )
    if clean_requested in advertised:
        return clean_requested, "exact"
    requested_rank = _REASONING_EFFORT_RANK.get(clean_requested, 0)
    ranked = sorted(
        (
            (_REASONING_EFFORT_RANK.get(item, 0), index, item)
            for index, item in enumerate(advertised)
            if _REASONING_EFFORT_RANK.get(item, 0) > 0
        ),
        key=lambda entry: (entry[0], entry[1]),
    )
    if not ranked:
        return "", "unavailable"
    not_stronger = [entry for entry in ranked if entry[0] <= requested_rank]
    if not_stronger:
        selected = not_stronger[-1][2]
        return selected, "downgraded"
    selected = ranked[0][2]
    return selected, "upgraded_to_provider_minimum"


def _strict_reasoning_on(cfg: Any) -> bool:
    raw_mode = str(
        getattr(cfg, "reasoning_requested_mode", "") or ""
    ).strip().lower()
    return raw_mode == "on" or bool(
        getattr(cfg, "reasoning_control_required", False)
    ) and _reasoning_requested_mode(cfg) == "on"


def _strict_reasoning_off(cfg: Any) -> bool:
    raw_mode = str(
        getattr(cfg, "reasoning_requested_mode", "") or ""
    ).strip().lower()
    return raw_mode == "off" or bool(
        getattr(cfg, "reasoning_control_required", False)
    ) and _reasoning_requested_mode(cfg) == "off"


def _resolve_mini_reasoning_transport_control(
    *,
    cfg: Any,
    model: str,
    base_url: str,
    effective_effort: str,
    transport_mode: str,
    output_tokens: int,
    capability: Any,
) -> tuple[str, Dict[str, Any]]:
    """Freeze the exact OpenRouter control used by the concrete request.

    Capability discovery must happen once, before cost admission.  Returning
    the provider payload here prevents a later catalog lookup from changing a
    disabled 4K request into an unbounded reasoning request after reservation.
    """

    effort = str(effective_effort or "").strip().lower()
    if not base_url_matches_provider(base_url, "openrouter"):
        return effort, {}
    if _mini_deepseek_v4_model(model):
        if transport_mode == "provider_default":
            return "", {}
        if transport_mode in {"disabled", "disabled_without_budget"}:
            return "none", {"reasoning": {"enabled": False}}
        if transport_mode == "bounded":
            if output_tokens <= 1 and _strict_reasoning_on(cfg):
                raise RuntimeError(
                    "explicit reasoning-on request needs at least two total "
                    f"output tokens for OpenRouter model={model}"
                )
            fraction, ceiling = {
                "minimal": (0.10, 512),
                "low": (0.20, 1024),
                "medium": (0.50, 4096),
                "high": (0.80, 8192),
                "max": (0.95, 16384),
                "xhigh": (0.95, 16384),
            }.get(effort, (0.50, 4096))
            budget = max(1, min(ceiling, int(output_tokens * fraction)))
            budget = min(budget, max(1, int(output_tokens) - 1))
            return effort or "medium", {"reasoning": {"max_tokens": budget}}
        if transport_mode in {"mandatory", "advertised_effort"}:
            if transport_mode == "mandatory" and _strict_reasoning_on(cfg):
                selected, _relation = _advertised_reasoning_effort_resolution(
                    effort,
                    capability,
                )
                if selected:
                    return selected, {"reasoning": {"effort": selected}}
                return effort or "medium", {"reasoning": {"enabled": True}}
            if transport_mode == "advertised_effort":
                selected, relation = _advertised_reasoning_effort_resolution(
                    effort,
                    capability,
                )
                if not selected:
                    raise RuntimeError(
                        "explicit reasoning-on has no advertised effort control "
                        f"for OpenRouter model={model}"
                    )
                del relation
                return selected, {"reasoning": {"effort": selected}}
            selected = _minimum_advertised_reasoning_effort(
                capability,
                model=model,
            )
            return selected, {"reasoning": {"effort": selected}}
        if transport_mode == "enabled_unbounded":
            return effort or "medium", {"reasoning": {"enabled": True}}
        if transport_mode == "unbounded_default" and effort in {"", "none"}:
            # Visibility recovery asks for none. The static DeepSeek v4
            # contract omits disable/max_tokens; raising here discarded
            # 45 minutes of Putnam 1978 A2 flash reasoning
            # (20260818_215944) before the visibility HTTP call.
            if bool(getattr(cfg, "reasoning_control_required", False)):
                return "none", {"reasoning": {"enabled": False}}
            return effort, {}
        if bool(getattr(cfg, "reasoning_control_required", False)):
            raise RuntimeError(
                "required bounded reasoning control is not advertised for "
                f"OpenRouter model={model}"
            )
        return effort, {}
    if transport_mode == "mandatory" and _strict_reasoning_on(cfg):
        selected, _relation = _advertised_reasoning_effort_resolution(
            effort,
            capability,
        )
        if selected:
            return selected, {"reasoning": {"effort": selected}}
        return effort, {"reasoning": {"enabled": True}}
    if transport_mode == "mandatory":
        selected = _minimum_advertised_reasoning_effort(
            capability,
            model=model,
        )
        return selected, {"reasoning": {"effort": selected}}
    if effort in {"", "none"}:
        return "none", {"reasoning": {"enabled": False}}
    if _strict_reasoning_on(cfg):
        selected, _relation = _advertised_reasoning_effort_resolution(
            effort,
            capability,
        )
        if selected:
            return selected, {"reasoning": {"effort": selected}}
        if capability is not None and (
            capability.default_enabled is True or capability.mandatory is True
        ):
            return effort, {"reasoning": {"enabled": True}}
        raise RuntimeError(
            "explicit reasoning-on has no advertised enabling transport for "
            f"OpenRouter model={model}"
        )
    return effort, {"reasoning": {"effort": effort}}


async def preflight_mini_reasoning_contract(
    client: Any,
    *,
    role: str = "llm",
) -> List[Dict[str, Any]]:
    """Prove explicit reasoning controls are satisfiable before search starts.

    The CLI stamps ``reasoning_requested_mode`` on each role config.  For an
    explicit ``on`` request every concrete wrapper leaf is capability-checked
    before any proof action or provider dispatch.  Provider-default and off
    retain their existing semantics.
    """

    records: List[Dict[str, Any]] = []
    for leaf, inherited_cfg in mini_request_concrete_leaf_bindings(client):
        cfg = getattr(leaf, "cfg", None) or inherited_cfg
        mode = _reasoning_requested_mode(cfg)
        requested = str(
            getattr(cfg, "reasoning_effort", "") or ""
        ).strip().lower()
        model = str(getattr(cfg, "model", "") or "").strip()
        base_url = str(
            getattr(leaf, "base_url", "")
            or getattr(cfg, "base_url", "")
            or ""
        ).strip()
        record: Dict[str, Any] = {
            "role": str(role or "llm"),
            "model": model,
            "base_url": base_url,
            "requested_mode": mode,
            "requested_effort": requested,
            "effective_effort": requested,
            "resolution": "not_required",
            "transport_mode": "provider_default",
        }
        if not _strict_reasoning_on(cfg):
            records.append(record)
            continue
        if requested in {"", "none"}:
            raise RuntimeError(
                f"explicit reasoning-on requires a positive effort for {role}"
            )
        if base_url_matches_provider(base_url, "openrouter"):
            # Resolve a representative concrete request through the exact same
            # leaf envelope algorithm used before cost reservation and send.
            # A parallel hand-written capability tree previously accepted
            # generic ``supports_max_tokens`` routes that the transport could
            # not encode, making startup preflight pass and first dispatch
            # fail.  The receipt is the executable contract.
            policy = mini_request_envelope_policy(
                work_type="formalize_claim"
            ).for_request(
                request_kind="tool_search",
                reasoning_mode="floor",
                reasoning_effort=requested,
            )
            try:
                receipt = await policy.resolve_for(leaf)
            except MiniReasoningCapabilityUnavailable:
                # Catalog transport is optional startup infrastructure. Keep
                # this typed, retryable admission result intact so the CLI can
                # enter MiniSession and let its durable zero-provider backoff
                # lane retry; only a proven capability incompatibility should
                # reject configuration before search starts.
                raise
            except RuntimeError as exc:
                raise RuntimeError(
                    "explicit reasoning-on capability preflight unavailable "
                    f"for {role} OpenRouter model={model}: {exc}"
                ) from exc
            control = dict(receipt.reasoning_transport_control or {}).get(
                "reasoning"
            )
            if isinstance(control, Mapping) and control.get("enabled") is False:
                raise RuntimeError(
                    "explicit reasoning-on preflight resolved to disabled "
                    f"transport for {role} OpenRouter model={model}"
                )
            record["capability"] = dict(receipt.reasoning_capability or {})
            record["effective_effort"] = str(
                receipt.effective_reasoning_effort or requested
            )
            record["transport_mode"] = str(
                receipt.reasoning_transport_mode or ""
            )
            _selected, relation = _advertised_reasoning_effort_resolution(
                requested,
                SimpleNamespace(
                    supported_efforts=tuple(
                        record["capability"].get("supported_efforts") or ()
                    )
                ),
            )
            record["resolution"] = (
                "exact_bounded"
                if record["transport_mode"] == "bounded"
                else relation
                if _selected
                else "provider_enabled_without_effort_label"
            )
            record["request_envelope_digest"] = receipt.digest
        else:
            record["resolution"] = "direct_provider_explicit"
            record["transport_mode"] = "enabled"
        try:
            setattr(cfg, "reasoning_preflight_record", dict(record))
        except Exception:
            pass
        records.append(record)
    return records


def mini_request_envelope_policy(
    *,
    work_type: str,
    session_max_tokens_override: Optional[int] = None,
) -> MiniRequestEnvelopePolicy:
    """Create an unresolved policy; no wrapper configuration is inspected."""

    return MiniRequestEnvelopePolicy(
        work_type=str(work_type or ""),
        session_max_tokens_override=(
            _positive_int(session_max_tokens_override) or None
        ),
    )


async def resolve_mini_request_output_tokens(
    client: Any,
    value: Any,
) -> tuple[Any, Optional[MiniRequestEnvelopeReceipt]]:
    """Resolve an opaque Mini policy for exactly one concrete client leaf."""

    if not isinstance(value, MiniRequestEnvelopePolicy):
        return value, None
    receipt = await value.resolve_for(client)
    return int(receipt.max_output_tokens), receipt


def mini_request_wrapper_children(client: Any) -> List[Any]:
    """Return one wrapper layer in deterministic dispatch order."""

    members = getattr(client, "members", None)
    if isinstance(members, list) and members:
        return [getattr(member, "client", member) for member in members]
    clients = getattr(client, "clients", None)
    if isinstance(clients, list) and clients:
        return list(clients)
    return []


def mini_request_concrete_leaf_bindings(client: Any) -> List[tuple[Any, Any]]:
    """Return concrete leaves with wrapper-supplied cfg fallbacks."""

    leaves: List[tuple[Any, Any]] = []
    active: set[int] = set()

    def visit(node: Any, inherited_cfg: Any = None) -> None:
        node_id = id(node)
        if node_id in active:
            raise RuntimeError("model wrapper cycle in Mini request envelope")
        members = getattr(node, "members", None)
        clients = getattr(node, "clients", None)
        if not (isinstance(members, list) and members) and not (
            isinstance(clients, list) and clients
        ):
            leaves.append((node, getattr(node, "cfg", None) or inherited_cfg))
            return
        active.add(node_id)
        try:
            if isinstance(members, list) and members:
                for member in members:
                    child = getattr(member, "client", member)
                    visit(
                        child,
                        getattr(member, "cfg", None)
                        or getattr(child, "cfg", None)
                        or inherited_cfg,
                    )
            else:
                for child in clients:
                    visit(
                        child,
                        getattr(child, "cfg", None) or inherited_cfg,
                    )
        finally:
            active.remove(node_id)

    visit(client)
    return leaves


def mini_request_concrete_leaves(client: Any) -> List[Any]:
    """Recursively enumerate concrete leaves, rejecting wrapper cycles."""

    return [leaf for leaf, _cfg in mini_request_concrete_leaf_bindings(client)]


async def resolve_mini_request_envelopes(
    client: Any,
    value: Any,
) -> List[MiniRequestEnvelopeReceipt]:
    """Resolve one request against all concrete leaves before admission."""

    if not isinstance(value, MiniRequestEnvelopePolicy):
        return []
    receipts: List[MiniRequestEnvelopeReceipt] = []
    for leaf in mini_request_concrete_leaves(client):
        receipts.append(await value.resolve_for(leaf))
    return receipts


@dataclass(frozen=True)
class DSMLAfterBudgetHandling:
    """Result of handling DeepSeek tool syntax emitted after tools are unavailable."""

    content: str
    event: str = ""
    original_content: str = ""
    content_metric_key: str = ""
    metric_key: str = ""
    feedback: str = ""
    salvaged_code: str = ""

    @property
    def changed(self) -> bool:
        return bool(self.event)

    @property
    def should_reprompt(self) -> bool:
        return bool(self.feedback)


@dataclass(frozen=True)
class FinalNoToolsResolution:
    """Bounded finalizer contract after tools become unavailable.

    Provider reasoning is telemetry, never proof evidence.  A current-turn
    Lean-accepted scratch proof is the only deterministic fallback when the
    provider emits reasoning-only or token-truncated final output.
    """

    content: str
    event: str = ""
    error: str = ""
    finish_reason: str = ""
    reasoning_content_chars: int = 0
    used_accepted_proof: bool = False
    metric_key: str = ""


def _raw_finish_reason(payload: Any, client: Any) -> str:
    if isinstance(payload, dict):
        choices = payload.get("choices")
        if isinstance(choices, list) and choices and isinstance(choices[0], dict):
            value = str(choices[0].get("finish_reason", "") or "").strip()
            if value:
                return value
    if bool(getattr(client, "last_truncated", False)):
        return "length"
    return ""


def _raw_reasoning_content_chars(payload: Any) -> int:
    if not isinstance(payload, dict):
        return 0
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
        return 0
    message = choices[0].get("message")
    if not isinstance(message, dict):
        return 0
    seen: set[str] = set()
    parts: List[str] = []
    for key in ("reasoning_content", "reasoning"):
        value = message.get(key)
        if isinstance(value, str):
            text = value.strip()
        elif isinstance(value, dict):
            text = str(
                value.get("text")
                or value.get("content")
                or value.get("summary")
                or ""
            ).strip()
        elif isinstance(value, list):
            text = "\n".join(
                str(
                    item.get("text")
                    or item.get("content")
                    or item.get("summary")
                    or ""
                ).strip()
                if isinstance(item, dict)
                else str(item or "").strip()
                for item in value
            ).strip()
        else:
            text = ""
        if not text or text in seen:
            continue
        for previous in parts:
            prefix = previous + "\n"
            if text.startswith(prefix):
                text = text[len(prefix) :].lstrip()
                break
        if text:
            seen.add(text)
            parts.append(text)
    return len("\n".join(parts))


def _looks_like_final_no_tools_transcript_echo(content: str) -> bool:
    """Recognize model-authored pseudo transcripts at a proof boundary.

    A final serializer must emit a proof artifact, not replay prior assistant
    reasoning and fabricated tool traffic.  Require multiple independent
    transcript markers so ordinary mathematical prose mentioning a tool does
    not trip this guard.
    """

    text = str(content or "")
    if "<response>" not in text:
        return False
    tool_result_markers = text.count("<tool_result>") + text.count(
        "Tool result ("
    )
    return bool(
        tool_result_markers >= 2
        and (
            "<tool_request>" in text
            or text.count("```") >= 4
            or "</response>" not in text
        )
    )


def resolve_final_no_tools_output(
    *,
    content: Any,
    raw_response: Any = None,
    client: Any = None,
    accepted_proof_codes: Sequence[str] = (),
) -> FinalNoToolsResolution:
    """Resolve one final no-tools response without another provider retry."""

    text = str(content or "")
    finish_reason = _raw_finish_reason(raw_response, client)
    reasoning_chars = _raw_reasoning_content_chars(raw_response)
    truncated = finish_reason == "length"
    missing = not text.strip()
    accepted = ""
    for raw_code in reversed(list(accepted_proof_codes or ())):
        candidate = _checked_code_body(raw_code)
        if not candidate:
            continue
        # Fail closed on the same explicit proof-term forms accepted by the
        # ordinary active-goal ``try_lean`` boundary.  A declaration denylist
        # is insufficient here: Lean declarations may carry modifiers
        # (``private lemma``) and have many forms (``def``, ``instance``, ...).
        # Declaration-required and target-integrity checks are valid formal
        # artifacts, but they are not proof bodies for this active goal.
        if re.match(
            r"^\s*(?:by|show|calc|exact|refine|fun)(?![\w'])",
            candidate,
        ) is None:
            continue
        accepted = candidate
        break
    if _looks_like_final_no_tools_transcript_echo(text):
        if accepted:
            return FinalNoToolsResolution(
                content=_fenced_lean(accepted),
                event="final_no_tools_accepted_proof_fallback",
                finish_reason=finish_reason,
                reasoning_content_chars=reasoning_chars,
                used_accepted_proof=True,
                metric_key=MINI_FINAL_ACCEPTED_PROOF_FALLBACK_METRIC,
            )
        # Explicitly tagged Lean is a high-confidence candidate, even when a
        # provider wrapped it in a malformed transcript.  Preserve exactly one
        # such candidate for the ordinary kernel gate; never promote generic
        # reasoning fences or choose among ambiguous explicit submissions.
        explicit_lean = re.findall(
            r"```(?:lean|lean4)\s*\n(.*?)```",
            text,
            flags=re.IGNORECASE | re.DOTALL,
        )
        if len(explicit_lean) == 1 and str(explicit_lean[0] or "").strip():
            return FinalNoToolsResolution(
                content=_fenced_lean(explicit_lean[0]),
                event="final_no_tools_transcript_echo_lean_salvaged",
                finish_reason=finish_reason,
                reasoning_content_chars=reasoning_chars,
            )
        return FinalNoToolsResolution(
            content="",
            event="final_no_tools_transcript_echo",
            error="final_no_tools_transcript_echo",
            finish_reason=finish_reason,
            reasoning_content_chars=reasoning_chars,
            metric_key=MINI_FINAL_TRANSCRIPT_ECHO_METRIC,
        )
    if not (truncated or missing):
        return FinalNoToolsResolution(
            content=text,
            finish_reason=finish_reason,
            reasoning_content_chars=reasoning_chars,
        )
    if accepted:
        return FinalNoToolsResolution(
            content=_fenced_lean(accepted),
            event="final_no_tools_accepted_proof_fallback",
            finish_reason=finish_reason,
            reasoning_content_chars=reasoning_chars,
            used_accepted_proof=True,
            metric_key=MINI_FINAL_ACCEPTED_PROOF_FALLBACK_METRIC,
        )
    if truncated:
        return FinalNoToolsResolution(
            content="",
            event="final_no_tools_token_exhausted",
            error="final_no_tools_token_exhausted",
            finish_reason=finish_reason,
            reasoning_content_chars=reasoning_chars,
            metric_key=MINI_FINAL_TOKEN_EXHAUSTED_METRIC,
        )
    return FinalNoToolsResolution(
        content="",
        event=(
            "final_no_tools_reasoning_only"
            if reasoning_chars > 0
            else "final_no_tools_empty_output"
        ),
        error="final_no_tools_empty_output",
        finish_reason=finish_reason,
        reasoning_content_chars=reasoning_chars,
        metric_key=MINI_FINAL_EMPTY_OUTPUT_METRIC,
    )


def _dsml_attrs(raw: str) -> Dict[str, str]:
    return {str(k): str(v) for k, v in _DSML_ATTR_RE.findall(str(raw or ""))}


def extract_dsml_tool_calls(content: Any) -> List[Dict[str, Any]]:
    """Parse DeepSeek DSML text tool calls into OpenAI-style tool call dicts."""

    if not isinstance(content, str) or "DSML" not in content:
        return []
    calls: List[Dict[str, Any]] = []
    for match in _DSML_INVOKE_RE.finditer(content):
        attrs = _dsml_attrs(match.group("attrs"))
        name = str(attrs.get("name", "") or "").strip()
        if not name:
            continue
        params: Dict[str, str] = {}
        for param_match in _DSML_PARAMETER_RE.finditer(match.group("body")):
            param_attrs = _dsml_attrs(param_match.group("attrs"))
            param_name = str(param_attrs.get("name", "") or "").strip()
            if not param_name:
                continue
            params[param_name] = param_match.group("value")
        calls.append(
            {
                "id": f"call_dsml_{len(calls) + 1}",
                "type": "function",
                "function": {
                    "name": name,
                    "arguments": json.dumps(params, ensure_ascii=False),
                },
            }
        )
    return calls


def _simple_xml_scalar(value: str) -> Any:
    text = str(value or "").strip()
    if not text:
        return ""
    try:
        parsed = json.loads(text)
    except (TypeError, ValueError, json.JSONDecodeError):
        return text
    return parsed


def _normalize_simple_xml_tool_arguments(
    name: str,
    arguments: Mapping[str, Any],
) -> Optional[Dict[str, Any]]:
    normalized = {str(key): value for key, value in arguments.items()}
    if name in {"search_mathlib", "search_theorems"}:
        if "limit" in normalized and "max_results" not in normalized:
            normalized["max_results"] = normalized.pop("limit")
    if name == "apply_decl_to_goal":
        if "name" in normalized and "decl_name" not in normalized:
            normalized["decl_name"] = normalized.pop("name")
    if name == "compute_examples":
        if "query" in normalized and "queries" not in normalized:
            normalized["queries"] = [normalized.pop("query")]
        queries = normalized.get("queries")
        if isinstance(queries, str):
            normalized["queries"] = [queries]
        elif not (
            isinstance(queries, list)
            and queries
            and all(isinstance(item, str) and item.strip() for item in queries)
        ):
            return None
    allowed = _MINI_TEXT_TOOL_PROPERTIES.get(name, frozenset())
    if not normalized or not set(normalized).issubset(allowed):
        return None
    required = _MINI_TEXT_TOOL_REQUIRED.get(name, "")
    if required and required not in normalized:
        return None
    string_fields = allowed - {"queries", "max_results"}
    for field_name in string_fields.intersection(normalized):
        value = normalized[field_name]
        if not isinstance(value, str):
            return None
        if field_name == required and not value.strip():
            return None
    if "max_results" in normalized:
        max_results = normalized["max_results"]
        if isinstance(max_results, bool) or not isinstance(max_results, int):
            return None
    if "mode" in normalized and normalized["mode"] not in {
        "eval",
        "reduce",
        "check",
    }:
        return None
    return normalized


def _simple_xml_tool_arguments(name: str, body: str) -> Optional[Dict[str, Any]]:
    text = str(body or "").strip()
    if not text:
        return None
    try:
        parsed = json.loads(text)
    except (TypeError, ValueError, json.JSONDecodeError):
        parsed = None
    if isinstance(parsed, dict):
        return _normalize_simple_xml_tool_arguments(name, parsed)

    keyed: Dict[str, Any] = {}
    keyed_form = True
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        match = re.fullmatch(
            r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*?)",
            stripped,
        )
        if match is None:
            keyed_form = False
            break
        keyed[match.group(1)] = _simple_xml_scalar(match.group(2))
    if keyed_form and keyed:
        normalized_keyed = _normalize_simple_xml_tool_arguments(name, keyed)
        if normalized_keyed is not None:
            return normalized_keyed
        recognized_keys = _MINI_TEXT_TOOL_PROPERTIES.get(
            name,
            frozenset(),
        ) | _MINI_TEXT_TOOL_ALIASES.get(name, frozenset())
        if set(keyed).intersection(recognized_keys):
            return None

    bare_argument = _MINI_TEXT_TOOL_BARE_ARGUMENT.get(str(name or ""))
    if bare_argument:
        return {bare_argument: text}
    if name == "compute_examples":
        return {"queries": [text]}
    return None


def _mask_nonprotocol_regions(content: str) -> str:
    """Mask fenced and Lean-comment/string regions while preserving offsets."""

    text = str(content or "")
    masked = list(text)

    def _blank(start: int, end: int) -> None:
        for index in range(start, min(end, len(masked))):
            if masked[index] not in {"\n", "\r"}:
                masked[index] = " "

    fence_char = ""
    fence_width = 0
    offset = 0
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip(" \t")
        marker_match = re.match(r"(`{3,}|~{3,})", stripped)
        if fence_char:
            _blank(offset, offset + len(line))
            close_match = re.fullmatch(
                rf"{re.escape(fence_char)}{{{fence_width},}}[ \t]*(?:\r?\n)?",
                stripped,
            )
            if close_match is not None:
                fence_char = ""
                fence_width = 0
        elif marker_match is not None:
            marker = marker_match.group(1)
            fence_char = marker[0]
            fence_width = len(marker)
            _blank(offset, offset + len(line))
        offset += len(line)
    if offset < len(text):
        _blank(offset, len(text))

    scan = "".join(masked)
    index = 0
    block_depth = 0
    in_string = False
    while index < len(scan):
        if block_depth:
            if scan.startswith("/-", index):
                block_depth += 1
                _blank(index, index + 2)
                index += 2
                continue
            if scan.startswith("-/", index):
                block_depth -= 1
                _blank(index, index + 2)
                index += 2
                continue
            _blank(index, index + 1)
            index += 1
            continue
        if in_string:
            if scan[index] == "\\":
                _blank(index, index + 2)
                index += 2
                continue
            char = scan[index]
            _blank(index, index + 1)
            index += 1
            if char == '"':
                in_string = False
            continue
        if scan.startswith("--", index):
            line_end = scan.find("\n", index)
            if line_end < 0:
                line_end = len(scan)
            _blank(index, line_end)
            index = line_end
            continue
        if scan.startswith("/-", index):
            block_depth = 1
            _blank(index, index + 2)
            index += 2
            continue
        if scan[index] == '"':
            in_string = True
            _blank(index, index + 1)
        index += 1
    return "".join(masked)


def extract_simple_xml_tool_calls(
    content: Any,
    *,
    allowed_tool_names: Optional[Sequence[str]] = None,
) -> List[Dict[str, Any]]:
    """Normalize DeepSeek's short XML tool form into ordinary tool calls.

    Only line-anchored, balanced tags for Mini's known tools are accepted.
    Fenced code is excluded so a Lean string or comment cannot become a call.
    Callers may further restrict names to the schemas enabled for that turn.
    """

    if not isinstance(content, str) or "<" not in content:
        return []
    if allowed_tool_names is None:
        allowed = set(_MINI_TEXT_TOOL_NAMES)
    else:
        allowed = {
            str(name or "").strip()
            for name in allowed_tool_names
            if str(name or "").strip()
        }
        allowed.intersection_update(_MINI_TEXT_TOOL_NAMES)
    if not allowed:
        return []
    scan_text = _mask_nonprotocol_regions(content)
    calls: List[Dict[str, Any]] = []
    for match in _SIMPLE_XML_TOOL_CALL_RE.finditer(scan_text):
        name = str(match.group("name") or "").strip()
        if name not in allowed:
            continue
        body_start, body_end = match.span("body")
        arguments = _simple_xml_tool_arguments(
            name,
            content[body_start:body_end],
        )
        if arguments is None:
            continue
        calls.append(
            {
                "id": f"call_xml_{len(calls) + 1}",
                "type": "function",
                "function": {
                    "name": name,
                    "arguments": json.dumps(arguments, ensure_ascii=False),
                },
            }
        )
    return calls


def is_deepseek_client(client: Any) -> bool:
    """Whether a client/model is backed by DeepSeek."""

    cfg = getattr(client, "cfg", None)
    base_urls = (
        getattr(client, "base_url", ""),
        getattr(client, "last_used_base_url", ""),
        getattr(cfg, "base_url", ""),
    )
    if any(base_url_matches_provider(str(url or ""), "deepseek") for url in base_urls):
        return True
    model_values = (
        getattr(client, "model", ""),
        getattr(client, "last_used_model", ""),
        getattr(cfg, "model", ""),
        getattr(cfg, "name", ""),
    )
    return any("deepseek" in str(value or "").strip().lower() for value in model_values)


def should_use_raw_final_no_tools(client: Any) -> bool:
    """DeepSeek should not receive a tools schema on the final no-tools turn."""

    return is_deepseek_client(client)


def toolless_final_messages(messages: Sequence[dict]) -> List[dict]:
    """Flatten a tool-call transcript into ordinary chat messages.

    Some providers reject or over-interpret ``role=tool`` messages when no
    tools schema is present.  The final no-tools call only needs the evidence,
    not a live tool protocol transcript.
    """

    flattened: List[dict] = []
    pending_tool_names: Dict[str, List[str]] = {}
    emitted_tool_labels: Dict[str, int] = {}

    # These fields are not part of the live tool protocol.  They carry the
    # atomicity/freshness contract used by prompt reduction and by the
    # immediately-before-dispatch proof-idea validator.  Provider-private
    # reasoning continuation fields are deliberately excluded: after tool
    # messages have been flattened, this is a new no-tools answer boundary,
    # not a continuation of a live tool-call protocol.  Replaying those blobs
    # duplicated 100K+ characters of private DeepSeek reasoning and induced a
    # visible transcript echo instead of a final Lean artifact.
    conserved_metadata = {
        "pinned",
        "pin",
        "preserve_context",
        "_required_prompt_context",
        "_selected_proof_idea_packet",
    }

    def ordinary_message(raw_msg: dict, *, role: str, content: str) -> dict:
        result = {"role": role, "content": content}
        for key in conserved_metadata:
            if key in raw_msg:
                result[key] = raw_msg[key]
        return result

    def tool_label(raw_msg: dict) -> str:
        tcid = str(raw_msg.get("tool_call_id", "") or "")
        explicit_name = str(raw_msg.get("name", "") or "")
        name = explicit_name
        if not name and tcid:
            queued = pending_tool_names.get(tcid) or []
            if queued:
                name = queued.pop(0)
        label = (
            f"{name} [{tcid}]"
            if name and tcid
            else name or tcid or "tool"
        )
        emitted_tool_labels[label] = int(emitted_tool_labels.get(label, 0) or 0) + 1
        count = emitted_tool_labels[label]
        if count > 1:
            return f"{label} #{count}"
        return label

    for raw_msg in list(messages or []):
        if not isinstance(raw_msg, dict):
            continue
        role = str(raw_msg.get("role", "") or "user")
        content = raw_msg.get("content", "")
        if isinstance(content, list):
            content = "\n".join(
                str(part.get("text", "") or "")
                for part in content
                if isinstance(part, dict)
            )
        content_text = str(content or "")
        if role == "assistant":
            content_text = strip_text_tool_call_requests(content_text)
            tool_calls = raw_msg.get("tool_calls")
            if isinstance(tool_calls, list) and tool_calls:
                pending_tool_names = {}
                for tc in tool_calls:
                    if not isinstance(tc, dict):
                        continue
                    tcid = str(tc.get("id", "") or "")
                    function = tc.get("function")
                    if not isinstance(function, dict):
                        function = {}
                    name = str(function.get("name", "") or "")
                    if tcid and name:
                        pending_tool_names.setdefault(tcid, []).append(name)
                combined = content_text.strip()
                if combined:
                    flattened.append(
                        ordinary_message(
                            raw_msg,
                            role=(
                                role
                                if role in {"system", "user", "assistant"}
                                else "user"
                            ),
                            content=combined,
                        )
                    )
                elif any(key in raw_msg for key in conserved_metadata):
                    # Opaque reasoning continuations can be provider-required
                    # even when the assistant's visible content is empty.
                    flattened.append(
                        ordinary_message(raw_msg, role="assistant", content="")
                    )
                continue
            if not content_text.strip() and not raw_msg.get("tool_calls"):
                continue
        if role == "tool":
            flattened.append(
                ordinary_message(
                    raw_msg,
                    role="user",
                    content=f"Tool result ({tool_label(raw_msg)}):\n{content_text}",
                )
            )
            continue
        flattened.append(
            ordinary_message(
                raw_msg,
                role=role if role in {"system", "user", "assistant"} else "user",
                content=content_text,
            )
        )
    return flattened


def strip_text_tool_call_requests(content: str) -> str:
    """Remove assistant-authored textual pseudo-tool calls from copied history."""

    text = str(content or "")
    scan_text = _mask_nonprotocol_regions(text)
    spans = [
        match.span()
        for match in _SIMPLE_XML_TOOL_CALL_RE.finditer(scan_text)
        if str(match.group("name") or "") in _MINI_TEXT_TOOL_NAMES
    ]
    if spans:
        pieces: List[str] = []
        cursor = 0
        for start, end in spans:
            pieces.append(text[cursor:start])
            if end < len(text) and text[end] == "\r":
                end += 1
            if end < len(text) and text[end] == "\n":
                end += 1
            cursor = end
        pieces.append(text[cursor:])
        text = "".join(pieces)
    marker = "Tool calls requested:"
    marker_pos = text.find(marker)
    if marker_pos < 0:
        return text.rstrip()
    return text[:marker_pos].rstrip()


def _first_dsml_try_lean_code(content: str) -> str:
    for call in extract_dsml_tool_calls(content):
        fn = call.get("function") or {}
        if str(fn.get("name", "") or "") != "try_lean":
            continue
        args, parse_error = parse_tool_arguments(fn.get("arguments", None))
        if parse_error:
            continue
        code_value = args.get("code")
        if isinstance(code_value, str):
            code = code_value.strip()
            if code:
                return code
    return ""


def _first_text_try_lean_code(content: str) -> str:
    text = str(content or "")
    decoder = json.JSONDecoder()
    start = 0
    while True:
        call_pos = text.find("try_lean", start)
        if call_pos < 0:
            return ""
        paren_pos = text.find("(", call_pos + len("try_lean"))
        if paren_pos < 0:
            return ""
        json_pos = paren_pos + 1
        while json_pos < len(text) and text[json_pos].isspace():
            json_pos += 1
        if json_pos >= len(text) or text[json_pos] != "{":
            start = paren_pos + 1
            continue
        try:
            args, end_pos = decoder.raw_decode(text[json_pos:])
        except json.JSONDecodeError:
            start = json_pos + 1
            continue
        close_pos = json_pos + end_pos
        while close_pos < len(text) and text[close_pos].isspace():
            close_pos += 1
        if close_pos >= len(text) or text[close_pos] != ")":
            start = close_pos
            continue
        args, parse_error = parse_tool_arguments(text[json_pos : json_pos + end_pos])
        if not parse_error:
            code_value = args.get("code")
            code = code_value.strip() if isinstance(code_value, str) else ""
            if code:
                return code
        start = close_pos + 1


def _has_text_tool_call_request(content: str) -> bool:
    text = str(content or "")
    if "Tool calls requested:" in text and re.search(
        r"(?m)^\s*-\s*[A-Za-z_][A-Za-z0-9_]*\s*\(",
        text,
    ):
        return True
    scan_text = _mask_nonprotocol_regions(text)
    return any(
        re.search(
            rf"(?m)^[ \t]*<{re.escape(name)}>[ \t]*$",
            scan_text,
        )
        for name in _MINI_TEXT_TOOL_NAMES
    )


def _checked_code_body(code: Any) -> str:
    body = str(code or "").strip()
    fence = re.search(
        r"```(?:lean|lean4)?\s*\n?(.*?)```",
        body,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if fence is not None:
        body = str(fence.group(1) or "").strip()
    return body


def _fenced_lean(code: str) -> str:
    body = _checked_code_body(code)
    return f"```lean\n{body}\n```"


def deepseek_dsml_feedback_after_budget() -> str:
    return (
        "The previous response used DeepSeek DSML tool-call markup, but tools "
        "are unavailable in this final step. Submit one fenced Lean proof block "
        "now, using the tool results already shown in the transcript."
    )


def deepseek_text_tool_feedback_after_budget() -> str:
    return (
        "The previous response copied a textual tool-call request, but tools "
        "are unavailable in this final step. Submit one fenced Lean proof block "
        "now, using the tool results already shown in the transcript."
    )


def handle_deepseek_dsml_after_budget(
    *,
    client: Any,
    content: str,
    already_reprompted: bool = False,
) -> DSMLAfterBudgetHandling:
    """Normalize DeepSeek tool markup/text emitted after tool budget exhaustion."""

    text = str(content or "")
    if not is_deepseek_client(client):
        return DSMLAfterBudgetHandling(content=text)
    if "DSML" in text:
        code = _first_dsml_try_lean_code(text)
        if code:
            return DSMLAfterBudgetHandling(
                content=_fenced_lean(code),
                event="deepseek_dsml_try_lean_salvaged",
                original_content=text,
                content_metric_key=DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC,
                metric_key=DEEPSEEK_DSML_TRY_LEAN_SALVAGED_METRIC,
                salvaged_code=code,
            )
        if already_reprompted:
            return DSMLAfterBudgetHandling(
                content="",
                event="deepseek_dsml_tool_after_budget_repeated",
                original_content=text,
                content_metric_key=DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC,
                metric_key=DEEPSEEK_DSML_TOOL_AFTER_BUDGET_METRIC,
            )
        return DSMLAfterBudgetHandling(
            content=text,
            event="deepseek_dsml_tool_after_budget",
            original_content=text,
            content_metric_key=DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC,
            metric_key=DEEPSEEK_DSML_TOOL_AFTER_BUDGET_METRIC,
            feedback=deepseek_dsml_feedback_after_budget(),
        )
    if not _has_text_tool_call_request(text):
        return DSMLAfterBudgetHandling(content=text)
    code = _first_text_try_lean_code(text)
    if code:
        return DSMLAfterBudgetHandling(
            content=_fenced_lean(code),
            event="deepseek_text_try_lean_salvaged",
            original_content=text,
            content_metric_key=DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
            metric_key=DEEPSEEK_TEXT_TRY_LEAN_SALVAGED_METRIC,
            salvaged_code=code,
        )
    if already_reprompted:
        return DSMLAfterBudgetHandling(
            content="",
            event="deepseek_text_tool_after_budget_repeated",
            original_content=text,
            content_metric_key=DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
            metric_key=DEEPSEEK_TEXT_TOOL_AFTER_BUDGET_METRIC,
        )
    return DSMLAfterBudgetHandling(
        content=text,
        event="deepseek_text_tool_after_budget",
        original_content=text,
        content_metric_key=DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
        metric_key=DEEPSEEK_TEXT_TOOL_AFTER_BUDGET_METRIC,
        feedback=deepseek_text_tool_feedback_after_budget(),
    )
