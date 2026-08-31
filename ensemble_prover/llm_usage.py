"""Request-scoped LLM usage, reservation, receipt, and cost accounting.

Immutable request records let shared clients, child sessions, retries, and
provider wrappers charge the correct scope without inferring usage from mutable
before-and-after counters.
"""

from __future__ import annotations

import asyncio
import contextvars
import hashlib
import inspect
import json
import math
import re
import time
import uuid
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass, field, replace
from numbers import Integral
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence

from .provider_dispatch_continuation import (
    PROVIDER_DISPATCH_EXPOSURE_TRACKER as _PROVIDER_DISPATCH_EXPOSURE_TRACKER,
    PROVIDER_DISPATCH_MARKER as _PROVIDER_DISPATCH_MARKER,
    PROVIDER_DISPATCH_OBSERVER as _PROVIDER_DISPATCH_OBSERVER,
    PROVIDER_DISPATCH_TARGET as _PROVIDER_DISPATCH_TARGET,
    PROVIDER_PENDING_DISPATCH_RECEIPT as _PROVIDER_PENDING_DISPATCH_RECEIPT,
)

from .llm_deadline import llm_retry_deadline_record_from_exception
from .proof_lineage import ProofLineageEnvelope
from .pricing import (
    compute_cost_usd,
    compute_model_cost_usd,
    conservative_reservation_token_pricing,
    conservative_reservation_token_pricing_async,
    lookup_known_token_pricing,
    provider_for_base_url,
)
from .provider_tool_protocol import (
    MiniRequestEnvelopePolicy,
    MiniRequestEnvelopeReceipt,
    bind_mini_request_envelope_receipt,
    mini_request_concrete_leaf_bindings,
    mini_request_wrapper_children,
    resolve_mini_request_envelopes,
)
from .runtime_context import (
    mark_runtime_owned_callback,
    require_hard_timeout_capability_active,
)
from .utils import estimate_tokens, format_exception
from .sampling_controls import is_api_default_temperature_override


@dataclass(frozen=True)
class ProviderUsageRecord:
    """One provider response usage payload, normalized with pricing context."""

    model: str
    base_url: str
    input_tokens: int = 0
    output_tokens: int = 0
    cached_input_tokens: int = 0
    cache_write_tokens: int = 0
    prompt_cache_miss_tokens: int = 0
    reasoning_output_tokens: int = 0
    usage_source: str = "provider_usage"
    raw_usage: Dict[str, Any] = field(default_factory=dict)
    reported_cost_usd: Optional[float] = None
    reported_cost_source: str = ""
    reported_cost_unit: str = ""
    requested_model: str = ""
    temperature_requested: Optional[float] = None
    temperature_sent: Optional[float] = None
    temperature_phase_key: str = ""
    temperature_source: str = ""
    temperature_provider_dropped: bool = False
    temperature_provider_drop_reason: str = ""
    reservation_target_id: str = ""
    reservation_dispatch_ordinal: int = 0

    def as_dict(self) -> Dict[str, Any]:
        return {
            "model": self.model,
            "base_url": self.base_url,
            "input_tokens": int(self.input_tokens),
            "output_tokens": int(self.output_tokens),
            "cached_input_tokens": int(self.cached_input_tokens),
            "cache_write_tokens": int(self.cache_write_tokens),
            "prompt_cache_miss_tokens": int(self.prompt_cache_miss_tokens),
            "reasoning_output_tokens": int(self.reasoning_output_tokens),
            "usage_source": self.usage_source,
            "raw_usage": dict(self.raw_usage),
            "reported_cost_usd": self.reported_cost_usd,
            "reported_cost_source": str(self.reported_cost_source or ""),
            "reported_cost_unit": str(self.reported_cost_unit or ""),
            "requested_model": str(self.requested_model or ""),
            "temperature_requested": self.temperature_requested,
            "temperature_sent": self.temperature_sent,
            "temperature_phase_key": str(self.temperature_phase_key or ""),
            "temperature_source": str(self.temperature_source or ""),
            "temperature_provider_dropped": bool(
                self.temperature_provider_dropped
            ),
            "temperature_provider_drop_reason": str(
                self.temperature_provider_drop_reason or ""
            ),
            "reservation_target_id": str(self.reservation_target_id or ""),
            "reservation_dispatch_ordinal": max(
                0,
                int(self.reservation_dispatch_ordinal or 0),
            ),
        }


@dataclass(frozen=True)
class CostReservation:
    """Pre-dispatch reservation for one logical LLM call."""

    reservation_id: str
    request_id: str
    role: str
    scope: str
    action_id: str
    call_kind: str
    estimated_input_tokens: int
    reserved_output_tokens: int
    estimated_cost_usd: float
    estimated_models: List[Dict[str, Any]]
    metadata: Dict[str, Any] = field(default_factory=dict)
    hold_for_late_usage: bool = False
    created_at: float = field(default_factory=time.time)


class CostBudgetExceeded(RuntimeError):
    """Raised before dispatch when a request cannot fit its dollar budget."""

    def __init__(
        self,
        *,
        max_cost_usd: float,
        accounted_cost_usd: float,
        requested_cost_usd: float,
        reason: str = "cost_budget_exhausted",
    ) -> None:
        self.max_cost_usd = float(max_cost_usd)
        self.accounted_cost_usd = float(accounted_cost_usd)
        self.requested_cost_usd = float(requested_cost_usd)
        self.reason = str(reason or "cost_budget_exhausted")
        super().__init__(
            f"{self.reason}: accounted=${self.accounted_cost_usd:.6f} "
            f"requested=${self.requested_cost_usd:.6f} "
            f"budget=${self.max_cost_usd:.6f}"
        )


class ProviderDispatchAttemptLimitExceeded(RuntimeError):
    """Raised before transport when one logical call spent its dispatch ceiling."""

    def __init__(
        self,
        message: str,
        *,
        provider_dispatches_started: int = 0,
        dispatch_attempt_limit: int = 0,
        next_dispatch_ordinal: int = 0,
        provider_dispatch_attempt_limit_target_id: str = "",
    ) -> None:
        self.provider_dispatches_started = max(
            0,
            int(provider_dispatches_started or 0),
        )
        self.dispatch_attempt_limit = max(0, int(dispatch_attempt_limit or 0))
        self.next_dispatch_ordinal = max(0, int(next_dispatch_ordinal or 0))
        self.provider_dispatch_attempt_limit_target_id = str(
            provider_dispatch_attempt_limit_target_id or ""
        ).strip()
        super().__init__(str(message or "provider dispatch attempt limit exhausted"))


@dataclass
class ProviderDispatchAttemptLease:
    """One logical dispatch ceiling shared across internal provider retries."""

    max_attempts: int
    _next_receipt_ordinal: int = field(default=0, init=False, repr=False)
    _live_receipt_ids: set[str] = field(default_factory=set, init=False, repr=False)
    _marked_receipt_ids: set[str] = field(default_factory=set, init=False, repr=False)
    _lock: asyncio.Lock = field(default_factory=asyncio.Lock, init=False, repr=False)

    def __post_init__(self) -> None:
        self.max_attempts = max(0, int(self.max_attempts or 0))

    @property
    def provider_dispatches_started(self) -> int:
        return len(self._live_receipt_ids)

    @property
    def authenticated_dispatches_started(self) -> int:
        """Return dispatches confirmed by this lease's exact marker receipt."""

        return len(self._marked_receipt_ids)

    async def authorize(self) -> Dict[str, Any]:
        async with self._lock:
            next_ordinal = len(self._live_receipt_ids) + 1
            if self.max_attempts and next_ordinal > self.max_attempts:
                raise ProviderDispatchAttemptLimitExceeded(
                    "provider dispatch attempt limit exhausted before "
                    f"dispatch (limit={self.max_attempts}, "
                    f"next_ordinal={next_ordinal})",
                    provider_dispatches_started=len(self._live_receipt_ids),
                    dispatch_attempt_limit=self.max_attempts,
                    next_dispatch_ordinal=next_ordinal,
                )
            self._next_receipt_ordinal += 1
            receipt_id = f"logical-dispatch:{self._next_receipt_ordinal}"
            self._live_receipt_ids.add(receipt_id)
            return {
                "provider_dispatch_lease_receipt_id": receipt_id,
                "provider_dispatch_logical_ordinal": next_ordinal,
            }

    def retire(self, details: Mapping[str, Any]) -> None:
        receipt_id = str(
            dict(details or {}).get("provider_dispatch_lease_receipt_id") or ""
        ).strip()
        if receipt_id:
            self._live_receipt_ids.discard(receipt_id)
            self._marked_receipt_ids.discard(receipt_id)

    def mark_dispatched(self, details: Mapping[str, Any]) -> None:
        """Authenticate one actual dispatch against a live lease receipt."""

        receipt_id = str(
            dict(details or {}).get("provider_dispatch_lease_receipt_id") or ""
        ).strip()
        if receipt_id and receipt_id in self._live_receipt_ids:
            self._marked_receipt_ids.add(receipt_id)

    def annotate_exception(self, exc: BaseException) -> None:
        count = self.provider_dispatches_started
        try:
            prior = max(
                0,
                int(getattr(exc, "provider_dispatches_started", 0) or 0),
            )
        except (TypeError, ValueError, OverflowError):
            prior = 0
        try:
            setattr(exc, "provider_dispatches_started", max(prior, count))
        except Exception:
            pass


@dataclass
class ProviderDispatchExposureTracker:
    """Cancellation-independent ledger of live, actually-started dispatches."""

    _live_receipt_ids: set[tuple[str, str, str, str, str]] = field(
        default_factory=set,
        init=False,
        repr=False,
    )
    _anonymous_dispatches_started: int = field(default=0, init=False, repr=False)
    _parent: Optional["ProviderDispatchExposureTracker"] = field(
        default=None,
        init=False,
        repr=False,
    )
    _parent_forwarded_receipt_ids: set[tuple[str, str, str, str, str]] = field(
        default_factory=set,
        init=False,
        repr=False,
    )
    _parent_forwarded_anonymous: int = field(default=0, init=False, repr=False)

    @staticmethod
    def _receipt_identity(
        details: Mapping[str, Any],
    ) -> tuple[str, str, str, str, str]:
        clean = dict(details or {})
        return (
            str(clean.get("provider_dispatch_lease_receipt_id") or "").strip(),
            str(clean.get("dispatch_authorization_id") or "").strip(),
            str(clean.get("plain_dispatch_authorization_id") or "").strip(),
            str(
                clean.get("provider_dispatch_notification_receipt_id") or ""
            ).strip(),
            str(clean.get("provider_dispatch_marker_receipt_id") or "").strip(),
        )

    @property
    def provider_dispatches_started(self) -> int:
        return len(self._live_receipt_ids) + self._anonymous_dispatches_started

    def _add_receipt_identity(
        self,
        identity: tuple[str, str, str, str, str],
    ) -> bool:
        if identity in self._live_receipt_ids:
            return False
        self._live_receipt_ids.add(identity)
        if self._parent is not None:
            if self._parent._add_receipt_identity(identity):
                self._parent_forwarded_receipt_ids.add(identity)
        return True

    def _remove_receipt_identity(
        self,
        identity: tuple[str, str, str, str, str],
    ) -> bool:
        if identity not in self._live_receipt_ids:
            return False
        self._live_receipt_ids.remove(identity)
        if (
            self._parent is not None
            and identity in self._parent_forwarded_receipt_ids
        ):
            self._parent._remove_receipt_identity(identity)
            self._parent_forwarded_receipt_ids.discard(identity)
        return True

    def _add_anonymous(self, count: int = 1) -> None:
        clean_count = max(0, int(count or 0))
        if clean_count <= 0:
            return
        self._anonymous_dispatches_started += clean_count
        if self._parent is not None:
            self._parent._add_anonymous(clean_count)
            self._parent_forwarded_anonymous += clean_count

    def _remove_anonymous(self, count: int) -> int:
        removed = min(
            self._anonymous_dispatches_started,
            max(0, int(count or 0)),
        )
        if removed <= 0:
            return 0
        self._anonymous_dispatches_started -= removed
        if self._parent is not None and self._parent_forwarded_anonymous > 0:
            forwarded_removed = min(removed, self._parent_forwarded_anonymous)
            self._parent._remove_anonymous(forwarded_removed)
            self._parent_forwarded_anonymous -= forwarded_removed
        return removed

    def mark_dispatched(self, details: Mapping[str, Any]) -> None:
        identity = self._receipt_identity(details)
        if any(identity):
            self._add_receipt_identity(identity)
        else:
            self._add_anonymous()

    def retire_pre_generation_rejection(self, details: Mapping[str, Any]) -> None:
        identity = self._receipt_identity(details)
        if any(identity):
            self._remove_receipt_identity(identity)

    def link_parent(self, parent: "ProviderDispatchExposureTracker") -> None:
        """Forward current and future exposure into an enclosing action."""

        if parent is self:
            raise ValueError("provider exposure tracker cannot parent itself")
        if self._parent is not None and self._parent is not parent:
            raise RuntimeError("provider exposure tracker parent already bound")
        if self._parent is parent:
            return
        self._parent = parent
        for identity in tuple(self._live_receipt_ids):
            if parent._add_receipt_identity(identity):
                self._parent_forwarded_receipt_ids.add(identity)
        if self._anonymous_dispatches_started > 0:
            parent._add_anonymous(self._anonymous_dispatches_started)
            self._parent_forwarded_anonymous = self._anonymous_dispatches_started

    def settle_forwarded_exposure(
        self,
        *,
        already_accounted: int = 0,
    ) -> int:
        """Remove the settled prefix from the parent while keeping the link live."""

        remaining = max(0, int(already_accounted or 0))
        removed = 0
        while remaining > 0 and self._parent_forwarded_receipt_ids:
            identity = next(iter(self._parent_forwarded_receipt_ids))
            if self._parent is not None:
                self._parent._remove_receipt_identity(identity)
            self._parent_forwarded_receipt_ids.discard(identity)
            remaining -= 1
            removed += 1
        if remaining > 0 and self._parent_forwarded_anonymous > 0:
            anonymous_removed = min(
                remaining,
                self._parent_forwarded_anonymous,
            )
            if self._parent is not None:
                self._parent._remove_anonymous(anonymous_removed)
            self._parent_forwarded_anonymous -= anonymous_removed
            removed += anonymous_removed
        return removed

    def settle_all_current_exposure(self) -> int:
        """Clear the currently durable exposure while preserving live links."""

        settled = self.provider_dispatches_started
        for identity in tuple(self._live_receipt_ids):
            self._remove_receipt_identity(identity)
        self._remove_anonymous(self._anonymous_dispatches_started)
        return settled


class RequiredProviderKeywordUnsupported(TypeError):
    """A direct adapter cannot honor a phase-critical request capability."""

    # There is no lower leaf for this shim to try: at this boundary the
    # configured adapter/chain is exhausted, so callers should report a setup
    # conflict rather than an arbitrary TypeError action crash.
    is_provider_capability_conflict = True
    is_provider_capability_chain_exhausted = True


_MISSING_USAGE_NO_CHARGE_STATUSES = {
    "cancelled",
    "pre_dispatch_failure",
    "retryable_exception_no_charge",
}

_INTERNAL_USAGE_EVENT_KEYS = {
    "llm_retryable_exception_no_charge",
    "llm_retryable_exception_no_charge_kind",
    "llm_missing_usage_charged",
}

_PROTECTED_USAGE_EVENT_KEYS = {
    "phase",
    "verdict",
    "status",
    "error",
    "llm_request_id",
    "llm_reservation_id",
    "provider_dispatch_receipt_id",
    "role",
    "call_kind",
    "target_id",
    "status_code",
    "reason",
    "reservation_dispatch_ordinal",
    "late_usage",
    "input_tokens",
    "output_tokens",
    "cached_input_tokens",
    "cache_write_tokens",
    "prompt_cache_miss_tokens",
    "reasoning_output_tokens",
    "cost_usd",
    "estimated_cost_usd",
    "estimated_unknown_cost_usd",
    "estimated_unknown_reversed_cost_usd",
    "recovered_unknown_reversed_cost_usd",
    "pricing_known",
    "usage_missing",
    "missing_provider_target_ids",
    "provider_exposed_target_counts",
    "provider_observations",
    "estimated_models",
    "max_cost_usd",
    "llm_observed_usage_cost_usd",
    "llm_conservative_unknown_exposure_usd",
    "cost_accounting_incomplete",
    "llm_cost_accounting_incomplete",
    "llm_budget_accounted_cost_is_conservative_upper_bound",
    "llm_budget_accounted_cost_usd",
    "llm_budget_committed_cost_usd",
    "llm_budget_remaining_usd",
    "llm_cost_budget_exhausted",
    "llm_cancelled_provider_inflight",
    "llm_cancelled_provider_exposure_risk",
    "llm_cancelled_provider_exposure_reversed_cost_usd",
}

def _provider_dispatch_receipt_id(
    *,
    reservation_id: str,
    target_id: str,
    dispatch_ordinal: int,
) -> str:
    """Return the in-process identity of one concrete provider dispatch."""

    ordinal = max(0, int(dispatch_ordinal or 0))
    clean_reservation = str(reservation_id or "")
    clean_target = str(target_id or "")
    if not clean_reservation or not clean_target or ordinal <= 0:
        return ""
    payload = {
        "reservation_id": clean_reservation,
        "target_id": clean_target,
        "dispatch_ordinal": ordinal,
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _late_usage_receipt_id(
    record: ProviderUsageRecord,
    *,
    reservation_id: str,
) -> str:
    # Mutable provider payload content is evidence, not occurrence identity.
    return _provider_dispatch_receipt_id(
        reservation_id=reservation_id,
        target_id=record.reservation_target_id,
        dispatch_ordinal=record.reservation_dispatch_ordinal,
    )


def _late_rejection_receipt_id(
    *,
    reservation_id: str,
    target_id: str,
    dispatch_ordinal: int,
    status_code: int,
    reason: str,
) -> str:
    """Identify one transport dispatch's definitive rejection receipt."""

    del status_code, reason
    return _provider_dispatch_receipt_id(
        reservation_id=reservation_id,
        target_id=target_id,
        dispatch_ordinal=dispatch_ordinal,
    )


_LLM_USAGE_CONTEXT: contextvars.ContextVar[Dict[str, Any]] = (
    contextvars.ContextVar("llm_usage_context", default={})
)


def _merge_usage_metadata(
    base: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> Dict[str, Any]:
    """Merge metadata while preserving non-empty proof-lineage coordinates."""

    base_record = dict(base or {})
    overlay_record = dict(overlay or {})

    def validated(source: Mapping[str, Any]) -> ProofLineageEnvelope:
        try:
            return ProofLineageEnvelope.from_metadata(source)
        except (TypeError, ValueError):
            return ProofLineageEnvelope()

    base_envelope = validated(base_record)
    overlay_envelope = validated(overlay_record)
    merged = dict(base_record)
    merged.pop("proof_lineage", None)
    overlay_record.pop("proof_lineage", None)
    for field_name in ProofLineageEnvelope.__dataclass_fields__:
        merged.pop(field_name, None)
        overlay_record.pop(field_name, None)
    merged.update(overlay_record)
    lineage_values = {
        field_name: (
            getattr(overlay_envelope, field_name)
            or getattr(base_envelope, field_name)
        )
        for field_name in base_envelope.__dataclass_fields__
    }
    def coordinate_changed(field_name: str) -> bool:
        overlay_value = getattr(overlay_envelope, field_name)
        return bool(
            overlay_value
            and overlay_value != getattr(base_envelope, field_name)
        )

    reset_fields = set()
    if coordinate_changed("strategy_lineage_id"):
        reset_fields.update({"route_id", "claim_id", "statement_identity"})
    elif coordinate_changed("route_id"):
        reset_fields.update({"claim_id", "statement_identity"})
    elif coordinate_changed("claim_id"):
        reset_fields.add("statement_identity")
    if coordinate_changed("proof_candidate_id"):
        reset_fields.update(
            {"lean_residual_id", "repair_ticket_id", "accepted_fact_id"}
        )
    elif coordinate_changed("lean_residual_id"):
        reset_fields.update({"repair_ticket_id", "accepted_fact_id"})
    elif coordinate_changed("repair_ticket_id"):
        reset_fields.add("accepted_fact_id")
    target_changed = any(
        coordinate_changed(field_name)
        for field_name in (
            "strategy_lineage_id",
            "route_id",
            "claim_id",
            "statement_identity",
        )
    )
    if target_changed:
        # A nested child may inherit strategy ancestry, but lifecycle
        # descendants belong to its own target. Parentage is represented by
        # parent_lineage_id; retaining a host candidate/residual here fabricates
        # cross-target evidence.
        reset_fields.update({
            "assembly_id",
            "proof_candidate_id",
            "lean_residual_id",
            "repair_ticket_id",
            "accepted_fact_id",
        })
    if reset_fields:
        for field_name in reset_fields:
            lineage_values[field_name] = getattr(
                overlay_envelope,
                field_name,
            )
    envelope = base_envelope.updated(**lineage_values)
    lineage = envelope.to_record()
    if any(value for key, value in lineage.items() if key != "schema_version"):
        merged = envelope.merged_metadata(merged)
    return merged


@contextmanager
def bind_llm_usage_context(metadata: Mapping[str, Any]):
    """Bind authoritative action lineage to every metered call in this task.

    Context variables are coroutine-local, so nested child sessions and
    concurrent branches cannot overwrite one another.  Nested bindings inherit
    parent lineage unless they provide a more specific value.
    """

    merged = _merge_usage_metadata(
        dict(_LLM_USAGE_CONTEXT.get() or {}),
        {
            str(key): value
            for key, value in dict(metadata or {}).items()
            if value not in (None, "", {}, [], ())
        },
    )
    token = _LLM_USAGE_CONTEXT.set(merged)
    try:
        yield
    finally:
        _LLM_USAGE_CONTEXT.reset(token)


def llm_usage_context_metadata(
    metadata: Optional[Mapping[str, Any]] = None,
) -> Dict[str, Any]:
    """Merge call-local metadata with authoritative dispatch context."""

    merged = dict(metadata or {})
    # Dispatch identity and proof lineage describe the executing scheduler
    # boundary, so a stale caller-supplied value must not override them.
    return _merge_usage_metadata(
        merged,
        dict(_LLM_USAGE_CONTEXT.get() or {}),
    )


def _reservation_usage_event_metadata(reservation: Any) -> Dict[str, Any]:
    metadata = dict(getattr(reservation, "metadata", {}) or {})
    for key in _INTERNAL_USAGE_EVENT_KEYS | _PROTECTED_USAGE_EVENT_KEYS:
        metadata.pop(key, None)
    return metadata

@contextmanager
def provider_dispatch_target(target_id: str):
    """Attribute a nested transport and its usage to one reserved leaf."""
    token = _PROVIDER_DISPATCH_TARGET.set(str(target_id or ""))
    try:
        yield
    finally:
        _PROVIDER_DISPATCH_TARGET.reset(token)


def provider_dispatch_child_target_id(wrapper: Any, child_index: int) -> str:
    """Map one nested wrapper child to its flattened reservation leaf span."""

    children = mini_request_wrapper_children(wrapper)
    index = int(child_index)
    if index < 0 or index >= len(children):
        raise IndexError("provider dispatch child index is outside wrapper topology")
    parent_target = str(_PROVIDER_DISPATCH_TARGET.get() or "").strip()
    base = 0
    if parent_target:
        match = re.fullmatch(r"target:([0-9]+)", parent_target)
        if match is None:
            raise RuntimeError(
                "nested provider dispatch target is not a flattened leaf base"
            )
        base = int(match.group(1))
    offset = sum(
        len(mini_request_concrete_leaf_bindings(child))
        for child in children[:index]
    )
    return f"target:{base + offset}"


@contextmanager
def provider_dispatch_observer(callback: Callable[..., Any]):
    """Observe the concrete transport boundary for one logical operation.

    The cost marker below is intentionally synchronous because usage settlement
    only mutates request-local accounting state.  Formal search additionally
    needs to record live progress immediately *before* transport dispatch.
    Keeping that awaitable observer separate preserves the existing marker API
    while allowing transports to publish intent before any request can be billed.
    """

    token = _PROVIDER_DISPATCH_OBSERVER.set(callback)
    try:
        yield
    finally:
        _PROVIDER_DISPATCH_OBSERVER.reset(token)


@contextmanager
def bind_provider_dispatch_exposure_tracker(
    tracker: ProviderDispatchExposureTracker,
):
    """Bind one shared live-exposure ledger across cancellation boundaries."""

    token = _PROVIDER_DISPATCH_EXPOSURE_TRACKER.set(tracker)
    try:
        yield tracker
    finally:
        _PROVIDER_DISPATCH_EXPOSURE_TRACKER.reset(token)


def _track_provider_dispatch_event(
    event: str,
    details: Mapping[str, Any],
) -> None:
    tracker = _PROVIDER_DISPATCH_EXPOSURE_TRACKER.get()
    if tracker is None:
        return
    if str(event or "").strip() == "pre_generation_rejection":
        tracker.retire_pre_generation_rejection(details)
    else:
        tracker.mark_dispatched(details)


async def notify_provider_dispatch_observer(
    **details: Any,
) -> Dict[str, Any]:
    """Authorize one transport dispatch and return its accounting receipt."""

    require_hard_timeout_capability_active(
        "provider transport dispatch authorization"
    )
    observer = _PROVIDER_DISPATCH_OBSERVER.get()
    if observer is None:
        receipt = dict(details)
    else:
        # The observer API predates accounting receipts: legacy progress hooks
        # are legitimately zero-argument callbacks, while the cost controller
        # consumes one details mapping. Inspect the call contract before
        # invoking it; catching TypeError after invocation could run a
        # mutating callback twice when the callback itself raises TypeError.
        try:
            inspect.signature(observer).bind(dict(details))
        except (TypeError, ValueError):
            result = observer()
        else:
            result = observer(dict(details))
        if inspect.isawaitable(result):
            result = await result
        receipt = dict(result or details)
    receipt["provider_dispatch_notification_receipt_id"] = (
        f"provider-dispatch:{uuid.uuid4().hex}"
    )
    _PROVIDER_PENDING_DISPATCH_RECEIPT.set(receipt)
    return receipt


def mark_provider_dispatched(**details: Any) -> None:
    """Mark the current metered operation at its concrete transport boundary."""
    marker = _PROVIDER_DISPATCH_MARKER.get()
    receipt = dict(details or _PROVIDER_PENDING_DISPATCH_RECEIPT.get() or {})
    if marker is not None:
        marker("dispatch", receipt)
    else:
        _track_provider_dispatch_event("dispatch", receipt)


def mark_provider_pre_generation_rejection(
    *,
    status_code: int,
    reason: str = "http_rejection",
    dispatch_receipt: Optional[Mapping[str, Any]] = None,
) -> None:
    """Retire one dispatch known not to have generated a completion.

    This is intentionally limited to authoritative provider receipts such as
    unsupported-parameter 4xx responses.  Transport timeouts remain ambiguous
    and therefore retain conservative missing-usage accounting.
    """

    marker = _PROVIDER_DISPATCH_MARKER.get()
    receipt = {
        "status_code": int(status_code),
        "reason": str(reason or "http_rejection"),
        **dict(
            dispatch_receipt
            or _PROVIDER_PENDING_DISPATCH_RECEIPT.get()
            or {}
        ),
    }
    if marker is not None:
        marker("pre_generation_rejection", receipt)
    else:
        _track_provider_dispatch_event("pre_generation_rejection", receipt)


def _usage_int(value: Any) -> int:
    try:
        if value is None:
            return 0
        return max(0, int(value))
    except Exception:
        return 0


def _usage_float(value: Any) -> Optional[float]:
    try:
        if value is None:
            return None
        out = float(value)
        if not math.isfinite(out) or out < 0:
            return None
        return out
    except Exception:
        return None


def provider_usage_from_payload(
    data: Dict[str, Any],
    *,
    model: str,
    base_url: str,
    temperature_requested: Optional[float] = None,
    temperature_sent: Optional[float] = None,
    temperature_phase_key: str = "",
    temperature_source: str = "",
    temperature_provider_dropped: bool = False,
    temperature_provider_drop_reason: str = "",
) -> Optional[ProviderUsageRecord]:
    """Normalize OpenAI-compatible usage data from a provider response."""

    usage = data.get("usage") if isinstance(data, dict) else None
    if not isinstance(usage, dict):
        return None
    input_tokens = _usage_int(usage.get("prompt_tokens", usage.get("input_tokens", 0)))
    output_tokens = _usage_int(
        usage.get("completion_tokens", usage.get("output_tokens", 0))
    )

    detail_records = [
        detail
        for detail in (
            usage.get("prompt_tokens_details"),
            usage.get("input_tokens_details"),
        )
        if isinstance(detail, dict)
    ]
    cached = max(
        (_usage_int(detail.get("cached_tokens", 0)) for detail in detail_records),
        default=0,
    )
    if cached <= 0:
        cached = _usage_int(usage.get("prompt_cache_hit_tokens", 0))
    if cached <= 0:
        cached = _usage_int(usage.get("cache_read_input_tokens", 0))
    if cached <= 0:
        cached = _usage_int(usage.get("cached_prompt_tokens", 0))
    cached = min(cached, input_tokens)

    cache_write_tokens = max(
        (
            _usage_int(detail.get("cache_write_tokens", 0))
            for detail in detail_records
        ),
        default=0,
    )
    if cache_write_tokens <= 0:
        cache_write_tokens = _usage_int(usage.get("cache_write_input_tokens", 0))
    cache_write_tokens = min(
        cache_write_tokens,
        max(0, input_tokens - cached),
    )

    miss_tokens = _usage_int(usage.get("prompt_cache_miss_tokens", 0))
    if miss_tokens <= 0:
        miss_tokens = max(0, input_tokens - cached)

    reasoning_tokens = _usage_int(usage.get("reasoning_tokens", 0))
    completion_details = usage.get("completion_tokens_details")
    if isinstance(completion_details, dict):
        reasoning_tokens = max(
            reasoning_tokens,
            _usage_int(completion_details.get("reasoning_tokens", 0)),
        )
    output_details = usage.get("output_tokens_details")
    if isinstance(output_details, dict):
        reasoning_tokens = max(
            reasoning_tokens,
            _usage_int(output_details.get("reasoning_tokens", 0)),
        )
    provider = provider_for_base_url(base_url)
    reported_cost = None
    reported_cost_source = ""
    reported_cost_unit = ""
    if provider == "openrouter":
        reported_cost = _usage_float(usage.get("cost"))
        if reported_cost is not None:
            reported_cost_source = "openrouter_usage.cost"
            reported_cost_unit = "openrouter_credits"
    has_token_totals = any(
        key in usage
        for key in (
            "prompt_tokens",
            "input_tokens",
            "completion_tokens",
            "output_tokens",
        )
    )
    if not has_token_totals and reported_cost is None:
        return None
    if isinstance(data, dict):
        response_model = str(data.get("model") or model or "")
    else:
        response_model = str(model or "")

    return ProviderUsageRecord(
        model=response_model,
        base_url=str(base_url or ""),
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        cached_input_tokens=cached,
        cache_write_tokens=cache_write_tokens,
        prompt_cache_miss_tokens=miss_tokens,
        reasoning_output_tokens=reasoning_tokens,
        raw_usage=dict(usage),
        reported_cost_usd=reported_cost,
        reported_cost_source=reported_cost_source,
        reported_cost_unit=reported_cost_unit,
        requested_model=str(model or ""),
        temperature_requested=temperature_requested,
        temperature_sent=temperature_sent,
        temperature_phase_key=str(temperature_phase_key or ""),
        temperature_source=str(temperature_source or ""),
        temperature_provider_dropped=bool(temperature_provider_dropped),
        temperature_provider_drop_reason=str(temperature_provider_drop_reason or ""),
    )


def emit_usage_callback(
    usage_callback: Optional[Callable[[ProviderUsageRecord], Any]],
    record: Optional[ProviderUsageRecord],
) -> None:
    """Invoke a provider usage callback without perturbing LLM results."""

    if usage_callback is None or record is None:
        return
    try:
        result = usage_callback(record)
        if inspect.isawaitable(result):
            # Provider methods are on the hot response path and cannot await a
            # caller-owned sink here.  Schedule best-effort async sinks.
            asyncio.create_task(result)  # type: ignore[arg-type]
    except Exception:
        return


def estimate_messages_tokens(
    messages: Sequence[Dict[str, Any]],
    *,
    model: Optional[str] = None,
    tools: Optional[Sequence[Dict[str, Any]]] = None,
) -> int:
    """Conservative token estimate for pre-dispatch budget reservations."""

    total = 0
    for message in list(messages or ()):
        if not isinstance(message, dict):
            total += estimate_tokens(str(message), model=model)
            continue
        try:
            text = json.dumps(
                message,
                ensure_ascii=True,
                separators=(",", ":"),
                allow_nan=False,
            )
        except Exception:
            text = str(message)
        total += estimate_tokens(text, model=model)
    for tool in list(tools or ()):
        try:
            text = json.dumps(
                tool,
                ensure_ascii=True,
                separators=(",", ":"),
                allow_nan=False,
            )
        except Exception:
            text = str(tool)
        total += estimate_tokens(text, model=model)
    return max(0, int(total))


def _budget_input_token_upper_bound(
    messages: Sequence[Dict[str, Any]],
    tools: Optional[Sequence[Dict[str, Any]]],
) -> int:
    """Return a tokenizer-independent upper bound for budget admission.

    Provider tokenizers are not always available locally. UTF-8 byte length
    bounds byte-fallback tokenization, while the fixed per-item allowance
    covers provider chat framing that is absent from the serialized payload.
    """

    message_items = list(messages or ())
    tool_items = list(tools or ())
    try:
        payload = json.dumps(
            {"messages": message_items, "tools": tool_items},
            ensure_ascii=False,
            separators=(",", ":"),
            allow_nan=False,
            default=str,
        ).encode("utf-8")
    except Exception:
        payload = repr((message_items, tool_items)).encode(
            "utf-8",
            errors="replace",
        )
    framing_allowance = 32 + 16 * (len(message_items) + len(tool_items))
    return len(payload) + framing_allowance


def _trusted_local_tokenizer_model(model: str, base_url: str) -> str:
    """Resolve a provider-qualified model to a trustworthy local tokenizer."""

    raw_model = str(model or "").strip()
    provider = provider_for_base_url(str(base_url or ""))
    candidate = ""
    if provider == "openai":
        candidate = raw_model.removeprefix("openai/")
    elif provider == "openrouter" and raw_model.startswith("openai/"):
        candidate = raw_model.split("/", 1)[1]
    if not candidate:
        return ""
    try:
        import tiktoken  # type: ignore

        tiktoken.encoding_for_model(candidate)
    except Exception:
        return ""
    return candidate


def _client_model_base(client: Any) -> tuple[str, str]:
    cfg = getattr(client, "cfg", None)
    model = str(
        getattr(client, "last_used_model", "")
        or getattr(cfg, "model", "")
        or ""
    )
    base_url = str(
        getattr(client, "last_used_base_url", "")
        or getattr(client, "base_url", "")
        or getattr(cfg, "base_url", "")
        or ""
    )
    return model, base_url


def _temperature_provider_metadata(client: Any) -> Dict[str, Any]:
    """Best-effort sampling-control metadata from the provider wrapper."""

    out: Dict[str, Any] = {}
    if hasattr(client, "last_temperature_requested"):
        requested = getattr(client, "last_temperature_requested", None)
        if is_api_default_temperature_override(requested):
            out["temperature_requested"] = None
        elif requested is not None:
            out["temperature_requested"] = requested
    for key in (
        "temperature_sent",
        "temperature_provider_dropped",
        "temperature_provider_drop_reason",
        "reasoning_control_requested",
        "reasoning_control_decision",
        "reasoning_control_sent",
        "reasoning_control_required",
        "reasoning_capability_record",
    ):
        attr = f"last_{key}"
        if hasattr(client, attr):
            value = getattr(client, attr, None)
            if key == "temperature_sent" and is_api_default_temperature_override(value):
                value = None
            out[key] = value
    if not out:
        return {}
    if "temperature_provider_dropped" in out:
        out["temperature_provider_dropped"] = bool(
            out.get("temperature_provider_dropped")
        )
    if "temperature_provider_drop_reason" in out:
        out["temperature_provider_drop_reason"] = str(
            out.get("temperature_provider_drop_reason") or ""
        )
    for key in ("reasoning_control_sent", "reasoning_capability_record"):
        if key in out:
            out[key] = dict(out.get(key) or {})
    if "reasoning_control_required" in out:
        out["reasoning_control_required"] = bool(
            out.get("reasoning_control_required")
        )
    for key in ("reasoning_control_requested", "reasoning_control_decision"):
        if key in out:
            out[key] = str(out.get(key) or "")
    return out


def _reservation_pricing_targets(client: Any) -> List[tuple[str, str]]:
    targets: List[tuple[str, str]] = []
    for leaf, fallback_cfg in mini_request_concrete_leaf_bindings(client):
        leaf_cfg = getattr(leaf, "cfg", None) or fallback_cfg
        model = str(
            getattr(leaf, "last_used_model", "")
            or getattr(leaf_cfg, "model", "")
            or ""
        )
        base_url = str(
            getattr(leaf, "last_used_base_url", "")
            or getattr(leaf, "base_url", "")
            or getattr(leaf_cfg, "base_url", "")
            or ""
        )
        targets.append((model, base_url))
    return targets


async def _request_envelope_receipts(
    client: Any,
    max_tokens_override: Any,
) -> List[MiniRequestEnvelopeReceipt]:
    if not isinstance(max_tokens_override, MiniRequestEnvelopePolicy):
        return []
    return await resolve_mini_request_envelopes(client, max_tokens_override)


def reservation_pricing_targets(client: Any) -> tuple[tuple[str, str], ...]:
    """Return every concrete model/provider leaf that a client may charge."""
    return tuple(_reservation_pricing_targets(client))


def _reservation_cost_aggregation(client: Any) -> str:
    if isinstance(getattr(client, "members", None), list):
        return "sum"
    if isinstance(getattr(client, "clients", None), list):
        return "sum"
    return "sum"


def _cfg_waits_for_provider_after_local_cancel(cfg: Any) -> bool:
    policy = (
        str(getattr(cfg, "llm_deadline_policy", "hard") or "hard")
        .strip()
        .lower()
    )
    return policy == "soft" or bool(getattr(cfg, "request_timeout_disabled", False))


def _client_waits_for_provider_after_local_cancel(client: Any) -> bool:
    return any(
        cfg is not None and _cfg_waits_for_provider_after_local_cancel(cfg)
        for _leaf, cfg in mini_request_concrete_leaf_bindings(client)
    )


def _client_tree_has_pool(client: Any) -> bool:
    active: set[int] = set()

    def visit(node: Any) -> bool:
        node_id = id(node)
        if node_id in active:
            raise RuntimeError("model wrapper cycle in LLM reservation topology")
        members = getattr(node, "members", None)
        if isinstance(members, list) and members:
            return True
        children = mini_request_wrapper_children(node)
        if not children:
            return False
        active.add(node_id)
        try:
            return any(visit(child) for child in children)
        finally:
            active.remove(node_id)

    return visit(client)


def _candidate_output_multipliers(
    client: Any,
    *,
    target_count: int,
    candidate_count: int,
    call_kind: str,
) -> List[int]:
    if target_count <= 0:
        return []
    if "chat_n" in str(call_kind or ""):
        candidate_count = max(1, int(candidate_count or 1))
        allocator = getattr(client, "_allocate_n", None)
        if callable(allocator):
            try:
                allocations = [max(0, int(v)) for v in list(allocator(candidate_count))]
            except Exception:
                allocations = []
            if len(allocations) == target_count:
                return allocations
        return [candidate_count for _ in range(target_count)]
    candidate_count = max(1, int(candidate_count or 1))
    return [1 for _ in range(target_count)]


def _require_reservation_multiplier_count(
    values: Sequence[Any],
    *,
    target_count: int,
    attribute: str,
) -> List[int]:
    """Reject ambiguous wrapper surfaces instead of inventing leaf defaults."""

    multipliers = list(values)
    expected = max(0, int(target_count or 0))
    if len(multipliers) != expected:
        raise RuntimeError(
            f"{attribute} returned {len(multipliers)} values for "
            f"{expected} concrete pricing targets"
        )
    if any(
        isinstance(value, bool)
        or not isinstance(value, Integral)
        or int(value) < 0
        for value in multipliers
    ):
        raise RuntimeError(
            f"{attribute} must return non-negative integer values"
        )
    return [int(value) for value in multipliers]


def _require_reservation_attempt_multiplier(value: Any) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, Integral)
        or int(value) <= 0
    ):
        raise RuntimeError(
            "reservation_attempt_multiplier must return a positive integer"
        )
    return int(value)


def _reservation_attempt_multipliers(
    client: Any,
    *,
    target_count: int,
    call_kind: str,
) -> List[int]:
    """Resolve one exact retry multiplier for every concrete pricing leaf."""

    attempt_multipliers_fn = getattr(
        client,
        "reservation_attempt_multipliers",
        None,
    )
    if callable(attempt_multipliers_fn):
        multipliers = _require_reservation_multiplier_count(
            attempt_multipliers_fn(target_count, call_kind),
            target_count=target_count,
            attribute="reservation_attempt_multipliers",
        )
        if any(value <= 0 for value in multipliers):
            raise RuntimeError(
                "reservation_attempt_multipliers must return positive "
                "integer values"
            )
        return multipliers
    attempt_multiplier_fn = getattr(
        client,
        "reservation_attempt_multiplier",
        None,
    )
    multiplier = _require_reservation_attempt_multiplier(
        attempt_multiplier_fn(call_kind)
        if callable(attempt_multiplier_fn)
        else 1
    )
    return [multiplier for _ in range(max(0, int(target_count or 0)))]


def cost_for_record(record: ProviderUsageRecord) -> tuple[float, bool]:
    if (
        record.reported_cost_usd is not None
        and provider_for_base_url(record.base_url) == "openrouter"
    ):
        return float(record.reported_cost_usd), True
    cost = compute_model_cost_usd(
        record.base_url,
        record.model,
        input_tokens=record.input_tokens,
        output_tokens=record.output_tokens,
        cached_input_tokens=record.cached_input_tokens,
        cache_write_tokens=record.cache_write_tokens,
    )
    if cost is None:
        return 0.0, False
    return (cost, True)


def _canonical_usage_role(role: str) -> str:
    text = str(role or "").strip()
    mapping = {
        "prove": "prover",
        "refine": "refiner",
    }
    return mapping.get(text, text or "llm")


class CostBudgetController:
    """Shared MiniSession cost meter and optional dollar-budget guard."""

    def __init__(
        self,
        *,
        max_cost_usd: float = 0.0,
        reserve_output_tokens: int = 1024,
        event_sink: Optional[Callable[[Dict[str, Any]], Any]] = None,
    ) -> None:
        self.max_cost_usd = max(0.0, float(max_cost_usd or 0.0))
        self.reserve_output_tokens = max(0, int(reserve_output_tokens or 0))
        self.event_sink = event_sink
        self._lock = asyncio.Lock()
        self._exact_cost_usd = 0.0
        self._unknown_cost_usd = 0.0
        self._input_tokens = 0
        self._output_tokens = 0
        self._cached_input_tokens = 0
        self._cache_write_tokens = 0
        self._prompt_cache_miss_tokens = 0
        self._reasoning_output_tokens = 0
        self._events = 0
        self._usage_missing_events = 0
        self._pricing_unknown_events = 0
        self._cancelled_provider_inflight_events = 0
        self._cancelled_provider_inflight_estimated_cost_usd = 0.0
        self._cancelled_provider_inflight_reservations: set[str] = set()
        self._cancelled_provider_inflight_cost_by_reservation: Dict[str, float] = {}
        self._cancelled_provider_inflight_target_costs: Dict[
            str, Dict[str, float]
        ] = {}
        self._retryable_exception_no_charge_events = 0
        self._reservations = 0
        self._reserved_cost_usd = 0.0
        self._active_reservations: Dict[str, float] = {}
        self._late_usage_receipts: Dict[str, Dict[str, Any]] = {}
        self._reservation_missing_unknown_cost_usd: Dict[str, float] = {}
        self._reservation_missing_target_costs: Dict[str, Dict[str, float]] = {}
        self._reservation_pricing_unknown_cost_usd: Dict[str, float] = {}
        self._reservation_pricing_unknown_target_costs: Dict[
            str,
            Dict[str, float],
        ] = {}
        self._reservation_unknown_role: Dict[str, str] = {}
        self._late_hold_reservations: set[str] = set()
        self._budget_rejections = 0
        self._terminal_reason = ""
        self._role_totals: Dict[str, Dict[str, Any]] = {}
        self._pending_late_usage_tasks: set[asyncio.Task] = set()
        self._final_accounting_frozen = False

    @property
    def budget_enabled(self) -> bool:
        return self.max_cost_usd > 0.0

    @property
    def accounted_cost_usd(self) -> float:
        return float(self._exact_cost_usd + self._unknown_cost_usd)

    @property
    def reserved_cost_usd(self) -> float:
        return float(self._reserved_cost_usd)

    def _reservation_accounted_exposure(self, reservation_id: str) -> float:
        missing = max(
            0.0,
            float(
                self._reservation_missing_unknown_cost_usd.get(
                    reservation_id,
                    0.0,
                )
                or 0.0
            ),
        )
        pricing = max(
            0.0,
            float(
                self._reservation_pricing_unknown_cost_usd.get(
                    reservation_id,
                    0.0,
                )
                or 0.0
            ),
        )
        missing_targets = self._reservation_missing_target_costs.get(
            reservation_id,
            {},
        )
        pricing_targets = self._reservation_pricing_unknown_target_costs.get(
            reservation_id,
            {},
        )
        if pricing_targets:
            return sum(
                max(0.0, float(value or 0.0))
                for value in missing_targets.values()
            ) + sum(
                max(0.0, float(value or 0.0))
                for value in pricing_targets.values()
            )
        return max(missing, pricing)

    @property
    def committed_cost_usd(self) -> float:
        accounted_hold_overlap = sum(
            min(
                max(0.0, float(held_cost or 0.0)),
                max(
                    0.0,
                    self._reservation_accounted_exposure(reservation_id),
                ),
            )
            for reservation_id, held_cost in self._active_reservations.items()
        )
        return float(
            self.accounted_cost_usd
            + self.reserved_cost_usd
            - accounted_hold_overlap
        )

    @property
    def terminal_reason(self) -> str:
        return self._terminal_reason

    def _refresh_terminal_reason_locked(self) -> None:
        if not self.budget_enabled:
            self._terminal_reason = ""
            return
        if self._terminal_reason == "llm_cost_budget_unknown_pricing":
            return
        if self.accounted_cost_usd >= self.max_cost_usd:
            self._terminal_reason = "llm_cost_budget_exhausted"
        elif self._terminal_reason == "llm_cost_budget_exhausted":
            self._terminal_reason = ""

    def exhausted(self) -> bool:
        if not self.budget_enabled:
            return False
        if str(self._terminal_reason or "").strip() in {
            "llm_cost_budget_exhausted",
            "llm_cost_budget_unknown_pricing",
        }:
            return True
        return bool(self.accounted_cost_usd >= self.max_cost_usd)

    def remaining_usd(self) -> Optional[float]:
        if not self.budget_enabled:
            return None
        if self.exhausted():
            return 0.0
        return max(0.0, self.max_cost_usd - self.committed_cost_usd)

    def request_output_capacity_available(
        self,
        *,
        client: Any,
        call_kind: str,
        max_tokens_override: Optional[int] = None,
        candidate_count: int = 1,
    ) -> bool:
        """Whether even a zero-input reservation can fit the current budget.

        This is a side-effect-free lower-bound admission probe for schedulers.
        It deliberately ignores prompt cost: ``False`` is therefore
        authoritative, while ``True`` only means the real reservation still
        has a chance to fit once its prompt is known.  Unknown pricing fails
        open so the normal asynchronous reservation remains authoritative.
        """

        if not self.budget_enabled:
            return True
        if isinstance(max_tokens_override, MiniRequestEnvelopePolicy):
            # Capability discovery and concrete-leaf resolution are async and
            # belong at authoritative reservation time.  This synchronous
            # lower-bound probe must fail open rather than either coercing an
            # unresolved policy or broadcasting one sibling's cap.
            return True
        cfg_max_tokens = getattr(getattr(client, "cfg", None), "max_tokens", None)
        if max_tokens_override is not None:
            reserved_output_tokens = max(0, int(max_tokens_override or 0))
        elif cfg_max_tokens is not None:
            reserved_output_tokens = max(
                0,
                min(int(cfg_max_tokens or 0), int(self.reserve_output_tokens or 0))
                if self.reserve_output_tokens > 0
                else int(cfg_max_tokens or 0),
            )
        else:
            reserved_output_tokens = int(self.reserve_output_tokens or 0)
        targets = _reservation_pricing_targets(client)
        multipliers = _candidate_output_multipliers(
            client,
            target_count=len(targets),
            candidate_count=candidate_count,
            call_kind=call_kind,
        )
        output_multiplier_fn = getattr(
            client,
            "reservation_output_multipliers",
            None,
        )
        if callable(output_multiplier_fn):
            multipliers = _require_reservation_multiplier_count(
                output_multiplier_fn(candidate_count, len(targets), call_kind),
                target_count=len(targets),
                attribute="reservation_output_multipliers",
            )
        attempt_multipliers = _reservation_attempt_multipliers(
            client,
            target_count=len(targets),
            call_kind=call_kind,
        )
        model_costs: List[float] = []
        for index, (model, base_url) in enumerate(targets):
            output_multiplier = multipliers[index]
            attempt_multiplier = attempt_multipliers[index]
            pricing = conservative_reservation_token_pricing(
                base_url,
                model,
                input_tokens=0,
            )
            if pricing is None:
                return True
            _input_per_m, _cached_per_m, output_per_m = pricing
            model_costs.append(
                reserved_output_tokens
                * max(0, output_multiplier)
                * attempt_multiplier
                * output_per_m
                / 1_000_000
            )
        minimum_cost = (
            max(model_costs, default=0.0)
            if _reservation_cost_aggregation(client) == "max"
            else sum(model_costs)
        )
        return self.committed_cost_usd + minimum_cost <= self.max_cost_usd

    def unspent_usd(self) -> Optional[float]:
        """Financially unspent budget, independent of terminal availability."""
        if not self.budget_enabled:
            return None
        return max(0.0, self.max_cost_usd - self.committed_cost_usd)

    async def reserve(
        self,
        *,
        client: Any,
        messages: Sequence[Dict[str, Any]],
        role: str,
        scope: str,
        action_id: str = "",
        call_kind: str,
        tools: Optional[Sequence[Dict[str, Any]]] = None,
        max_tokens_override: Any = None,
        candidate_count: int = 1,
        metadata: Optional[Mapping[str, Any]] = None,
    ) -> CostReservation:
        # Bind at the reservation boundary, not only in the convenience
        # wrapper.  This keeps direct controller.metered_call users and future
        # call sites inside the same dispatch-lineage contract.
        metadata = dict(llm_usage_context_metadata(metadata))
        targets = _reservation_pricing_targets(client)
        envelope_receipts = await _request_envelope_receipts(
            client,
            max_tokens_override,
        )
        if envelope_receipts:
            if len(envelope_receipts) != len(targets):
                raise RuntimeError(
                    "Mini request envelope leaf count does not match pricing targets"
                )
            metadata["mini_request_envelopes"] = [
                receipt.to_record() for receipt in envelope_receipts
            ]
        if not targets:
            targets = [_client_model_base(client)]
        budget_input_upper_bound = (
            _budget_input_token_upper_bound(messages, tools)
            if self.budget_enabled
            else 0
        )
        estimated_input_tokens_by_target: List[int] = []
        for model, base_url in targets:
            tokenizer_model = _trusted_local_tokenizer_model(model, base_url)
            target_estimate = estimate_messages_tokens(
                messages,
                model=tokenizer_model or model,
                tools=tools,
            )
            if self.budget_enabled and not tokenizer_model:
                # A hard dollar ceiling needs a tokenizer-independent bound
                # for each reachable provider leaf whose tokenizer is not
                # locally authoritative. Known leaves retain tight estimates.
                target_estimate = max(
                    target_estimate,
                    budget_input_upper_bound,
                )
            estimated_input_tokens_by_target.append(target_estimate)
        estimated_input_tokens = max(
            estimated_input_tokens_by_target,
            default=0,
        )
        cfg_max_tokens = getattr(getattr(client, "cfg", None), "max_tokens", None)
        if envelope_receipts:
            reserved_output_tokens_by_target = [
                max(0, int(receipt.max_output_tokens))
                for receipt in envelope_receipts
            ]
            reserved_output_tokens = max(
                reserved_output_tokens_by_target,
                default=0,
            )
        elif max_tokens_override is not None:
            reserved_output_tokens = max(0, int(max_tokens_override or 0))
            reserved_output_tokens_by_target = [
                reserved_output_tokens for _ in targets
            ]
        elif cfg_max_tokens is not None:
            reserved_output_tokens = max(
                0,
                min(int(cfg_max_tokens or 0), int(self.reserve_output_tokens or 0))
                if self.reserve_output_tokens > 0
                else int(cfg_max_tokens or 0),
            )
            reserved_output_tokens_by_target = [
                reserved_output_tokens for _ in targets
            ]
        else:
            reserved_output_tokens = int(self.reserve_output_tokens or 0)
            reserved_output_tokens_by_target = [
                reserved_output_tokens for _ in targets
            ]

        multipliers = _candidate_output_multipliers(
            client,
            target_count=len(targets),
            candidate_count=candidate_count,
            call_kind=call_kind,
        )
        output_multiplier_fn = getattr(
            client,
            "reservation_output_multipliers",
            None,
        )
        if callable(output_multiplier_fn):
            multipliers = _require_reservation_multiplier_count(
                output_multiplier_fn(candidate_count, len(targets), call_kind),
                target_count=len(targets),
                attribute="reservation_output_multipliers",
            )
        prompt_multiplier_fn = getattr(
            client,
            "reservation_prompt_multipliers",
            None,
        )
        prompt_multipliers = _require_reservation_multiplier_count(
            prompt_multiplier_fn(candidate_count, len(targets), call_kind)
            if callable(prompt_multiplier_fn)
            else multipliers,
            target_count=len(targets),
            attribute="reservation_prompt_multipliers",
        )
        attempt_multipliers = _reservation_attempt_multipliers(
            client,
            target_count=len(targets),
            call_kind=call_kind,
        )
        aggregation = _reservation_cost_aggregation(client)
        call_kind_text = str(call_kind or "")
        hold_for_late_usage = (
            _client_tree_has_pool(client) and "chat_n" not in call_kind_text
        )
        model_costs: List[float] = []
        estimated_models: List[Dict[str, Any]] = []
        unknown_pricing = False
        for index, (model, base_url) in enumerate(targets):
            model_cost = 0.0
            dispatch_cost = 0.0
            output_multiplier = multipliers[index]
            prompt_multiplier = prompt_multipliers[index]
            attempt_multiplier = attempt_multipliers[index]
            target_estimated_input_tokens = estimated_input_tokens_by_target[index]
            leaf_output_tokens = (
                reserved_output_tokens_by_target[index]
                if index < len(reserved_output_tokens_by_target)
                else reserved_output_tokens
            )
            target_output_tokens = (
                leaf_output_tokens
                * max(0, output_multiplier)
                * attempt_multiplier
            )
            if output_multiplier <= 0:
                target_input_tokens = 0
            elif "chat_n" in call_kind_text:
                target_input_tokens = (
                    target_estimated_input_tokens
                    * max(1, prompt_multiplier)
                    * attempt_multiplier
                )
            else:
                target_input_tokens = (
                    target_estimated_input_tokens * attempt_multiplier
                )
            pricing_input_tokens = (
                target_estimated_input_tokens if output_multiplier > 0 else 0
            )
            pricing = (
                await conservative_reservation_token_pricing_async(
                    base_url,
                    model,
                    input_tokens=pricing_input_tokens,
                )
                if self.budget_enabled
                else conservative_reservation_token_pricing(
                    base_url,
                    model,
                    input_tokens=pricing_input_tokens,
                )
            )
            target_active = target_input_tokens > 0 or target_output_tokens > 0
            if pricing is None and target_active:
                unknown_pricing = True
            elif pricing is not None:
                input_per_m, _cached_per_m, output_per_m = pricing
                dispatch_input_cost = (
                    target_estimated_input_tokens * input_per_m / 1_000_000
                )
                dispatch_output_cost = (
                    leaf_output_tokens * output_per_m / 1_000_000
                )
                model_cost = (
                    target_input_tokens * input_per_m / 1_000_000
                    + target_output_tokens * output_per_m / 1_000_000
                )
                dispatch_output_tokens = leaf_output_tokens * max(
                    1,
                    output_multiplier if "chat_n" in call_kind_text else 1,
                )
                dispatch_cost = (
                    dispatch_input_cost
                    + dispatch_output_tokens * output_per_m / 1_000_000
                )
                model_costs.append(model_cost)
            estimated_models.append(
                {
                    "target_id": f"target:{index}",
                    "model": model,
                    "base_url": base_url,
                    "pricing_known": pricing is not None,
                    "reservation_active": target_active,
                    "estimated_cost_usd": model_cost,
                    "estimated_dispatch_cost_usd": dispatch_cost,
                    "estimated_dispatch_input_cost_usd": (
                        dispatch_input_cost if pricing is not None else 0.0
                    ),
                    "estimated_dispatch_output_cost_usd": (
                        dispatch_output_cost if pricing is not None else 0.0
                    ),
                    "reserved_input_tokens": target_input_tokens,
                    "pricing_input_tokens": pricing_input_tokens,
                    "reserved_output_tokens": target_output_tokens,
                    "request_output_tokens": leaf_output_tokens,
                    "candidate_output_multiplier": output_multiplier,
                    "provider_prompt_multiplier": prompt_multiplier,
                    "provider_attempt_multiplier": attempt_multiplier,
                }
            )
        if aggregation == "max":
            estimated_cost = max(model_costs, default=0.0)
        else:
            estimated_cost = sum(model_costs)
        dispatch_attempt_limit = max(
            0,
            int(metadata.get("provider_dispatch_max_attempts", 0) or 0),
        )
        if (
            dispatch_attempt_limit
            and aggregation == "sum"
            and bool(
                getattr(
                    client,
                    "supports_transport_dispatch_authorization",
                    False,
                )
            )
        ):
            # The transport observer below enforces one ceiling across every
            # retry/fallback/pool target.  Admission must reserve the same
            # reachable exposure surface, not all leaves times all wrapper
            # retries.  The N most expensive individual dispatches are a safe
            # upper bound for any N concrete transports; per-target records
            # remain intact for exact settlement and late-usage correlation.
            # Opaque clients cannot prove that ceiling at the provider
            # boundary, so they deliberately retain the full reservation.
            possible_dispatch_costs: List[float] = []
            for item in estimated_models:
                per_dispatch_cost = max(
                    0.0,
                    float(item.get("estimated_dispatch_cost_usd", 0.0) or 0.0),
                )
                possible_dispatch_costs.extend(
                    [per_dispatch_cost]
                    * max(1, int(item.get("provider_attempt_multiplier", 1) or 1))
                )
            capped_estimated_cost = sum(
                sorted(possible_dispatch_costs, reverse=True)[
                    :dispatch_attempt_limit
                ]
            )
            if capped_estimated_cost + 1e-12 < estimated_cost:
                metadata.update(
                    {
                        "provider_dispatch_reservation_capped": True,
                        "provider_dispatch_uncapped_estimated_cost_usd": (
                            estimated_cost
                        ),
                        "provider_dispatch_capped_estimated_cost_usd": (
                            capped_estimated_cost
                        ),
                    }
                )
                estimated_cost = capped_estimated_cost

        # Reservation metadata is live, in-process state.  Keep the mapping
        # independent from its caller without imposing a serialization gate
        # on provider work; individual values may intentionally be opaque.
        reservation_metadata = dict(metadata or {})
        reservation_estimated_models = [dict(item) for item in estimated_models]
        reservation_id = uuid.uuid4().hex
        request_id = uuid.uuid4().hex
        async with self._lock:
            if self._final_accounting_frozen:
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=estimated_cost,
                    reason="llm_final_accounting_frozen",
                )
            if self.budget_enabled and self.exhausted():
                reason = self._terminal_reason or "llm_cost_budget_exhausted"
                if not self._terminal_reason:
                    self._terminal_reason = reason
                self._budget_rejections += 1
                await self._record_event_locked(
                    {
                        "phase": "llm_usage",
                        "verdict": "cost_budget_rejected",
                        "budget_rejection_reason": reason,
                        "budget_rejection_terminal": True,
                        "role": role,
                        "session_scope": scope,
                        "action_id": action_id,
                        "call_kind": call_kind,
                        "max_cost_usd": self.max_cost_usd,
                        "cost_usd": self._exact_cost_usd,
                        "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                        "llm_budget_committed_cost_usd": self.committed_cost_usd,
                        "estimated_cost_usd": estimated_cost,
                        "estimated_models": estimated_models,
                        **dict(metadata or {}),
                    }
                )
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=estimated_cost,
                    reason=reason,
                )
            if self.budget_enabled and unknown_pricing:
                self._budget_rejections += 1
                self._terminal_reason = "llm_cost_budget_unknown_pricing"
                await self._record_event_locked(
                    {
                        "phase": "llm_usage",
                        "verdict": "cost_budget_rejected",
                        "budget_rejection_reason": "unknown_pricing",
                        "role": role,
                        "session_scope": scope,
                        "action_id": action_id,
                        "call_kind": call_kind,
                        "budget_rejection_terminal": True,
                        "max_cost_usd": self.max_cost_usd,
                        "cost_usd": self._exact_cost_usd,
                        "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                        "llm_budget_committed_cost_usd": self.committed_cost_usd,
                        "estimated_cost_usd": estimated_cost,
                        "estimated_models": estimated_models,
                        **dict(metadata or {}),
                    }
                )
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=estimated_cost,
                    reason="llm_cost_budget_unknown_pricing",
                )
            if (
                self.budget_enabled
                and self.committed_cost_usd + estimated_cost > self.max_cost_usd
            ):
                self._budget_rejections += 1
                temporary_capacity = self._reserved_cost_usd > 0.0
                rejection_reason = (
                    "llm_cost_budget_reserved_capacity"
                    if temporary_capacity
                    else "llm_cost_budget_request_capacity"
                )
                await self._record_event_locked(
                    {
                        "phase": "llm_usage",
                        "verdict": "cost_budget_rejected",
                        "budget_rejection_reason": rejection_reason,
                        # One request being too expensive does not prove that
                        # the budget is globally exhausted. A cheaper model,
                        # phase, or static lane may still fit. Actual terminal
                        # exhaustion is established by ``exhausted()`` from
                        # accounted cost, never by this admission comparison.
                        "budget_rejection_terminal": False,
                        "role": role,
                        "session_scope": scope,
                        "action_id": action_id,
                        "call_kind": call_kind,
                        "max_cost_usd": self.max_cost_usd,
                        "cost_usd": self._exact_cost_usd,
                        "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                        "llm_budget_committed_cost_usd": self.committed_cost_usd,
                        "estimated_cost_usd": estimated_cost,
                        "estimated_models": estimated_models,
                        **dict(metadata or {}),
                    }
                )
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=estimated_cost,
                    reason=rejection_reason,
                )
            self._reservations += 1
            self._reserved_cost_usd += estimated_cost
            self._active_reservations[reservation_id] = estimated_cost

        return CostReservation(
            reservation_id=reservation_id,
            request_id=request_id,
            role=str(role or ""),
            scope=str(scope or ""),
            action_id=str(action_id or ""),
            call_kind=str(call_kind or ""),
            estimated_input_tokens=estimated_input_tokens,
            reserved_output_tokens=reserved_output_tokens,
            estimated_cost_usd=estimated_cost,
            estimated_models=reservation_estimated_models,
            metadata=reservation_metadata,
            hold_for_late_usage=hold_for_late_usage,
        )

    async def authorize_provider_retry_dispatch(
        self,
        reservation: CostReservation,
        *,
        target_id: str,
        dispatch_ordinal: int,
        requested_cost_usd: Optional[float] = None,
    ) -> None:
        """Extend a live hold before one unreserved provider retry.

        Every transport retry is another possible billable generation. Calls
        with a very large output capability may reserve one useful attempt up
        front, but a later retry cannot cross the HTTP boundary until its own
        worst-case dispatch cost is held. Denial is scoped to this retry so a
        cheaper fallback may still consume the remaining session budget.
        """

        clean_target = str(target_id or "")
        default_cost = next(
            (
                max(
                    0.0,
                    float(item.get("estimated_dispatch_cost_usd", 0.0) or 0.0),
                )
                for item in reservation.estimated_models
                if str(item.get("target_id") or "") == clean_target
            ),
            0.0,
        )
        unit_cost = (
            max(0.0, float(requested_cost_usd or 0.0))
            if requested_cost_usd is not None
            else default_cost
        )
        def record_authorized_retry() -> None:
            metadata = reservation.metadata
            if not isinstance(metadata, dict):
                return
            authorized = dict(
                metadata.get("llm_retry_authorized_target_counts") or {}
            )
            authorized[clean_target] = (
                int(authorized.get(clean_target, 0) or 0) + 1
            )
            metadata["llm_retry_authorized_target_counts"] = authorized

        if unit_cost <= 0.0 or not self.budget_enabled:
            record_authorized_retry()
            return
        async with self._lock:
            if self._final_accounting_frozen:
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=unit_cost,
                    reason="llm_final_accounting_frozen",
                )
            if reservation.reservation_id not in self._active_reservations:
                raise RuntimeError(
                    "cannot authorize a provider retry for an inactive "
                    f"reservation: {reservation.reservation_id}"
                )
            if self.committed_cost_usd + unit_cost > self.max_cost_usd:
                self._budget_rejections += 1
                await self._record_event_locked(
                    {
                        "phase": "llm_usage",
                        "verdict": "provider_retry_budget_rejected",
                        "budget_rejection_reason": "llm_cost_budget_retry_capacity",
                        "budget_rejection_terminal": False,
                        "role": reservation.role,
                        "session_scope": reservation.scope,
                        "action_id": reservation.action_id,
                        "call_kind": reservation.call_kind,
                        "llm_request_id": reservation.request_id,
                        "llm_reservation_id": reservation.reservation_id,
                        "target_id": clean_target,
                        "reservation_dispatch_ordinal": max(
                            0, int(dispatch_ordinal or 0)
                        ),
                        "max_cost_usd": self.max_cost_usd,
                        "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                        "llm_budget_committed_cost_usd": self.committed_cost_usd,
                        "estimated_retry_dispatch_cost_usd": unit_cost,
                        **_reservation_usage_event_metadata(reservation),
                    }
                )
                raise CostBudgetExceeded(
                    max_cost_usd=self.max_cost_usd,
                    accounted_cost_usd=self.accounted_cost_usd,
                    requested_cost_usd=unit_cost,
                    reason="llm_cost_budget_retry_capacity",
                )
            self._reserved_cost_usd += unit_cost
            self._active_reservations[reservation.reservation_id] = (
                max(
                    0.0,
                    float(
                        self._active_reservations.get(
                            reservation.reservation_id, 0.0
                        )
                        or 0.0
                    ),
                )
                + unit_cost
            )
            record_authorized_retry()
            await self._record_event_locked(
                {
                    "phase": "llm_usage",
                    "verdict": "provider_retry_budget_authorized",
                    "role": reservation.role,
                    "session_scope": reservation.scope,
                    "action_id": reservation.action_id,
                    "call_kind": reservation.call_kind,
                    "llm_request_id": reservation.request_id,
                    "llm_reservation_id": reservation.reservation_id,
                    "target_id": clean_target,
                    "reservation_dispatch_ordinal": max(
                        0, int(dispatch_ordinal or 0)
                    ),
                    "estimated_retry_dispatch_cost_usd": unit_cost,
                    "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                    "llm_budget_committed_cost_usd": self.committed_cost_usd,
                    **_reservation_usage_event_metadata(reservation),
                }
            )

    async def settle(
        self,
        reservation: CostReservation,
        observations: Sequence[ProviderUsageRecord],
        *,
        status: str,
        error: str = "",
    ) -> None:
        await self._settle_observations(
            reservation,
            observations,
            status=status,
            error=error,
            release_reservation=True,
            late=False,
        )

    async def record_late_usage(
        self,
        reservation: CostReservation,
        record: ProviderUsageRecord,
        *,
        retire_cancelled_exposure: bool = True,
    ) -> None:
        await self._settle_observations(
            reservation,
            [record],
            status="late_usage",
            error="",
            release_reservation=False,
            late=True,
            retire_cancelled_exposure=retire_cancelled_exposure,
        )

    async def record_late_dispatch(
        self,
        reservation: CostReservation,
        target_id: str,
        *,
        estimated_dispatch_cost_usd: Optional[float] = None,
    ) -> None:
        """Conservatively account a provider dispatch after initial settlement."""
        clean_target = str(target_id or "")
        if estimated_dispatch_cost_usd is not None:
            target_cost = max(0.0, float(estimated_dispatch_cost_usd or 0.0))
        else:
            target_cost = next(
            (
                max(0.0, float(item.get("estimated_cost_usd", 0.0) or 0.0))
                for item in reservation.estimated_models
                if str(item.get("target_id") or "") == clean_target
            ),
            float(reservation.estimated_cost_usd or 0.0),
        )
            target_cost = next(
                (
                    max(
                        0.0,
                        float(
                            item.get("estimated_dispatch_cost_usd", target_cost)
                            or 0.0
                        ),
                    )
                    for item in reservation.estimated_models
                    if str(item.get("target_id") or "") == clean_target
                ),
                target_cost,
            )
        role_key = _canonical_usage_role(reservation.role)
        async with self._lock:
            if self._final_accounting_frozen:
                return
            self._events += 1
            self._usage_missing_events += 1
            unknown_added = target_cost if self.budget_enabled else 0.0
            if unknown_added > 0.0:
                target_costs = self._reservation_missing_target_costs.setdefault(
                    reservation.reservation_id,
                    {},
                )
                target_costs[clean_target] = (
                    float(target_costs.get(clean_target, 0.0) or 0.0)
                    + unknown_added
                )
                aggregate = sum(target_costs.values())
                prior_aggregate = float(
                    self._reservation_missing_unknown_cost_usd.get(
                        reservation.reservation_id,
                        0.0,
                    )
                    or 0.0
                )
                self._reservation_missing_unknown_cost_usd[
                    reservation.reservation_id
                ] = aggregate
                self._reservation_unknown_role[reservation.reservation_id] = role_key
                delta = max(0.0, aggregate - prior_aggregate)
                self._unknown_cost_usd += delta
                role_totals = self._role_totals.setdefault(
                    role_key,
                    {
                        "input_tokens": 0,
                        "output_tokens": 0,
                        "cached_input_tokens": 0,
                        "cache_write_tokens": 0,
                        "prompt_cache_miss_tokens": 0,
                        "reasoning_output_tokens": 0,
                        "cost_usd": 0.0,
                        "estimated_unknown_cost_usd": 0.0,
                        "model": "",
                    },
                )
                role_totals["estimated_unknown_cost_usd"] = float(
                    role_totals.get("estimated_unknown_cost_usd", 0.0) or 0.0
                ) + delta
                self._refresh_terminal_reason_locked()
            event = {
                    "phase": "llm_usage",
                    "verdict": "llm_late_dispatch_missing_usage",
                    "status": "late_dispatch",
                    "llm_request_id": reservation.request_id,
                    "llm_reservation_id": reservation.reservation_id,
                    "role": reservation.role,
                    "session_scope": reservation.scope,
                    "action_id": reservation.action_id,
                    "call_kind": reservation.call_kind,
                    "late_usage": True,
                    "usage_missing": True,
                    "missing_provider_target_ids": [clean_target],
                    "estimated_unknown_cost_usd": unknown_added,
                    "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                    "llm_budget_committed_cost_usd": self.committed_cost_usd,
                }
            event.update(_reservation_usage_event_metadata(reservation))
            await self._record_event_locked(event)

    def _reverse_cancelled_exposure_locked(
        self,
        reservation_id: str,
        amount: float,
        *,
        target_id: str = "",
    ) -> float:
        """Reverse only exposure owned by the correlated reservation."""

        current = max(
            0.0,
            float(
                self._cancelled_provider_inflight_cost_by_reservation.get(
                    reservation_id,
                    0.0,
                )
                or 0.0
            ),
        )
        target_costs = self._cancelled_provider_inflight_target_costs.get(
            reservation_id
        )
        clean_target = str(target_id or "")
        if target_costs is not None:
            if not clean_target and len(target_costs) == 1:
                clean_target = next(iter(target_costs))
            target_current = max(
                0.0,
                float(target_costs.get(clean_target, 0.0) or 0.0),
            )
            reversed_cost = min(
                target_current,
                max(0.0, float(amount or 0.0)),
            )
        else:
            reversed_cost = min(current, max(0.0, float(amount or 0.0)))
        if reversed_cost <= 0.0:
            return 0.0
        remaining = current - reversed_cost
        if target_costs is not None:
            target_remaining = max(
                0.0,
                float(target_costs.get(clean_target, 0.0) or 0.0)
                - reversed_cost,
            )
            if target_remaining > 0.0:
                target_costs[clean_target] = target_remaining
            else:
                target_costs.pop(clean_target, None)
            if target_costs:
                self._cancelled_provider_inflight_target_costs[
                    reservation_id
                ] = target_costs
            else:
                self._cancelled_provider_inflight_target_costs.pop(
                    reservation_id,
                    None,
                )
        if remaining > 0.0:
            self._cancelled_provider_inflight_cost_by_reservation[
                reservation_id
            ] = remaining
        else:
            self._cancelled_provider_inflight_cost_by_reservation.pop(
                reservation_id,
                None,
            )
        self._cancelled_provider_inflight_estimated_cost_usd = max(
            0.0,
            self._cancelled_provider_inflight_estimated_cost_usd - reversed_cost,
        )
        return reversed_cost

    def _reverse_late_unknown_locked(
        self,
        reservation_id: str,
        amount: float,
        *,
        target_id: str = "",
        receipt_id: str = "",
        receipt_record: Optional[Mapping[str, Any]] = None,
    ) -> tuple[float, bool]:
        """Retire live unknown exposure using a correlated late receipt.

        Returns ``(reversed_cost, duplicate_receipt)``. Receipt fingerprints
        remain on a zero-cost tombstone so replaying the same late callback
        after another callback cannot add exact cost twice.
        """

        receipt = self._late_usage_receipts.get(reservation_id)
        if not isinstance(receipt, dict):
            # The receipt ledger is occurrence authority for *all* provider
            # dispatches, not only previously unknown exposure. A zero-cost
            # tombstone lets the same process deduplicate repeated late
            # callbacks for this concrete dispatch.
            receipt = {
                "cost_usd": 0.0,
                "role": _canonical_usage_role(
                    str(dict(receipt_record or {}).get("role") or "unknown")
                ),
            }
        applied_receipts = dict(receipt.get("applied_receipts") or {})
        applied = {
            str(value)
            for value in list(receipt.get("applied_receipt_ids") or ())
            if str(value)
        } | {str(value) for value in applied_receipts}
        if receipt_id and receipt_id in applied:
            existing_record = applied_receipts.get(receipt_id)
            if existing_record is not None and receipt_record is not None:
                accounting_keys = {
                    "kind",
                    "role",
                    "target_id",
                    "dispatch_ordinal",
                    "model",
                    "status_code",
                    "input_tokens",
                    "output_tokens",
                    "cached_input_tokens",
                    "cache_write_tokens",
                    "prompt_cache_miss_tokens",
                    "reasoning_output_tokens",
                    "cost_usd",
                }
                existing_signature = {
                    key: existing_record.get(key)
                    for key in accounting_keys
                    if key in existing_record
                }
                incoming_signature = {
                    key: receipt_record.get(key)
                    for key in accounting_keys
                    if key in receipt_record
                }
                if existing_signature != incoming_signature:
                    raise ValueError(
                        "conflicting outcomes for provider dispatch receipt "
                        f"{receipt_id}"
                    )
            return 0.0, True
        current = max(0.0, float(receipt.get("cost_usd", 0.0) or 0.0))
        target_costs = dict(receipt.get("target_costs") or {})
        clean_target = str(target_id or "")
        if not clean_target and len(target_costs) == 1:
            clean_target = next(iter(target_costs))
        requested = max(0.0, float(amount or 0.0))
        if target_costs and clean_target in target_costs:
            target_current = max(
                0.0,
                float(target_costs.get(clean_target, 0.0) or 0.0),
            )
            reversed_cost = min(
                current,
                target_current,
                requested,
            )
            target_remaining = max(0.0, target_current - reversed_cost)
            if target_remaining > 0.0:
                target_costs[clean_target] = target_remaining
            else:
                target_costs.pop(clean_target, None)
        elif not target_costs and receipt.get("target_costs_complete") is not False:
            reversed_cost = min(
                current,
                requested,
            )
        else:
            # A multi-target or opaque receipt without complete target
            # correlation cannot safely identify which estimate to retire.
            reversed_cost = 0.0
        if reversed_cost > 0.0:
            receipt["cost_usd"] = max(0.0, current - reversed_cost)
            if target_costs:
                receipt["target_costs"] = target_costs
            else:
                receipt.pop("target_costs", None)
        if receipt_id:
            applied.add(receipt_id)
            receipt["applied_receipt_ids"] = sorted(applied)[-512:]
            if receipt_record is not None:
                receipt_snapshot = dict(receipt_record)
                receipt_snapshot[
                    "recovered_unknown_reversed_cost_usd"
                ] = reversed_cost
                applied_receipts[receipt_id] = receipt_snapshot
                receipt["applied_receipts"] = {
                    key: applied_receipts[key]
                    for key in sorted(applied_receipts)[-512:]
                }
        self._late_usage_receipts[reservation_id] = receipt
        return reversed_cost, False

    def _annotate_provider_dispatch_receipt_locked(
        self,
        reservation_id: str,
        receipt_id: str,
        **updates: Any,
    ) -> None:
        """Attach derived ledger effects to an already accepted receipt."""

        if not receipt_id:
            return
        receipt = self._late_usage_receipts.get(reservation_id)
        if not isinstance(receipt, dict):
            return
        applied = dict(receipt.get("applied_receipts") or {})
        record = applied.get(receipt_id)
        if not isinstance(record, Mapping):
            return
        updated = dict(record)
        updated.update(updates)
        applied[receipt_id] = updated
        receipt["applied_receipts"] = {
            key: applied[key] for key in sorted(applied)[-512:]
        }
        self._late_usage_receipts[reservation_id] = receipt

    async def record_late_pre_generation_rejection(
        self,
        reservation: CostReservation,
        target_id: str,
        *,
        status_code: int,
        reason: str,
        retire_cancelled_exposure: bool = True,
        dispatch_ordinal: int = 0,
        estimated_dispatch_cost_usd: Optional[float] = None,
    ) -> None:
        """Reverse one missing-usage exposure after a definitive late 4xx."""

        clean_target = str(target_id or "")
        role_key = _canonical_usage_role(reservation.role)
        async with self._lock:
            if self._final_accounting_frozen:
                return
            target_costs = self._reservation_missing_target_costs.get(
                reservation.reservation_id,
                {},
            )
            current = max(
                0.0,
                float(target_costs.get(clean_target, 0.0) or 0.0),
            )
            unit_cost = (
                max(0.0, float(estimated_dispatch_cost_usd or 0.0))
                if estimated_dispatch_cost_usd is not None
                else next(
                (
                    max(
                        0.0,
                        float(item.get("estimated_dispatch_cost_usd", 0.0) or 0.0),
                    )
                    for item in reservation.estimated_models
                    if str(item.get("target_id") or "") == clean_target
                ),
                    current,
                )
            )
            missing_reversed_cost = min(
                current,
                unit_cost if unit_cost > 0.0 else current,
            )
            rejection_receipt_id = _late_rejection_receipt_id(
                reservation_id=reservation.reservation_id,
                target_id=clean_target,
                dispatch_ordinal=dispatch_ordinal,
                status_code=status_code,
                reason=reason,
            )
            recovered_reversed_cost, duplicate_receipt = (
                self._reverse_late_unknown_locked(
                    reservation.reservation_id,
                    max(0.0, unit_cost - missing_reversed_cost),
                    target_id=clean_target,
                    receipt_id=rejection_receipt_id,
                    receipt_record={
                        "kind": "pre_generation_rejection",
                        "role": role_key,
                        "target_id": clean_target,
                        "dispatch_ordinal": max(0, int(dispatch_ordinal or 0)),
                        "status_code": int(status_code or 0),
                        "reason": str(reason or ""),
                        "cost_usd": 0.0,
                    }
                    if rejection_receipt_id
                    else None,
                )
            )
            if duplicate_receipt:
                return
            reversed_cost = missing_reversed_cost + recovered_reversed_cost
            # Provider exposure is an observability/safety ledger independent
            # of whether a dollar budget is enabled.  A definitive correlated
            # pre-generation rejection retires one dispatch even when no
            # budget-side missing-usage entry was created.
            cancelled_exposure_reversed = (
                self._reverse_cancelled_exposure_locked(
                    reservation.reservation_id,
                    unit_cost,
                    target_id=clean_target,
                )
                if retire_cancelled_exposure
                else 0.0
            )
            self._annotate_provider_dispatch_receipt_locked(
                reservation.reservation_id,
                rejection_receipt_id,
                cancelled_provider_exposure_reversed_cost_usd=(
                    cancelled_exposure_reversed
                ),
            )
            if missing_reversed_cost > 0.0:
                remaining = max(0.0, current - missing_reversed_cost)
                if remaining > 0.0:
                    target_costs[clean_target] = remaining
                else:
                    target_costs.pop(clean_target, None)
                if target_costs:
                    self._reservation_missing_target_costs[
                        reservation.reservation_id
                    ] = target_costs
                    self._reservation_missing_unknown_cost_usd[
                        reservation.reservation_id
                    ] = sum(target_costs.values())
                else:
                    self._reservation_missing_target_costs.pop(
                        reservation.reservation_id,
                        None,
                    )
                    self._reservation_missing_unknown_cost_usd.pop(
                        reservation.reservation_id,
                        None,
                    )
                    if not self._reservation_pricing_unknown_cost_usd.get(
                        reservation.reservation_id
                    ):
                        self._reservation_unknown_role.pop(
                            reservation.reservation_id,
                            None,
                        )
            if reversed_cost > 0.0:
                self._unknown_cost_usd = max(
                    0.0,
                    self._unknown_cost_usd - reversed_cost,
                )
                role_totals = self._role_totals.get(role_key)
                if role_totals is not None:
                    role_totals["estimated_unknown_cost_usd"] = max(
                        0.0,
                        float(
                            role_totals.get("estimated_unknown_cost_usd", 0.0)
                            or 0.0
                        )
                        - reversed_cost,
                    )
                held = max(
                    0.0,
                    float(
                        self._active_reservations.get(
                            reservation.reservation_id,
                            0.0,
                        )
                        or 0.0
                    ),
                )
                released = min(held, reversed_cost)
                if released > 0.0:
                    remaining_hold = max(0.0, held - released)
                    self._reserved_cost_usd = max(
                        0.0,
                        self._reserved_cost_usd - released,
                    )
                    if remaining_hold > 0.0:
                        self._active_reservations[
                            reservation.reservation_id
                        ] = remaining_hold
                    else:
                        self._active_reservations.pop(
                            reservation.reservation_id,
                            None,
                        )
                        self._late_hold_reservations.discard(
                            reservation.reservation_id
                        )
                self._refresh_terminal_reason_locked()
            self._events += 1
            event = {
                    "phase": "llm_usage",
                    "verdict": "llm_late_pre_generation_rejection_recorded",
                    "status": "late_pre_generation_rejection",
                    "llm_request_id": reservation.request_id,
                    "llm_reservation_id": reservation.reservation_id,
                    "role": reservation.role,
                    "session_scope": reservation.scope,
                    "action_id": reservation.action_id,
                    "call_kind": reservation.call_kind,
                    "provider_dispatch_receipt_id": rejection_receipt_id,
                    "target_id": clean_target,
                    "status_code": int(status_code),
                    "reason": str(reason or ""),
                    "reservation_dispatch_ordinal": max(
                        0,
                        int(dispatch_ordinal or 0),
                    ),
                    "estimated_unknown_reversed_cost_usd": reversed_cost,
                    "recovered_unknown_reversed_cost_usd": (
                        recovered_reversed_cost
                    ),
                    "llm_cancelled_provider_exposure_reversed_cost_usd": (
                        cancelled_exposure_reversed
                    ),
                    "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                    "llm_budget_committed_cost_usd": self.committed_cost_usd,
                }
            event.update(_reservation_usage_event_metadata(reservation))
            await self._record_event_locked(event)

    async def _settle_observations(
        self,
        reservation: CostReservation,
        observations: Sequence[ProviderUsageRecord],
        *,
        status: str,
        error: str,
        release_reservation: bool,
        late: bool,
        retire_cancelled_exposure: bool = True,
    ) -> None:
        records = list(observations or ())
        late_receipt_id = (
            _late_usage_receipt_id(
                records[0],
                reservation_id=reservation.reservation_id,
            )
            if late and len(records) == 1
            else ""
        )
        input_tokens = sum(int(r.input_tokens) for r in records)
        output_tokens = sum(int(r.output_tokens) for r in records)
        cached_tokens = sum(int(r.cached_input_tokens) for r in records)
        cache_write_tokens = sum(int(r.cache_write_tokens) for r in records)
        miss_tokens = sum(int(r.prompt_cache_miss_tokens) for r in records)
        reasoning_tokens = sum(int(r.reasoning_output_tokens) for r in records)
        exact_cost = 0.0
        pricing_known = True
        unknown_pricing_target_counts: Counter[str] = Counter()
        ambiguous_unknown_pricing = False
        observation_details: List[Dict[str, Any]] = []
        for record in records:
            record_cost, known = cost_for_record(record)
            pricing_known = pricing_known and known
            if not known:
                if record.reservation_target_id:
                    unknown_pricing_target_counts[record.reservation_target_id] += 1
                else:
                    ambiguous_unknown_pricing = True
            item = record.as_dict()
            item["cost_usd"] = record_cost
            item["pricing_known"] = known
            observation_details.append(item)
            exact_cost += record_cost

        estimated_dispatch_cost_by_target = {
            str(item.get("target_id") or ""): max(
                0.0,
                float(
                    item.get(
                        "estimated_dispatch_cost_usd",
                        item.get("estimated_cost_usd", 0.0),
                    )
                    or 0.0
                ),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        reserved_output_by_target = {
            str(item.get("target_id") or ""): max(
                0,
                int(item.get("reserved_output_tokens", 0) or 0),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        sole_reserved_output = (
            next(iter(reserved_output_by_target.values()))
            if len(reserved_output_by_target) == 1
            else None
        )
        provider_output_reservation_overruns: List[Dict[str, Any]] = []
        for record in records:
            target_id = str(record.reservation_target_id or "")
            reserved_output = reserved_output_by_target.get(target_id)
            if reserved_output is None:
                reserved_output = sole_reserved_output
            if reserved_output is None or int(record.output_tokens) <= reserved_output:
                continue
            # Some reasoning providers interpret the request's output limit as
            # a visible-token allowance and report private reasoning in
            # addition to it.  Supported-effort catalogs expose no numeric
            # upper bound, so inflating admission by a guessed multiplier
            # would not create a sound financial guarantee.  Record the exact
            # per-dispatch overrun so operators can distinguish that provider
            # contract from an ordinary estimate miss and a future transport
            # interface can supply a real total-generation ceiling.
            provider_output_reservation_overruns.append(
                {
                    "target_id": target_id,
                    "model": str(record.model or ""),
                    "base_url": str(record.base_url or ""),
                    "reserved_output_tokens": int(reserved_output),
                    "observed_output_tokens": int(record.output_tokens),
                    "observed_reasoning_output_tokens": int(
                        record.reasoning_output_tokens or 0
                    ),
                    "excess_output_tokens": int(record.output_tokens)
                    - int(reserved_output),
                }
            )
        reserved_input_by_target = {
            str(item.get("target_id") or ""): max(
                0,
                int(item.get("reserved_input_tokens", 0) or 0),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        request_input_by_target = {
            str(item.get("target_id") or ""): max(
                0,
                int(item.get("pricing_input_tokens", 0) or 0),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        authorized_retry_counts = {
            str(target_id): max(0, int(count or 0))
            for target_id, count in dict(
                reservation.metadata.get("llm_retry_authorized_target_counts")
                or {}
            ).items()
            if str(target_id)
        }
        has_authenticated_dispatch_counts = (
            "llm_dispatched_target_counts" in reservation.metadata
        )
        if has_authenticated_dispatch_counts:
            dispatched_input_counts = {
                str(target_id): max(0, int(count or 0))
                for target_id, count in dict(
                    reservation.metadata.get("llm_dispatched_target_counts")
                    or {}
                ).items()
                if str(target_id)
            }
            rejected_input_counts = {
                str(target_id): max(0, int(count or 0))
                for target_id, count in dict(
                    reservation.metadata.get(
                        "llm_pre_generation_rejection_target_counts"
                    )
                    or {}
                ).items()
                if str(target_id)
            }
            for target_id, dispatch_count in dispatched_input_counts.items():
                if target_id not in reserved_input_by_target:
                    continue
                input_bearing_dispatches = max(
                    0,
                    dispatch_count - rejected_input_counts.get(target_id, 0),
                )
                reserved_input_by_target[target_id] = max(
                    reserved_input_by_target[target_id],
                    input_bearing_dispatches
                    * request_input_by_target.get(target_id, 0),
                )
        else:
            # Direct controller callers may not install the production
            # dispatch observer. Preserve their explicit authorization
            # contract, while production settlement uses authenticated
            # completed dispatch receipts and cannot count a failed hook.
            for target_id, retry_count in authorized_retry_counts.items():
                if target_id not in reserved_input_by_target:
                    continue
                reserved_input_by_target[target_id] += (
                    retry_count * request_input_by_target.get(target_id, 0)
                )
        sole_reserved_input_target = (
            next(iter(reserved_input_by_target))
            if len(reserved_input_by_target) == 1
            else ""
        )
        observed_input_by_target: Counter[str] = Counter()
        observed_input_example_by_target: Dict[str, ProviderUsageRecord] = {}
        for record in records:
            target_id = str(record.reservation_target_id or "")
            if not target_id and sole_reserved_input_target:
                target_id = sole_reserved_input_target
            observed_input_by_target[target_id] += max(
                0,
                int(record.input_tokens or 0),
            )
            observed_input_example_by_target.setdefault(target_id, record)
        provider_input_reservation_overruns: List[Dict[str, Any]] = []
        for target_id, observed_input in sorted(observed_input_by_target.items()):
            reserved_input = reserved_input_by_target.get(target_id)
            if reserved_input is None or observed_input <= reserved_input:
                continue
            example = observed_input_example_by_target[target_id]
            provider_input_reservation_overruns.append(
                {
                    "target_id": target_id,
                    "model": str(example.model or ""),
                    "base_url": str(example.base_url or ""),
                    "reserved_input_tokens": int(reserved_input),
                    "observed_input_tokens": int(observed_input),
                    "excess_input_tokens": int(observed_input)
                    - int(reserved_input),
                }
            )
        dispatched_target_counts = Counter(
            {
                str(target_id): max(0, int(count or 0))
                for target_id, count in dict(
                    reservation.metadata.get("llm_dispatched_target_counts") or {}
                ).items()
                if str(target_id)
            }
        )
        if not dispatched_target_counts:
            dispatched_target_counts.update(
                str(value)
                for value in reservation.metadata.get(
                    "llm_dispatched_target_ids",
                    (),
                )
                if str(value)
            )
        pre_generation_rejection_target_counts = Counter(
            {
                str(target_id): max(0, int(count or 0))
                for target_id, count in dict(
                    reservation.metadata.get(
                        "llm_pre_generation_rejection_target_counts"
                    )
                    or {}
                ).items()
                if str(target_id)
            }
        )
        exposed_target_counts = Counter(
            {
                target_id: max(
                    0,
                    dispatch_count
                    - pre_generation_rejection_target_counts[target_id],
                )
                for target_id, dispatch_count in dispatched_target_counts.items()
            }
        )
        observed_target_counts = Counter(
            str(record.reservation_target_id)
            for record in records
            if str(record.reservation_target_id or "")
        )
        observed_target_ids = set(observed_target_counts)
        provider_dispatch_receipts = [
            dict(receipt)
            for receipt in list(
                reservation.metadata.get("llm_provider_dispatch_receipts") or ()
            )
            if isinstance(receipt, Mapping)
        ]
        rejected_receipt_keys = {
            (
                str(receipt.get("target_id") or ""),
                max(0, int(receipt.get("dispatch_ordinal", 0) or 0)),
            )
            for receipt in provider_dispatch_receipts
            if str(receipt.get("event") or "") == "pre_generation_rejection"
        }
        precise_dispatch_receipt_costs: Dict[tuple[str, int], float] = {
            (
                str(receipt.get("target_id") or ""),
                max(0, int(receipt.get("dispatch_ordinal", 0) or 0)),
            ): max(
                0.0,
                float(receipt.get("estimated_dispatch_cost_usd", 0.0) or 0.0),
            )
            for receipt in provider_dispatch_receipts
            if str(receipt.get("event") or "") == "dispatch"
            and str(receipt.get("target_id") or "")
            and int(receipt.get("dispatch_ordinal", 0) or 0) > 0
        }
        exposed_receipt_costs = {
            receipt_key: dispatch_cost
            for receipt_key, dispatch_cost in precise_dispatch_receipt_costs.items()
            if receipt_key not in rejected_receipt_keys
        }
        precise_dispatch_ledger_present = bool(
            precise_dispatch_receipt_costs
        ) and all(
            cost > 0.0 for cost in precise_dispatch_receipt_costs.values()
        )
        observed_receipt_keys = {
            (
                str(record.reservation_target_id or ""),
                max(0, int(record.reservation_dispatch_ordinal or 0)),
            )
            for record in records
            if str(record.reservation_target_id or "")
            and int(record.reservation_dispatch_ordinal or 0) > 0
        }
        if release_reservation and precise_dispatch_ledger_present:
            missing_target_costs: Dict[str, float] = {}
            for (target_id, ordinal), dispatch_cost in exposed_receipt_costs.items():
                if (target_id, ordinal) in observed_receipt_keys:
                    continue
                missing_target_costs[target_id] = (
                    missing_target_costs.get(target_id, 0.0) + dispatch_cost
                )
        else:
            # Legacy/opaque clients lack exact dispatch receipts; preserve the
            # former conservative target-count accounting.
            missing_target_costs = (
                {
                    target_id: (
                        estimated_dispatch_cost_by_target.get(target_id, 0.0)
                        * max(0, dispatch_count - observed_target_counts[target_id])
                    )
                    for target_id, dispatch_count in exposed_target_counts.items()
                    if dispatch_count > observed_target_counts[target_id]
                }
                if release_reservation
                else {}
            )
        usage_missing = bool(not records or missing_target_costs)
        missing_unknown_cost = 0.0
        charge_missing_usage = (
            usage_missing and status not in _MISSING_USAGE_NO_CHARGE_STATUSES
        )
        provider_inflight_cancelled = (
            status == "cancelled_provider_inflight"
            or bool(reservation.metadata.get("llm_cancelled_provider_inflight"))
        )
        retryable_exception_no_charge = status == "retryable_exception_no_charge"
        if charge_missing_usage:
            if self.budget_enabled:
                missing_unknown_cost = (
                    sum(missing_target_costs.values())
                    if precise_dispatch_ledger_present
                    or missing_target_costs
                    else float(reservation.estimated_cost_usd or 0.0)
                )
        pricing_unknown_target_costs = {
            target_id: (
                estimated_dispatch_cost_by_target.get(target_id, 0.0) * count
            )
            for target_id, count in unknown_pricing_target_counts.items()
        }
        pricing_unknown_cost = (
            float(reservation.estimated_cost_usd or 0.0)
            if ambiguous_unknown_pricing
            else sum(pricing_unknown_target_costs.values())
        )
        if not self.budget_enabled:
            pricing_unknown_cost = 0.0
            pricing_unknown_target_costs = {}
        if ambiguous_unknown_pricing:
            # The full reservation already covers every possibly missing leaf.
            missing_unknown_cost = 0.0
            missing_target_costs = {}
        late_receipt_record = (
            {
                "kind": "usage",
                "role": _canonical_usage_role(reservation.role),
                "target_id": str(records[0].reservation_target_id or ""),
                "dispatch_ordinal": max(
                    0,
                    int(records[0].reservation_dispatch_ordinal or 0),
                ),
                "input_tokens": input_tokens,
                "output_tokens": output_tokens,
                "cached_input_tokens": cached_tokens,
                "cache_write_tokens": cache_write_tokens,
                "prompt_cache_miss_tokens": miss_tokens,
                "reasoning_output_tokens": reasoning_tokens,
                "cost_usd": exact_cost,
                "model": str(records[0].model or "") if records else "",
            }
            if late_receipt_id
            else {}
        )

        async with self._lock:
            if self._final_accounting_frozen:
                return
            recovered_unknown_reversed = 0.0
            if late and len(records) == 1:
                receipt_target = str(records[0].reservation_target_id or "")
                receipt_unit_cost = max(
                    0.0,
                    float(
                        estimated_dispatch_cost_by_target.get(
                            receipt_target,
                            0.0,
                        )
                        or 0.0
                    ),
                )
                recovered_unknown_reversed, duplicate_receipt = (
                    self._reverse_late_unknown_locked(
                        reservation.reservation_id,
                        receipt_unit_cost,
                        target_id=receipt_target,
                        receipt_id=late_receipt_id,
                        receipt_record=(
                            late_receipt_record if late_receipt_id else None
                        ),
                    )
                )
                if duplicate_receipt:
                    return
            if release_reservation:
                reserved_cost = float(
                    self._active_reservations.pop(reservation.reservation_id, 0.0)
                    or 0.0
                )
                held_cost = 0.0
                if (
                    reservation.hold_for_late_usage
                    and status not in _MISSING_USAGE_NO_CHARGE_STATUSES
                ):
                    held_cost = max(0.0, reserved_cost - exact_cost)
                released_cost = max(0.0, reserved_cost - held_cost)
                self._reserved_cost_usd = max(0.0, self._reserved_cost_usd - released_cost)
                if held_cost > 0.0:
                    self._active_reservations[reservation.reservation_id] = held_cost
                    self._late_hold_reservations.add(reservation.reservation_id)
            self._events += 1
            if usage_missing:
                self._usage_missing_events += 1
            if (
                provider_inflight_cancelled
                and status == "cancelled_provider_inflight"
                and reservation.reservation_id
                not in self._cancelled_provider_inflight_reservations
            ):
                self._cancelled_provider_inflight_reservations.add(
                    reservation.reservation_id
                )
                self._cancelled_provider_inflight_events += 1
                # Precise dispatch receipts identify exactly which requests
                # remained exposed at cancellation.  Charging the full
                # multi-attempt reservation here overstates one dispatched
                # request by the fallback/retry multiplier and cannot later be
                # fully reversed by its correlated receipt.  Retain the full
                # reservation only for opaque clients with no target ledger.
                cancelled_estimate = max(
                    0.0,
                    float(
                        sum(missing_target_costs.values())
                        if dispatched_target_counts
                        else reservation.estimated_cost_usd
                        or 0.0
                    ),
                )
                self._cancelled_provider_inflight_estimated_cost_usd += (
                    cancelled_estimate
                )
                self._cancelled_provider_inflight_cost_by_reservation[
                    reservation.reservation_id
                ] = cancelled_estimate
                if missing_target_costs:
                    self._cancelled_provider_inflight_target_costs[
                        reservation.reservation_id
                    ] = dict(missing_target_costs)
            if retryable_exception_no_charge and usage_missing:
                self._retryable_exception_no_charge_events += 1
            if not pricing_known:
                self._pricing_unknown_events += 1
                if self.budget_enabled:
                    self._terminal_reason = "llm_cost_budget_unknown_pricing"
            role_key = _canonical_usage_role(reservation.role)
            prior_missing_unknown = float(
                self._reservation_missing_unknown_cost_usd.get(
                    reservation.reservation_id,
                    0.0,
                )
                or 0.0
            )
            prior_pricing_unknown = float(
                self._reservation_pricing_unknown_cost_usd.get(
                    reservation.reservation_id,
                    0.0,
                )
                or 0.0
            )
            unknown_reversed = recovered_unknown_reversed
            late_unknown_reversal_remaining: Dict[str, float] = {}
            if late and len(records) == 1:
                receipt_target = str(records[0].reservation_target_id or "")
                receipt_unit_cost = max(
                    0.0,
                    float(
                        estimated_dispatch_cost_by_target.get(receipt_target, 0.0)
                        or 0.0
                    ),
                )
                late_unknown_reversal_remaining[receipt_target] = max(
                    0.0,
                    receipt_unit_cost - recovered_unknown_reversed,
                )
            if records and prior_missing_unknown > 0.0:
                prior_target_costs = dict(
                    self._reservation_missing_target_costs.get(
                        reservation.reservation_id,
                        {},
                    )
                )
                reversible_targets = set(observed_target_ids)
                if not reversible_targets and len(prior_target_costs) == 1:
                    reversible_targets = set(prior_target_costs)
                if prior_target_costs:
                    for target_id in reversible_targets:
                        current_target_cost = max(
                            0.0,
                            float(prior_target_costs.get(target_id, 0.0) or 0.0),
                        )
                        unit_cost = max(
                            0.0,
                            float(
                                estimated_dispatch_cost_by_target.get(
                                    target_id,
                                    0.0,
                                )
                                or 0.0
                            ),
                        )
                        reversed_cost = min(
                            current_target_cost,
                            unit_cost if unit_cost > 0.0 else current_target_cost,
                        )
                        if target_id in late_unknown_reversal_remaining:
                            reversed_cost = min(
                                reversed_cost,
                                late_unknown_reversal_remaining[target_id],
                            )
                            late_unknown_reversal_remaining[target_id] = max(
                                0.0,
                                late_unknown_reversal_remaining[target_id]
                                - reversed_cost,
                            )
                        unknown_reversed += reversed_cost
                        remaining_target_cost = current_target_cost - reversed_cost
                        if remaining_target_cost > 0.0:
                            prior_target_costs[target_id] = remaining_target_cost
                        else:
                            prior_target_costs.pop(target_id, None)
                    if prior_target_costs:
                        self._reservation_missing_target_costs[
                            reservation.reservation_id
                        ] = prior_target_costs
                        self._reservation_missing_unknown_cost_usd[
                            reservation.reservation_id
                        ] = sum(prior_target_costs.values())
                    else:
                        self._reservation_missing_target_costs.pop(
                            reservation.reservation_id,
                            None,
                        )
                        self._reservation_missing_unknown_cost_usd.pop(
                            reservation.reservation_id,
                            None,
                        )
                else:
                    unknown_reversed = prior_missing_unknown
                    self._reservation_missing_unknown_cost_usd.pop(
                        reservation.reservation_id,
                        None,
                    )
                if (
                    not self._reservation_missing_unknown_cost_usd.get(
                        reservation.reservation_id
                    )
                    and pricing_known
                    and prior_pricing_unknown <= 0.0
                ):
                    self._reservation_unknown_role.pop(
                        reservation.reservation_id,
                        None,
                    )
            unknown_cost = 0.0
            if missing_unknown_cost > 0.0 and prior_missing_unknown <= 0.0:
                self._reservation_missing_unknown_cost_usd[
                    reservation.reservation_id
                ] = missing_unknown_cost
                if missing_target_costs:
                    self._reservation_missing_target_costs[
                        reservation.reservation_id
                    ] = dict(missing_target_costs)
                unknown_cost += missing_unknown_cost
            if pricing_unknown_cost > 0.0:
                if pricing_unknown_target_costs and not ambiguous_unknown_pricing:
                    target_costs = (
                        self._reservation_pricing_unknown_target_costs.setdefault(
                            reservation.reservation_id,
                            {},
                        )
                    )
                    for target_id, cost in pricing_unknown_target_costs.items():
                        target_costs[target_id] = (
                            float(target_costs.get(target_id, 0.0) or 0.0)
                            + cost
                        )
                    new_pricing_unknown = sum(target_costs.values())
                else:
                    new_pricing_unknown = (
                        prior_pricing_unknown + pricing_unknown_cost
                    )
                self._reservation_pricing_unknown_cost_usd[
                    reservation.reservation_id
                ] = new_pricing_unknown
                unknown_cost += max(
                    0.0,
                    new_pricing_unknown - prior_pricing_unknown,
                )
            if (
                self._reservation_missing_unknown_cost_usd.get(
                    reservation.reservation_id
                )
                or self._reservation_pricing_unknown_cost_usd.get(
                    reservation.reservation_id
                )
            ):
                self._reservation_unknown_role[reservation.reservation_id] = role_key
            if not release_reservation and unknown_reversed > 0.0 and exact_cost > 0.0:
                held = max(
                    0.0,
                    float(
                        self._active_reservations.get(
                            reservation.reservation_id,
                            0.0,
                        )
                        or 0.0
                    ),
                )
                reduction = min(held, exact_cost)
                if reduction > 0.0:
                    remaining_hold = max(0.0, held - reduction)
                    self._reserved_cost_usd = max(
                        0.0,
                        self._reserved_cost_usd - reduction,
                    )
                    if remaining_hold > 0.0:
                        self._active_reservations[
                            reservation.reservation_id
                        ] = remaining_hold
                    else:
                        self._active_reservations.pop(
                            reservation.reservation_id,
                            None,
                        )
                        self._late_hold_reservations.discard(
                            reservation.reservation_id
                        )
            self._input_tokens += input_tokens
            self._output_tokens += output_tokens
            self._cached_input_tokens += cached_tokens
            self._cache_write_tokens += cache_write_tokens
            self._prompt_cache_miss_tokens += miss_tokens
            self._reasoning_output_tokens += reasoning_tokens
            self._exact_cost_usd += exact_cost
            self._unknown_cost_usd = max(
                0.0,
                self._unknown_cost_usd + unknown_cost - unknown_reversed,
            )
            if not release_reservation and retire_cancelled_exposure:
                cancelled_exposure_reversed = 0.0
                for target_id, count in observed_target_counts.items():
                    receipt_exposure_cost = max(
                        0.0,
                        float(
                            estimated_dispatch_cost_by_target.get(target_id, 0.0)
                            or 0.0
                        ),
                    ) * count
                    cancelled_exposure_reversed += self._reverse_cancelled_exposure_locked(
                        reservation.reservation_id,
                        receipt_exposure_cost,
                        target_id=target_id,
                    )
                if not observed_target_counts and records:
                    cancelled_exposure_reversed += self._reverse_cancelled_exposure_locked(
                        reservation.reservation_id,
                        unknown_reversed,
                    )
                self._annotate_provider_dispatch_receipt_locked(
                    reservation.reservation_id,
                    late_receipt_id,
                    cancelled_provider_exposure_reversed_cost_usd=(
                        cancelled_exposure_reversed
                    ),
                )
            role_totals = self._role_totals.setdefault(
                role_key,
                {
                    "input_tokens": 0,
                    "output_tokens": 0,
                    "cached_input_tokens": 0,
                    "cache_write_tokens": 0,
                    "prompt_cache_miss_tokens": 0,
                    "reasoning_output_tokens": 0,
                    "cost_usd": 0.0,
                    "estimated_unknown_cost_usd": 0.0,
                    "model": "",
                },
            )
            role_totals["input_tokens"] += input_tokens
            role_totals["output_tokens"] += output_tokens
            role_totals["cached_input_tokens"] += cached_tokens
            role_totals["cache_write_tokens"] = int(
                role_totals.get("cache_write_tokens", 0) or 0
            ) + cache_write_tokens
            role_totals["prompt_cache_miss_tokens"] += miss_tokens
            role_totals["reasoning_output_tokens"] += reasoning_tokens
            role_totals["cost_usd"] += exact_cost
            role_totals["estimated_unknown_cost_usd"] = max(
                0.0,
                float(role_totals["estimated_unknown_cost_usd"])
                + unknown_cost
                - unknown_reversed,
            )
            if records:
                role_totals["model"] = records[-1].model
            self._refresh_terminal_reason_locked()
            unknown_exposure = float(self._unknown_cost_usd)
            accounting_incomplete = bool(unknown_exposure > 1e-12)
            event = {
                "phase": "llm_usage",
                "verdict": (
                    "llm_usage_missing" if usage_missing else "llm_usage_recorded"
                ),
                "status": status,
                "error": error,
                "llm_request_id": reservation.request_id,
                "llm_reservation_id": reservation.reservation_id,
                "role": reservation.role,
                "session_scope": reservation.scope,
                "action_id": reservation.action_id,
                "call_kind": reservation.call_kind,
                "late_usage": bool(late),
                "provider_dispatch_receipt_id": late_receipt_id,
                "input_tokens": input_tokens,
                "output_tokens": output_tokens,
                "cached_input_tokens": cached_tokens,
                "cache_write_tokens": cache_write_tokens,
                "prompt_cache_miss_tokens": miss_tokens,
                "reasoning_output_tokens": reasoning_tokens,
                "cost_usd": exact_cost,
                "estimated_cost_usd": reservation.estimated_cost_usd,
                "estimated_unknown_cost_usd": unknown_cost,
                "estimated_unknown_reversed_cost_usd": unknown_reversed,
                "recovered_unknown_reversed_cost_usd": (
                    recovered_unknown_reversed
                ),
                "pricing_known": pricing_known,
                "usage_missing": usage_missing,
                "missing_provider_target_ids": sorted(missing_target_costs),
                "provider_exposed_target_counts": dict(exposed_target_counts),
                "provider_observations": observation_details,
                "estimated_models": list(reservation.estimated_models),
                "provider_output_reservation_overrun": bool(
                    provider_output_reservation_overruns
                ),
                "provider_output_reservation_overruns": (
                    provider_output_reservation_overruns
                ),
                "provider_input_reservation_overrun": bool(
                    provider_input_reservation_overruns
                ),
                "provider_input_reservation_overruns": (
                    provider_input_reservation_overruns
                ),
                "max_cost_usd": self.max_cost_usd,
                "llm_budget_accounted_cost_usd": self.accounted_cost_usd,
                "llm_budget_committed_cost_usd": self.committed_cost_usd,
                "llm_observed_usage_cost_usd": float(self._exact_cost_usd),
                "llm_conservative_unknown_exposure_usd": unknown_exposure,
                "cost_accounting_incomplete": accounting_incomplete,
                "llm_cost_accounting_incomplete": accounting_incomplete,
                "llm_budget_accounted_cost_is_conservative_upper_bound": (
                    accounting_incomplete
                ),
                "llm_budget_remaining_usd": self.remaining_usd(),
                "llm_cost_budget_exhausted": self.exhausted(),
            }
            event.update(_reservation_usage_event_metadata(reservation))
            if provider_inflight_cancelled:
                event["llm_cancelled_provider_inflight"] = True
                event["llm_cancelled_provider_exposure_risk"] = True
            if retryable_exception_no_charge and usage_missing:
                event["llm_retryable_exception_no_charge"] = True
                event["llm_retryable_exception_no_charge_kind"] = str(
                    reservation.metadata.get("llm_retryable_exception_no_charge_kind")
                    or ""
                )
                event["llm_missing_usage_charged"] = False
            elif usage_missing:
                event["llm_missing_usage_charged"] = bool(unknown_cost > 0.0)
            if usage_missing:
                event["reasoning_output_tokens_unknown"] = True
            if usage_missing and bool(event.get("llm_retry_deadline_exhausted")):
                event["llm_usage_missing_due_to_retry_deadline"] = True
            temperature_requested = event.get("temperature_requested")
            temperature_sent = event.get("temperature_sent")
            temperature_provider_dropped = bool(
                event.get("temperature_provider_dropped")
            )
            temperature_provider_drop_reason = str(
                event.get("temperature_provider_drop_reason") or ""
            )
            observed_temperature_metadata = False
            observed_any_provider_drop = False
            observed_provider_drop_reason = ""
            observed_sent_values: List[Any] = []
            for observed in observation_details:
                if not isinstance(observed, dict):
                    continue
                observed_requested = observed.get("temperature_requested")
                observed_sent = observed.get("temperature_sent")
                observed_dropped = bool(
                    observed.get("temperature_provider_dropped")
                )
                observed_reason = str(
                    observed.get("temperature_provider_drop_reason") or ""
                ).strip()
                has_observed_temperature_metadata = (
                    observed_requested is not None
                    or observed_sent is not None
                    or observed_dropped
                    or bool(observed_reason)
                )
                if not has_observed_temperature_metadata:
                    continue
                observed_temperature_metadata = True
                if observed_requested is not None:
                    temperature_requested = observed_requested
                if observed_sent is not None:
                    observed_sent_values.append(observed_sent)
                if observed_dropped:
                    observed_any_provider_drop = True
                    if observed_reason:
                        observed_provider_drop_reason = observed_reason
            if observed_temperature_metadata:
                temperature_sent = (
                    observed_sent_values[-1] if observed_sent_values else None
                )
                temperature_provider_dropped = bool(observed_any_provider_drop)
                temperature_provider_drop_reason = (
                    observed_provider_drop_reason
                    if observed_any_provider_drop
                    else ""
                )
            event["temperature_requested"] = temperature_requested
            event["temperature_sent"] = temperature_sent
            event["temperature_provider_dropped"] = bool(
                temperature_provider_dropped
            )
            event["temperature_provider_drop_reason"] = (
                temperature_provider_drop_reason
            )
            await self._record_event_locked(event)

    async def metered_call(
        self,
        *,
        client: Any,
        messages: Sequence[Dict[str, Any]],
        role: str,
        scope: str,
        call_kind: str,
        invoke: Callable[[Optional[Callable[[ProviderUsageRecord], Any]]], Any],
        action_id: str = "",
        tools: Optional[Sequence[Dict[str, Any]]] = None,
        max_tokens_override: Optional[int] = None,
        candidate_count: int = 1,
        metadata: Optional[Mapping[str, Any]] = None,
        retryable_exception_no_charge: Optional[Callable[[BaseException], bool]] = None,
        on_reserved: Optional[Callable[[Any], Any]] = None,
        provider_dispatch_lease: Optional[ProviderDispatchAttemptLease] = None,
    ) -> Any:
        requested_dispatch_limit = max(
            0,
            int(dict(metadata or {}).get("provider_dispatch_max_attempts", 0) or 0),
        )
        if (
            requested_dispatch_limit
            and bool(getattr(client, "supports_transport_dispatch_marker", False))
            and not bool(
                getattr(
                    client,
                    "supports_transport_dispatch_authorization",
                    False,
                )
            )
        ):
            raise ProviderDispatchAttemptLimitExceeded(
                "provider dispatch attempt limit requires awaited transport "
                "authorization; marker-only client cannot enforce the ceiling"
            )
        reservation = await self.reserve(
            client=client,
            messages=messages,
            role=role,
            scope=scope,
            action_id=action_id,
            call_kind=call_kind,
            tools=tools,
            max_tokens_override=max_tokens_override,
            candidate_count=candidate_count,
            metadata=metadata,
        )
        observations: List[ProviderUsageRecord] = []
        settled = False
        # Production transports opt in to the precise marker below.  Preserve
        # the historical public contract for arbitrary duck-typed clients:
        # once their invoke callback begins we cannot know whether a local
        # exception happened before or after an opaque provider dispatch, so
        # fail closed and treat it as dispatched.
        precise_dispatch_marker = bool(
            getattr(client, "supports_transport_dispatch_marker", False)
        )
        provider_dispatched = False
        active_target_ids = {
            str(item.get("target_id") or "")
            for item in reservation.estimated_models
            if bool(item.get("reservation_active", False))
            and str(item.get("target_id") or "")
        }
        dispatched_target_counts: Counter[str] = Counter()
        pre_generation_rejection_target_counts: Counter[str] = Counter()
        live_legacy_marker_records: Dict[str, Dict[str, Any]] = {}
        dispatch_receipts: List[Dict[str, Any]] = []
        callback_target_counts: Counter[str] = Counter()
        late_dispatch_tasks: Dict[str, List[asyncio.Task]] = {}
        dispatch_context_token: Optional[contextvars.Token] = None
        pending_dispatch_receipt_token: Optional[contextvars.Token] = None
        settlement_complete = asyncio.Event()
        dispatch_observer_token: Optional[contextvars.Token] = None
        inherited_dispatch_observer = _PROVIDER_DISPATCH_OBSERVER.get()

        dispatch_authority_remaining_usd: Dict[str, float] = {
            str(item.get("target_id") or ""): max(
                0.0,
                float(item.get("estimated_cost_usd", 0.0) or 0.0),
            )
            for item in reservation.estimated_models
            if bool(item.get("reservation_active", False))
            and str(item.get("target_id") or "")
        }
        dispatch_pricing: Dict[str, tuple[float, float]] = {
            str(item.get("target_id") or ""): (
                max(
                    0.0,
                    float(
                        item.get("estimated_dispatch_input_cost_usd", 0.0)
                        or 0.0
                    ),
                ),
                max(
                    0.0,
                    float(
                        item.get("estimated_dispatch_output_cost_usd", 0.0)
                        or 0.0
                    ),
                ),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        fallback_dispatch_costs: Dict[str, float] = {
            str(item.get("target_id") or ""): max(
                0.0,
                float(item.get("estimated_dispatch_cost_usd", 0.0) or 0.0),
            )
            for item in reservation.estimated_models
            if str(item.get("target_id") or "")
        }
        dispatch_authorization_counts: Counter[str] = Counter()
        dispatch_authorization_lock = asyncio.Lock()
        counted_dispatch_authorization_ids: set[str] = set()
        marked_dispatch_authorization_ids: set[str] = set()
        dispatch_authorization_lease_receipt_ids: Dict[str, str] = {}
        dispatch_authorization_records: Dict[str, Dict[str, Any]] = {}

        async def _authorize_concrete_dispatch_locked(
            details: Mapping[str, Any],
        ) -> Dict[str, Any]:
            """Acquire exact worst-case capacity for one provider exposure."""

            # A cancellation-resistant recursive helper can remain inside an
            # already-admitted pool/chain call after its parent yields. Every
            # production transport retry crosses this awaited authorization
            # boundary, so consult the mutable task-context lease before it
            # can create another paid provider exposure.
            require_hard_timeout_capability_active(
                "concrete provider transport authorization"
            )
            target_id = str(_PROVIDER_DISPATCH_TARGET.get() or "")
            target_id = str(dict(details or {}).get("target_id") or target_id)
            if not target_id and len(active_target_ids) == 1:
                target_id = next(iter(active_target_ids))
            if not target_id and len(active_target_ids) > 1:
                raise RuntimeError(
                    "provider dispatch target is ambiguous across multiple "
                    "reserved pricing leaves"
                )
            candidate_count = max(
                1,
                int(dict(details or {}).get("candidate_count", 1) or 1),
            )
            input_cost, output_cost = dispatch_pricing.get(target_id, (0.0, 0.0))
            dispatch_cost = input_cost + output_cost * candidate_count
            if dispatch_cost <= 0.0:
                dispatch_cost = fallback_dispatch_costs.get(target_id, 0.0)
            available = max(
                0.0,
                float(dispatch_authority_remaining_usd.get(target_id, 0.0) or 0.0),
            )
            next_ordinal = int(dispatch_authorization_counts[target_id]) + 1
            dispatch_attempt_limit = max(
                0,
                int(
                    reservation.metadata.get(
                        "provider_dispatch_max_attempts", 0
                    )
                    or 0
                ),
            )
            next_logical_ordinal = len(counted_dispatch_authorization_ids) + 1
            if (
                dispatch_attempt_limit
                and next_logical_ordinal > dispatch_attempt_limit
            ):
                # Enforce the logical-call retry ceiling at the concrete
                # transport boundary. This works across HTTP status, timeout,
                # compatibility, ModelChain, and Responses retry paths without
                # guessing which wrapper owns the retry. Earlier dispatched
                # attempts remain conservatively accounted; this attempt is
                # refused before a new provider exposure exists.
                reservation.metadata.update(
                    {
                        "provider_dispatch_attempt_limit_exhausted": True,
                        "provider_dispatch_attempt_limit": (
                            dispatch_attempt_limit
                        ),
                        "provider_dispatch_attempt_limit_target_id": target_id,
                        "provider_dispatch_attempt_limit_next_ordinal": (
                            next_logical_ordinal
                        ),
                    }
                )
                raise ProviderDispatchAttemptLimitExceeded(
                    "provider dispatch attempt limit exhausted before "
                    f"dispatch (target={target_id}, "
                    f"limit={dispatch_attempt_limit}, "
                    f"next_ordinal={next_logical_ordinal})",
                    provider_dispatches_started=len(
                        counted_dispatch_authorization_ids
                    ),
                    dispatch_attempt_limit=dispatch_attempt_limit,
                    next_dispatch_ordinal=next_logical_ordinal,
                    provider_dispatch_attempt_limit_target_id=target_id,
                )
            extension = max(0.0, dispatch_cost - available)
            if extension > 1e-12:
                await self.authorize_provider_retry_dispatch(
                    reservation,
                    target_id=target_id,
                    dispatch_ordinal=next_ordinal,
                    requested_cost_usd=extension,
                )
                available += extension
            # A synchronous authoritative rejection can retire an earlier
            # authorization while this coroutine awaits budget extension.
            # Recompute the live logical ordinal before committing this ticket.
            next_logical_ordinal = len(counted_dispatch_authorization_ids) + 1
            if (
                dispatch_attempt_limit
                and next_logical_ordinal > dispatch_attempt_limit
            ):
                raise ProviderDispatchAttemptLimitExceeded(
                    "provider dispatch attempt limit exhausted before "
                    f"dispatch (target={target_id}, "
                    f"limit={dispatch_attempt_limit}, "
                    f"next_ordinal={next_logical_ordinal})",
                    provider_dispatches_started=len(
                        counted_dispatch_authorization_ids
                    ),
                    dispatch_attempt_limit=dispatch_attempt_limit,
                    next_dispatch_ordinal=next_logical_ordinal,
                    provider_dispatch_attempt_limit_target_id=target_id,
                )
            lease_receipt = (
                await provider_dispatch_lease.authorize()
                if provider_dispatch_lease is not None
                else {}
            )
            authorization_id = f"dispatch-authorization:{uuid.uuid4().hex}"
            counted_dispatch_authorization_ids.add(authorization_id)
            dispatch_authorization_lease_receipt_ids[authorization_id] = str(
                lease_receipt.get("provider_dispatch_lease_receipt_id") or ""
            )
            dispatch_authority_remaining_usd[target_id] = max(
                0.0, available - dispatch_cost
            )
            dispatch_authorization_counts[target_id] = next_ordinal
            receipt = {
                **dict(details or {}),
                **lease_receipt,
                "target_id": target_id,
                "dispatch_ordinal": next_ordinal,
                "logical_dispatch_ordinal": next_logical_ordinal,
                "dispatch_authorization_id": authorization_id,
                "candidate_count": candidate_count,
                "estimated_dispatch_cost_usd": dispatch_cost,
            }
            dispatch_authorization_records[authorization_id] = dict(receipt)
            # Preserve the caller's live pre-dispatch hook. Budget state is
            # extended first so the live hold includes new authority.
            if inherited_dispatch_observer is not None:
                try:
                    observed = inherited_dispatch_observer()
                    if inspect.isawaitable(observed):
                        await observed
                except BaseException:
                    counted_dispatch_authorization_ids.discard(authorization_id)
                    dispatch_authorization_lease_receipt_ids.pop(
                        authorization_id,
                        None,
                    )
                    dispatch_authorization_records.pop(authorization_id, None)
                    if provider_dispatch_lease is not None:
                        provider_dispatch_lease.retire(receipt)
                    dispatch_authority_remaining_usd[target_id] = (
                        max(
                            0.0,
                            float(
                                dispatch_authority_remaining_usd.get(
                                    target_id,
                                    0.0,
                                )
                                or 0.0
                            ),
                        )
                        + dispatch_cost
                    )
                    raise
            return receipt

        async def _authorize_concrete_dispatch(
            details: Mapping[str, Any],
        ) -> Dict[str, Any]:
            # ModelPool leaves and nested retry adapters may reach this callback
            # concurrently.  The logical limit, cost-authority drawdown, and
            # receipt ordinal are one transaction.
            async with dispatch_authorization_lock:
                return await _authorize_concrete_dispatch_locked(details)

        def _mark_dispatched(
            event: str = "dispatch",
            details: Mapping[str, Any] | None = None,
        ) -> None:
            nonlocal provider_dispatched
            clean_details = dict(details or {})
            clean_event = str(event or "dispatch")
            if (
                clean_event == "dispatch"
                and clean_details.get("provider_dispatch_marker_receipt_id")
                and not clean_details.get("dispatch_authorization_id")
            ):
                # A no-argument legacy marker reads the pending receipt used
                # to correlate the previous dispatch's rejection. Starting a
                # new dispatch must not inherit that receipt or its target.
                clean_details.pop("provider_dispatch_marker_receipt_id", None)
                clean_details.pop("target_id", None)
            target_id = str(_PROVIDER_DISPATCH_TARGET.get() or "")
            target_id = str(clean_details.get("target_id") or target_id)
            if not target_id and len(active_target_ids) == 1:
                target_id = next(iter(active_target_ids))
            if clean_event == "pre_generation_rejection":
                authorization_id = str(
                    clean_details.get("dispatch_authorization_id") or ""
                ).strip()
                legacy_marker_receipt_id = str(
                    clean_details.get("provider_dispatch_marker_receipt_id") or ""
                ).strip()
                expected_lease_receipt_id = (
                    dispatch_authorization_lease_receipt_ids.get(
                        authorization_id,
                        "",
                    )
                )
                provided_lease_receipt_id = str(
                    clean_details.get(
                        "provider_dispatch_lease_receipt_id"
                    )
                    or ""
                ).strip()
                authorization_record = dict(
                    dispatch_authorization_records.get(authorization_id, {}) or {}
                )
                legacy_marker_record = dict(
                    live_legacy_marker_records.get(
                        legacy_marker_receipt_id,
                        {},
                    )
                    or {}
                )
                canonical_target_id = str(
                    authorization_record.get("target_id") or ""
                ).strip()
                provided_target_id = str(
                    clean_details.get("target_id") or ""
                ).strip()
                canonical_notification_receipt_id = str(
                    authorization_record.get(
                        "provider_dispatch_notification_receipt_id"
                    )
                    or ""
                ).strip()
                provided_notification_receipt_id = str(
                    clean_details.get(
                        "provider_dispatch_notification_receipt_id"
                    )
                    or ""
                ).strip()
                authorization_is_live = bool(
                    authorization_id
                    and authorization_id
                    in counted_dispatch_authorization_ids
                    and authorization_record
                    and canonical_target_id
                    and provided_target_id == canonical_target_id
                    and (
                        not canonical_notification_receipt_id
                        or provided_notification_receipt_id
                        == canonical_notification_receipt_id
                    )
                    and (
                        provider_dispatch_lease is None
                        or (
                            expected_lease_receipt_id
                            and provided_lease_receipt_id
                            == expected_lease_receipt_id
                        )
                    )
                )
                legacy_unretired_dispatch = bool(
                    provider_dispatch_lease is None
                    and not authorization_id
                    and legacy_marker_receipt_id
                    and legacy_marker_record
                    and provided_target_id
                    == str(legacy_marker_record.get("target_id") or "").strip()
                )
                if not authorization_is_live and not legacy_unretired_dispatch:
                    # Provider callbacks may repeat within the same run. A
                    # rejection can retire/refund exactly one live dispatch
                    # ticket; an unknown or duplicate receipt is telemetry,
                    # never new budget authority or negative exposure.
                    dispatch_receipts.append(
                        {
                            "event": "duplicate_pre_generation_rejection",
                            "target_id": target_id,
                            **clean_details,
                        }
                    )
                    return
                # This provider receipt proves that no generation occurred.
                # Recycle both dollars and the logical generation-attempt
                # ticket so a corrected payload can use the configured cap.
                if authorization_is_live:
                    target_id = canonical_target_id
                    rejection_details = {
                        **authorization_record,
                        "status_code": clean_details.get("status_code", 0),
                        "reason": clean_details.get("reason", ""),
                    }
                    counted_dispatch_authorization_ids.remove(authorization_id)
                    dispatch_authorization_lease_receipt_ids.pop(
                        authorization_id,
                        None,
                    )
                    dispatch_authorization_records.pop(authorization_id, None)
                    if provider_dispatch_lease is not None:
                        provider_dispatch_lease.retire(rejection_details)
                    _track_provider_dispatch_event(
                        "pre_generation_rejection",
                        rejection_details,
                    )
                else:
                    target_id = str(
                        legacy_marker_record.get("target_id") or ""
                    ).strip()
                    rejection_details = {
                        **legacy_marker_record,
                        "status_code": clean_details.get("status_code", 0),
                        "reason": clean_details.get("reason", ""),
                    }
                    live_legacy_marker_records.pop(
                        legacy_marker_receipt_id,
                        None,
                    )
                    _track_provider_dispatch_event(
                        "pre_generation_rejection",
                        rejection_details,
                    )
                dispatch_ordinal = max(
                    0,
                    int(
                        (
                            authorization_record.get("dispatch_ordinal")
                            if authorization_is_live
                            else rejection_details.get("dispatch_ordinal")
                        )
                        or dispatched_target_counts.get(target_id, 0)
                        or 0
                    ),
                )
                if target_id:
                    pre_generation_rejection_target_counts[target_id] += 1
                    # The provider authoritatively rejected this request
                    # before generation. Recycle its already-held dispatch
                    # capacity so an unsupported-parameter correction can
                    # reach the provider without reserving fictitious spend.
                    if authorization_is_live:
                        dispatch_authority_remaining_usd[target_id] = (
                            max(
                                0.0,
                                float(
                                    dispatch_authority_remaining_usd.get(
                                        target_id, 0.0
                                    )
                                    or 0.0
                                ),
                            )
                            + max(
                                0.0,
                                float(
                                    authorization_record.get(
                                        "estimated_dispatch_cost_usd", 0.0
                                    )
                                    or 0.0
                                ),
                            )
                        )
                dispatch_receipts.append(
                    {
                        "event": clean_event,
                        "target_id": target_id,
                        "dispatch_ordinal": dispatch_ordinal,
                            **rejection_details,
                    }
                )
                if settled and target_id:
                    dispatch_tasks = late_dispatch_tasks.get(target_id, [])
                    dispatch_task = dispatch_tasks.pop(0) if dispatch_tasks else None

                    async def _reverse_after_settlement() -> None:
                        await settlement_complete.wait()
                        if dispatch_task is not None:
                            try:
                                await asyncio.shield(dispatch_task)
                            except Exception:
                                pass
                        late_kwargs = {
                            "status_code": int(
                                rejection_details.get("status_code", 0) or 0
                            ),
                            "reason": str(rejection_details.get("reason") or ""),
                            "retire_cancelled_exposure": dispatch_task is None,
                            "dispatch_ordinal": dispatch_ordinal,
                        }
                        if "estimated_dispatch_cost_usd" in rejection_details:
                            late_kwargs["estimated_dispatch_cost_usd"] = max(
                                0.0,
                                float(
                                    (
                                        authorization_record.get(
                                            "estimated_dispatch_cost_usd", 0.0
                                        )
                                        if authorization_is_live
                                        else clean_details.get(
                                            "estimated_dispatch_cost_usd", 0.0
                                        )
                                    )
                                    or 0.0
                                ),
                            )
                        await self.record_late_pre_generation_rejection(
                            reservation, target_id, **late_kwargs
                        )

                    task = asyncio.create_task(_reverse_after_settlement())
                    self._pending_late_usage_tasks.add(task)
                    task.add_done_callback(
                        mark_runtime_owned_callback(
                            self._pending_late_usage_tasks.discard
                        )
                    )
                return
            dispatch_authorization_id = str(
                clean_details.get("dispatch_authorization_id") or ""
            ).strip()
            canonical_authorization_record = dict(
                dispatch_authorization_records.get(
                    dispatch_authorization_id,
                    {},
                )
                or {}
            )
            if dispatch_authorization_id:
                if (
                    not canonical_authorization_record
                    or dispatch_authorization_id
                    in marked_dispatch_authorization_ids
                ):
                    dispatch_receipts.append(
                        {
                            "event": "duplicate_dispatch",
                            "target_id": target_id,
                            **clean_details,
                        }
                    )
                    return
                pending_receipt = dict(
                    _PROVIDER_PENDING_DISPATCH_RECEIPT.get() or {}
                )
                if str(
                    pending_receipt.get("dispatch_authorization_id") or ""
                ).strip() == dispatch_authorization_id:
                    notification_receipt_id = str(
                        pending_receipt.get(
                            "provider_dispatch_notification_receipt_id"
                        )
                        or ""
                    ).strip()
                    if notification_receipt_id:
                        canonical_authorization_record[
                            "provider_dispatch_notification_receipt_id"
                        ] = notification_receipt_id
                dispatch_authorization_records[dispatch_authorization_id] = (
                    dict(canonical_authorization_record)
                )
                marked_dispatch_authorization_ids.add(
                    dispatch_authorization_id
                )
                clean_details = dict(canonical_authorization_record)
                target_id = str(clean_details.get("target_id") or "").strip()
            if (
                provider_dispatch_lease is None
                and not str(
                    clean_details.get("dispatch_authorization_id") or ""
                ).strip()
            ):
                legacy_marker_receipt_id = (
                    f"provider-marker-dispatch:{uuid.uuid4().hex}"
                )
                clean_details["provider_dispatch_marker_receipt_id"] = (
                    legacy_marker_receipt_id
                )
                clean_details["target_id"] = target_id
                _PROVIDER_PENDING_DISPATCH_RECEIPT.set(clean_details)
            provider_dispatched = True
            if provider_dispatch_lease is not None:
                provider_dispatch_lease.mark_dispatched(clean_details)
            if target_id:
                dispatched_target_counts[target_id] += 1
            dispatch_ordinal = max(
                0,
                int(
                    clean_details.get("dispatch_ordinal")
                    or dispatched_target_counts.get(target_id, 0)
                    or 0
                ),
            )
            clean_details["dispatch_ordinal"] = dispatch_ordinal
            legacy_marker_receipt_id = str(
                clean_details.get("provider_dispatch_marker_receipt_id") or ""
            ).strip()
            if legacy_marker_receipt_id:
                live_legacy_marker_records[legacy_marker_receipt_id] = dict(
                    clean_details
                )
            dispatch_receipts.append(
                {
                    "event": "dispatch",
                    "target_id": target_id,
                    "dispatch_ordinal": dispatch_ordinal,
                    **clean_details,
                }
            )
            _track_provider_dispatch_event("dispatch", clean_details)
            if settled and target_id:
                if "estimated_dispatch_cost_usd" in clean_details:
                    late_call = self.record_late_dispatch(
                        reservation,
                        target_id,
                        estimated_dispatch_cost_usd=max(
                            0.0,
                            float(
                                clean_details.get(
                                    "estimated_dispatch_cost_usd", 0.0
                                )
                                or 0.0
                            ),
                        ),
                    )
                else:
                    late_call = self.record_late_dispatch(reservation, target_id)
                task = asyncio.create_task(late_call)
                late_dispatch_tasks.setdefault(target_id, []).append(task)
                self._pending_late_usage_tasks.add(task)
                task.add_done_callback(
                    mark_runtime_owned_callback(self._pending_late_usage_tasks.discard)
                )

        def _reset_dispatch_context() -> None:
            nonlocal dispatch_context_token, dispatch_observer_token
            nonlocal pending_dispatch_receipt_token
            if dispatch_context_token is not None:
                _PROVIDER_DISPATCH_MARKER.reset(dispatch_context_token)
                dispatch_context_token = None
            if dispatch_observer_token is not None:
                _PROVIDER_DISPATCH_OBSERVER.reset(dispatch_observer_token)
                dispatch_observer_token = None
            if pending_dispatch_receipt_token is not None:
                _PROVIDER_PENDING_DISPATCH_RECEIPT.reset(
                    pending_dispatch_receipt_token
                )
                pending_dispatch_receipt_token = None

        def _has_unretired_provider_exposure() -> bool:
            return any(
                count > pre_generation_rejection_target_counts[target_id]
                for target_id, count in dispatched_target_counts.items()
            )

        async def _settle_shielded(*, status: str, error: str = "") -> None:
            reservation.metadata["llm_dispatched_target_counts"] = dict(
                dispatched_target_counts
            )
            reservation.metadata["llm_pre_generation_rejection_target_counts"] = (
                dict(pre_generation_rejection_target_counts)
            )
            reservation.metadata["llm_provider_dispatch_receipts"] = list(
                dispatch_receipts
            )
            try:
                provider_temperature_metadata = _temperature_provider_metadata(client)
                if (
                    "temperature_requested" in reservation.metadata
                    and reservation.metadata.get("temperature_requested") is None
                    and provider_temperature_metadata.get(
                        "temperature_provider_drop_reason"
                    )
                    == "unsupported_sampling_controls"
                ):
                    provider_temperature_metadata["temperature_provider_dropped"] = False
                    provider_temperature_metadata["temperature_provider_drop_reason"] = ""
                reservation.metadata.update(provider_temperature_metadata)
            except Exception:
                pass
            task = asyncio.create_task(
                self.settle(
                    reservation,
                    observations,
                    status=status,
                    error=error,
                )
            )
            try:
                await asyncio.shield(task)
            except asyncio.CancelledError:
                while not task.done():
                    try:
                        await asyncio.shield(task)
                    except asyncio.CancelledError:
                        continue
                try:
                    task.exception()
                except asyncio.CancelledError:
                    pass
                raise
            finally:
                if task.done():
                    settlement_complete.set()

        def _usage_callback(record: ProviderUsageRecord) -> None:
            nonlocal settled
            target_id = str(_PROVIDER_DISPATCH_TARGET.get() or "")
            if not target_id and len(active_target_ids) == 1:
                target_id = next(iter(active_target_ids))
            if (
                target_id
                and dispatched_target_counts[target_id]
                <= callback_target_counts[target_id]
            ):
                _mark_dispatched()
            elif not target_id and not provider_dispatched:
                _mark_dispatched()
            if target_id:
                callback_target_counts[target_id] += 1
            if target_id and (
                not record.reservation_target_id
                or int(record.reservation_dispatch_ordinal or 0) <= 0
            ):
                record = replace(
                    record,
                    reservation_target_id=(
                        record.reservation_target_id or target_id
                    ),
                    reservation_dispatch_ordinal=(
                        record.reservation_dispatch_ordinal
                        or callback_target_counts[target_id]
                    ),
                )
            if settled:
                dispatch_tasks = late_dispatch_tasks.get(target_id, [])
                dispatch_task = dispatch_tasks.pop(0) if dispatch_tasks else None

                async def _record_after_dispatch() -> None:
                    if dispatch_task is not None:
                        try:
                            await asyncio.shield(dispatch_task)
                        except Exception:
                            pass
                    await self.record_late_usage(
                        reservation,
                        record,
                        retire_cancelled_exposure=dispatch_task is None,
                    )

                task = asyncio.create_task(_record_after_dispatch())
                self._pending_late_usage_tasks.add(task)
                task.add_done_callback(
                    mark_runtime_owned_callback(self._pending_late_usage_tasks.discard)
                )
                return
            observations.append(record)

        try:
            if on_reserved is not None:
                reserved_result = on_reserved(reservation)
                if inspect.isawaitable(reserved_result):
                    await reserved_result
            if not precise_dispatch_marker:
                provider_dispatched = True
                dispatched_target_counts.update(active_target_ids)
            dispatch_context_token = _PROVIDER_DISPATCH_MARKER.set(_mark_dispatched)
            dispatch_observer_token = _PROVIDER_DISPATCH_OBSERVER.set(
                _authorize_concrete_dispatch
            )
            pending_dispatch_receipt_token = (
                _PROVIDER_PENDING_DISPATCH_RECEIPT.set({})
            )
            result = invoke(_usage_callback)
            if inspect.isawaitable(result):
                result = await result
        except asyncio.CancelledError as exc:
            if provider_dispatch_lease is not None:
                provider_dispatch_lease.annotate_exception(exc)
            else:
                try:
                    setattr(
                        exc,
                        "provider_dispatches_started",
                        len(counted_dispatch_authorization_ids),
                    )
                except Exception:
                    pass
            _reset_dispatch_context()
            settled = True
            cancel_status = "cancelled"
            if provider_dispatched and _has_unretired_provider_exposure():
                cancel_status = "cancelled_provider_inflight"
                waits_for_provider = _client_waits_for_provider_after_local_cancel(
                    client
                )
                reservation.metadata.update(
                    {
                        "llm_cancelled_provider_inflight": True,
                        "llm_cancelled_provider_exposure_risk": True,
                        "llm_cancelled_provider_exposure_reason": (
                            "soft_deadline_or_unbounded_request_timeout"
                            if waits_for_provider
                            else "confirmed_dispatch_cancelled_before_usage"
                        ),
                    }
                )
            await _settle_shielded(
                status=cancel_status,
                error=format_exception(exc)[:500],
            )
            raise
        except BaseException as exc:
            if provider_dispatch_lease is not None:
                provider_dispatch_lease.annotate_exception(exc)
            else:
                try:
                    setattr(
                        exc,
                        "provider_dispatches_started",
                        len(counted_dispatch_authorization_ids),
                    )
                except Exception:
                    pass
            _reset_dispatch_context()
            settled = True
            deadline_record = llm_retry_deadline_record_from_exception(exc)
            if deadline_record:
                reservation.metadata.update(deadline_record)
            no_charge_retryable_exception = False
            if not provider_dispatched or not _has_unretired_provider_exposure():
                no_charge_retryable_exception = True
            if retryable_exception_no_charge is not None and not observations:
                try:
                    no_charge_retryable_exception = bool(
                        retryable_exception_no_charge(exc)
                    )
                    if (
                        precise_dispatch_marker
                        and provider_dispatched
                        and _has_unretired_provider_exposure()
                    ):
                        # A precise transport receipt says generation exposure
                        # really occurred.  Retryability does not make that
                        # dispatched request free; retain conservative cost
                        # until a correlated late usage/rejection receipt.
                        no_charge_retryable_exception = False
                except Exception:
                    no_charge_retryable_exception = False
            if no_charge_retryable_exception:
                reservation.metadata.update(
                    {
                        "llm_retryable_exception_no_charge": True,
                        "llm_retryable_exception_no_charge_kind": type(exc).__name__,
                    }
                )
            await _settle_shielded(
                status=(
                    "pre_dispatch_failure"
                    if not provider_dispatched
                    or not _has_unretired_provider_exposure()
                    else "retryable_exception_no_charge"
                    if no_charge_retryable_exception
                    else "exception"
                ),
                error=format_exception(exc)[:500],
            )
            raise
        _reset_dispatch_context()
        settled = True
        await _settle_shielded(status="success")
        return result

    async def drain_late_usage(self, *, timeout_s: float = 1.0) -> None:
        """Best-effort wait for late provider usage tasks already reported."""

        # With no dispatched/reserved request, no provider callback can arrive.
        # Once any request has existed, however, a provider wrapper may enqueue
        # its late callback on the next loop turn before the task registry or a
        # late-hold marker becomes visible; retain the grace period then.
        if self._reservations <= 0:
            return

        deadline = time.monotonic() + max(0.0, float(timeout_s or 0.0))
        while True:
            remaining = max(0.0, deadline - time.monotonic())
            tasks = set(self._pending_late_usage_tasks)
            if tasks:
                try:
                    done, pending = await asyncio.wait(
                        tasks,
                        timeout=min(0.05, remaining),
                    )
                except Exception:
                    done, pending = set(), tasks
                for task in done:
                    try:
                        task.exception()
                    except asyncio.CancelledError:
                        pass
                    except Exception:
                        pass
                self._pending_late_usage_tasks.intersection_update(pending)
            elif remaining > 0.0:
                await asyncio.sleep(min(0.05, remaining))
            if time.monotonic() >= deadline:
                break
        async with self._lock:
            if self._final_accounting_frozen:
                return
            for reservation_id in list(self._late_hold_reservations):
                held_cost = float(
                    self._active_reservations.pop(reservation_id, 0.0)
                    or 0.0
                )
                self._reserved_cost_usd = max(
                    0.0,
                    self._reserved_cost_usd - held_cost,
                )
                self._late_hold_reservations.discard(reservation_id)

    async def freeze_final_accounting(self) -> None:
        """Reject provider receipts arriving after the final summary cut."""

        async with self._lock:
            self._final_accounting_frozen = True

    async def _record_event_locked(self, record: Dict[str, Any]) -> bool:
        sink = self.event_sink
        if sink is None:
            return True
        payload = dict(record)
        if str(payload.get("phase") or "") == "llm_usage":
            # Every LLM-ledger event is a possible watchdog observation point.
            # Publish the cumulative authority bundle atomically even for
            # reversal/admission events, not only ordinary settle.
            # Otherwise a later event can update accounted cost while leaving
            # the watchdog to combine it with stale observed/unknown fields.
            unknown_exposure = float(self._unknown_cost_usd)
            accounting_incomplete = bool(unknown_exposure > 1e-12)
            payload.update(
                {
                    "llm_observed_usage_cost_usd": float(self._exact_cost_usd),
                    "llm_conservative_unknown_exposure_usd": unknown_exposure,
                    "cost_accounting_incomplete": accounting_incomplete,
                    "llm_cost_accounting_incomplete": accounting_incomplete,
                    "llm_budget_accounted_cost_is_conservative_upper_bound": (
                        accounting_incomplete
                    ),
                    "llm_budget_accounted_cost_usd": float(
                        self.accounted_cost_usd
                    ),
                    "llm_budget_committed_cost_usd": float(
                        self.committed_cost_usd
                    ),
                }
            )
        try:
            result = sink(payload)
            if inspect.isawaitable(result):
                await result
        except Exception:
            return False
        return True

    def summary(self) -> Dict[str, Any]:
        unknown_exposure = float(self._unknown_cost_usd)
        accounting_incomplete = bool(unknown_exposure > 1e-12)
        summary: Dict[str, Any] = {
            "input_tokens": int(self._input_tokens),
            "output_tokens": int(self._output_tokens),
            "cached_input_tokens": int(self._cached_input_tokens),
            "cache_write_tokens": int(self._cache_write_tokens),
            "prompt_cache_miss_tokens": int(self._prompt_cache_miss_tokens),
            "reasoning_output_tokens": int(self._reasoning_output_tokens),
            "cost_usd": float(self._exact_cost_usd),
            # ``cost_usd`` is derived only from provider-reported usage.
            # Budget accounting deliberately adds a worst-case estimate for
            # dispatched requests whose usage never arrived. Keep explicit
            # aliases and authority flags so an upper bound is not mistaken
            # for an invoice or observed spend in run summaries.
            "llm_observed_usage_cost_usd": float(self._exact_cost_usd),
            "estimated_unknown_cost_usd": unknown_exposure,
            "llm_conservative_unknown_exposure_usd": unknown_exposure,
            "cost_accounting_incomplete": accounting_incomplete,
            "llm_cost_accounting_incomplete": accounting_incomplete,
            "llm_budget_accounted_cost_is_conservative_upper_bound": (
                accounting_incomplete
            ),
            "llm_budget_accounted_cost_usd": float(self.accounted_cost_usd),
            "llm_budget_committed_cost_usd": float(self.committed_cost_usd),
            "llm_budget_reserved_cost_usd": float(self.reserved_cost_usd),
            "max_cost_usd": float(self.max_cost_usd),
            "llm_budget_remaining_usd": self.remaining_usd(),
            "llm_budget_unspent_usd": self.unspent_usd(),
            "llm_cost_budget_enabled": bool(self.budget_enabled),
            "llm_cost_budget_exhausted": bool(self.exhausted()),
            "llm_cost_budget_terminal_reason": self._terminal_reason,
            "llm_usage_events": int(self._events),
            "llm_usage_missing_events": int(self._usage_missing_events),
            "llm_pricing_unknown_events": int(self._pricing_unknown_events),
            "llm_cancelled_provider_inflight_events": int(
                self._cancelled_provider_inflight_events
            ),
            "llm_cancelled_provider_inflight_estimated_cost_usd": float(
                self._cancelled_provider_inflight_estimated_cost_usd
            ),
            "llm_retryable_exception_no_charge_events": int(
                self._retryable_exception_no_charge_events
            ),
            "llm_budget_reservations": int(self._reservations),
            "llm_budget_rejections": int(self._budget_rejections),
            "llm_cost_budget_reserve_output_tokens": int(self.reserve_output_tokens),
            "llm_final_accounting_frozen": bool(self._final_accounting_frozen),
        }
        for role, totals in self._role_totals.items():
            prefix = str(role or "llm").strip()
            if not prefix:
                continue
            summary[f"{prefix}_input_tokens"] = int(totals["input_tokens"])
            summary[f"{prefix}_output_tokens"] = int(totals["output_tokens"])
            summary[f"{prefix}_cached_input_tokens"] = int(
                totals["cached_input_tokens"]
            )
            summary[f"{prefix}_cache_write_tokens"] = int(
                totals.get("cache_write_tokens", 0)
            )
            summary[f"{prefix}_prompt_cache_miss_tokens"] = int(
                totals["prompt_cache_miss_tokens"]
            )
            summary[f"{prefix}_reasoning_output_tokens"] = int(
                totals["reasoning_output_tokens"]
            )
            summary[f"{prefix}_cost_usd"] = float(totals["cost_usd"])
            summary[f"{prefix}_estimated_unknown_cost_usd"] = float(
                totals["estimated_unknown_cost_usd"]
            )
            summary[f"{prefix}_model"] = str(totals.get("model") or "")
        return summary


async def metered_or_plain_call(
    *,
    cost_controller: Optional[CostBudgetController],
    client: Any,
    messages: Sequence[Dict[str, Any]],
    role: str,
    scope: str,
    call_kind: str,
    invoke: Callable[[Optional[Callable[[ProviderUsageRecord], Any]]], Any],
    action_id: str = "",
    tools: Optional[Sequence[Dict[str, Any]]] = None,
    max_tokens_override: Optional[int] = None,
    candidate_count: int = 1,
    metadata: Optional[Mapping[str, Any]] = None,
    retryable_exception_no_charge: Optional[Callable[[BaseException], bool]] = None,
    on_reserved: Optional[Callable[[Any], Any]] = None,
    provider_dispatch_lease: Optional[ProviderDispatchAttemptLease] = None,
) -> Any:
    """Call through a cost controller when present, otherwise pass no callback."""

    usage_metadata = llm_usage_context_metadata(metadata)
    if cost_controller is None:
        dispatch_attempt_limit = max(
            0,
            int(usage_metadata.get("provider_dispatch_max_attempts", 0) or 0),
        )
        if not dispatch_attempt_limit:
            pending_receipt_token = _PROVIDER_PENDING_DISPATCH_RECEIPT.set({})
            try:
                result = invoke(None)
                if inspect.isawaitable(result):
                    return await result
                return result
            finally:
                _PROVIDER_PENDING_DISPATCH_RECEIPT.reset(
                    pending_receipt_token
                )
        if (
            bool(getattr(client, "supports_transport_dispatch_marker", False))
            and not bool(
                getattr(
                    client,
                    "supports_transport_dispatch_authorization",
                    False,
                )
            )
        ):
            raise ProviderDispatchAttemptLimitExceeded(
                "provider dispatch attempt limit requires awaited transport "
                "authorization; marker-only client cannot enforce the ceiling"
            )

        # Retry policy must not silently become unbounded merely because cost
        # accounting was disabled. Install the same pre-transport ceiling used
        # by CostBudgetController while preserving any outer live-dispatch
        # observer.
        inherited_dispatch_observer = _PROVIDER_DISPATCH_OBSERVER.get()
        inherited_dispatch_marker = _PROVIDER_DISPATCH_MARKER.get()
        live_plain_authorization_ids: set[str] = set()
        plain_authorization_lease_receipt_ids: Dict[str, str] = {}

        async def _authorize_plain_dispatch(
            details: Mapping[str, Any],
        ) -> Dict[str, Any]:
            require_hard_timeout_capability_active(
                "plain provider transport authorization"
            )
            next_ordinal = len(live_plain_authorization_ids) + 1
            target_id = str(
                dict(details or {}).get("target_id")
                or _PROVIDER_DISPATCH_TARGET.get()
                or ""
            ).strip()
            if next_ordinal > dispatch_attempt_limit:
                raise ProviderDispatchAttemptLimitExceeded(
                    "provider dispatch attempt limit exhausted before "
                    f"dispatch (limit={dispatch_attempt_limit}, "
                    f"next_ordinal={next_ordinal})",
                    provider_dispatches_started=len(
                        live_plain_authorization_ids
                    ),
                    dispatch_attempt_limit=dispatch_attempt_limit,
                    next_dispatch_ordinal=next_ordinal,
                    provider_dispatch_attempt_limit_target_id=target_id,
                )
            lease_receipt = (
                await provider_dispatch_lease.authorize()
                if provider_dispatch_lease is not None
                else {}
            )
            authorization_id = f"plain-dispatch-authorization:{uuid.uuid4().hex}"
            live_plain_authorization_ids.add(authorization_id)
            plain_authorization_lease_receipt_ids[authorization_id] = str(
                lease_receipt.get("provider_dispatch_lease_receipt_id") or ""
            )
            receipt = {
                **dict(details or {}),
                **lease_receipt,
                "dispatch_ordinal": next_ordinal,
                "plain_dispatch_authorization_id": authorization_id,
            }
            if inherited_dispatch_observer is not None:
                try:
                    try:
                        inspect.signature(inherited_dispatch_observer).bind(receipt)
                    except (TypeError, ValueError):
                        observed = inherited_dispatch_observer()
                    else:
                        observed = inherited_dispatch_observer(receipt)
                    if inspect.isawaitable(observed):
                        observed = await observed
                    if isinstance(observed, Mapping):
                        receipt.update(dict(observed))
                        # Nested progress observers may enrich a receipt, but
                        # they do not own this metering invocation's local or
                        # shared dispatch authority.
                        receipt.update(lease_receipt)
                        receipt["plain_dispatch_authorization_id"] = (
                            authorization_id
                        )
                except BaseException:
                    live_plain_authorization_ids.discard(authorization_id)
                    plain_authorization_lease_receipt_ids.pop(
                        authorization_id,
                        None,
                    )
                    if provider_dispatch_lease is not None:
                        provider_dispatch_lease.retire(receipt)
                    raise
            return receipt

        def _mark_plain_dispatch(
            event: str = "dispatch",
            details: Mapping[str, Any] | None = None,
        ) -> None:
            if str(event or "").strip() == "pre_generation_rejection":
                authorization_id = str(
                    dict(details or {}).get(
                        "plain_dispatch_authorization_id"
                    )
                    or ""
                ).strip()
                expected_lease_receipt_id = (
                    plain_authorization_lease_receipt_ids.get(
                        authorization_id,
                        "",
                    )
                )
                provided_lease_receipt_id = str(
                    dict(details or {}).get(
                        "provider_dispatch_lease_receipt_id"
                    )
                    or ""
                ).strip()
                authorization_is_live = bool(
                    authorization_id in live_plain_authorization_ids
                    and (
                        provider_dispatch_lease is None
                        or (
                            expected_lease_receipt_id
                            and provided_lease_receipt_id
                            == expected_lease_receipt_id
                        )
                    )
                )
                if authorization_is_live:
                    live_plain_authorization_ids.remove(authorization_id)
                    plain_authorization_lease_receipt_ids.pop(
                        authorization_id,
                        None,
                    )
                    if provider_dispatch_lease is not None:
                        provider_dispatch_lease.retire(details or {})
                    _track_provider_dispatch_event(
                        "pre_generation_rejection",
                        details or {},
                    )
            else:
                authorization_id = str(
                    dict(details or {}).get(
                        "plain_dispatch_authorization_id"
                    )
                    or ""
                ).strip()
                if authorization_id in live_plain_authorization_ids:
                    if provider_dispatch_lease is not None:
                        provider_dispatch_lease.mark_dispatched(details or {})
                    _track_provider_dispatch_event("dispatch", details or {})
            if inherited_dispatch_marker is not None:
                inherited_dispatch_marker(event, details or {})

        marker_token = _PROVIDER_DISPATCH_MARKER.set(_mark_plain_dispatch)
        pending_receipt_token = _PROVIDER_PENDING_DISPATCH_RECEIPT.set({})
        try:
            with provider_dispatch_observer(_authorize_plain_dispatch):
                result = invoke(None)
                if inspect.isawaitable(result):
                    return await result
                return result
        except BaseException as exc:
            if provider_dispatch_lease is not None:
                provider_dispatch_lease.annotate_exception(exc)
            else:
                try:
                    setattr(
                        exc,
                        "provider_dispatches_started",
                        len(live_plain_authorization_ids),
                    )
                except Exception:
                    pass
            raise
        finally:
            _PROVIDER_PENDING_DISPATCH_RECEIPT.reset(pending_receipt_token)
            _PROVIDER_DISPATCH_MARKER.reset(marker_token)
    return await cost_controller.metered_call(
        client=client,
        messages=messages,
        role=role,
        scope=scope,
        action_id=action_id,
        call_kind=call_kind,
        tools=tools,
        max_tokens_override=max_tokens_override,
        candidate_count=candidate_count,
        metadata=usage_metadata,
        retryable_exception_no_charge=retryable_exception_no_charge,
        on_reserved=on_reserved,
        provider_dispatch_lease=provider_dispatch_lease,
        invoke=invoke,
    )


async def call_with_optional_usage_callback(
    method: Callable[..., Any],
    *args: Any,
    usage_callback: Optional[Callable[[ProviderUsageRecord], Any]] = None,
    required_keywords: Sequence[str] = (),
    **kwargs: Any,
) -> Any:
    """Invoke a client method while preserving older fake/client signatures.

    Callers may mark phase-critical controls as required.  Silently dropping a
    required output cap would make cost admission reserve a different request
    from the one sent to the provider; dropping a required reasoning/format
    control can similarly defeat a bounded structured phase.
    """

    def _accepts_keyword(key: str) -> bool:
        try:
            signature = inspect.signature(method)
        except (TypeError, ValueError):
            return True
        parameters = signature.parameters
        if key in parameters:
            return True
        return any(
            parameter.kind is inspect.Parameter.VAR_KEYWORD
            for parameter in parameters.values()
        )

    call_kwargs = dict(kwargs)
    request_receipt: Optional[MiniRequestEnvelopeReceipt] = None
    request_policy = call_kwargs.get("max_tokens_override")
    if isinstance(request_policy, MiniRequestEnvelopePolicy):
        owner = getattr(method, "__self__", None)
        is_wrapper = bool(
            isinstance(getattr(owner, "members", None), list)
            or isinstance(getattr(owner, "clients", None), list)
        )
        if owner is not None and not is_wrapper:
            request_receipt = await request_policy.resolve_for(owner)
            call_kwargs["max_tokens_override"] = int(
                request_receipt.max_output_tokens
            )
            if "reasoning_effort_override" in call_kwargs:
                call_kwargs["reasoning_effort_override"] = (
                    request_receipt.effective_reasoning_effort or None
                )
    required = {str(key) for key in list(required_keywords or ()) if str(key)}
    if usage_callback is not None:
        call_kwargs["usage_callback"] = usage_callback
    for key in (
        "usage_callback",
        "max_tokens_override",
        "reasoning_effort_override",
        "response_format",
        "deadline",
        "request_timeout_override_s",
        "operation_timeout_override_s",
    ):
        if key in call_kwargs and not _accepts_keyword(key):
            if key in required:
                method_name = str(getattr(method, "__qualname__", "") or method)
                raise RequiredProviderKeywordUnsupported(
                    f"{method_name} does not accept required keyword {key!r}"
                )
            call_kwargs.pop(key, None)
    def invoke() -> Any:
        return method(*args, **call_kwargs)

    if request_receipt is not None:
        with bind_mini_request_envelope_receipt(request_receipt):
            result = invoke()
            if inspect.isawaitable(result):
                return await result
            return result
    result = invoke()
    if inspect.isawaitable(result):
        return await result
    return result


def usage_totals_from_clients(
    role_clients: Iterable[tuple[str, Any]],
) -> Dict[str, Any]:
    """Fallback summary for callers without request-scoped controller events."""

    totals: Dict[str, Any] = {
        "input_tokens": 0,
        "output_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_tokens": 0,
        "prompt_cache_miss_tokens": 0,
        "usage_missing_responses": 0,
        "cost_accounting_incomplete": False,
        "cost_usd": 0.0,
    }
    for role, client in role_clients:
        if client is None:
            continue
        usage = getattr(client, "token_usage", lambda: {})()
        if not isinstance(usage, dict):
            usage = {}
        input_tokens = int(usage.get("input_tokens", 0) or 0)
        output_tokens = int(usage.get("output_tokens", 0) or 0)
        cached_tokens = int(usage.get("cached_input_tokens", 0) or 0)
        cache_write_tokens = int(usage.get("cache_write_tokens", 0) or 0)
        miss_tokens = int(usage.get("prompt_cache_miss_tokens", 0) or 0)
        missing_responses = int(usage.get("usage_missing_responses", 0) or 0)
        model, base_url = _client_model_base(client)
        reported_aggregate_cost = _usage_float(usage.get("cost_usd"))
        if reported_aggregate_cost is not None and bool(
            usage.get("cost_usd_authoritative", False)
        ):
            cost = reported_aggregate_cost
        else:
            # Cumulative token counters do not retain per-request prompt sizes,
            # so they cannot safely reapply long-context tiers. Request-scoped
            # OpenAI clients publish their accumulated exact cost above.
            has_unpriced_partition = "unpriced_input_tokens" in usage
            fallback_input_tokens = (
                int(usage.get("unpriced_input_tokens", 0) or 0)
                if has_unpriced_partition
                else input_tokens
            )
            fallback_output_tokens = (
                int(usage.get("unpriced_output_tokens", 0) or 0)
                if has_unpriced_partition
                else output_tokens
            )
            fallback_cached_tokens = (
                int(usage.get("unpriced_cached_input_tokens", 0) or 0)
                if has_unpriced_partition
                else cached_tokens
            )
            pricing = lookup_known_token_pricing(base_url, model)
            cost = (
                compute_cost_usd(
                    fallback_input_tokens,
                    fallback_output_tokens,
                    fallback_cached_tokens,
                    pricing,
                )
                if pricing is not None
                else 0.0
            )
            if has_unpriced_partition:
                cost = float(cost or 0.0) + float(reported_aggregate_cost or 0.0)
            else:
                cost = max(
                    float(cost or 0.0),
                    float(reported_aggregate_cost or 0.0),
                )
        prefix = str(role or "llm").strip()
        totals[f"{prefix}_input_tokens"] = input_tokens
        totals[f"{prefix}_output_tokens"] = output_tokens
        totals[f"{prefix}_cached_input_tokens"] = cached_tokens
        totals[f"{prefix}_cache_write_tokens"] = cache_write_tokens
        totals[f"{prefix}_prompt_cache_miss_tokens"] = miss_tokens
        totals[f"{prefix}_usage_missing_responses"] = missing_responses
        totals[f"{prefix}_cost_usd"] = cost
        totals[f"{prefix}_model"] = model
        totals["input_tokens"] += input_tokens
        totals["output_tokens"] += output_tokens
        totals["cached_input_tokens"] += cached_tokens
        totals["cache_write_tokens"] += cache_write_tokens
        totals["prompt_cache_miss_tokens"] += miss_tokens
        totals["usage_missing_responses"] += missing_responses
        totals["cost_accounting_incomplete"] = bool(
            totals["cost_accounting_incomplete"] or missing_responses > 0
        )
        totals["cost_usd"] += cost
    return totals
