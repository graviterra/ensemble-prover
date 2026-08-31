"""Provider pricing catalogs, capability metadata, and bounded refresh logic."""

from __future__ import annotations

import asyncio
import concurrent.futures
import json
import math
import os
import threading
import time
from dataclasses import asdict, dataclass
from typing import Optional, Tuple
from urllib.parse import urlsplit
from urllib.request import Request, urlopen

PricingTuple = Tuple[float, float, float]


@dataclass(frozen=True)
class OpenRouterReasoningCapabilities:
    """Reasoning controls explicitly advertised by OpenRouter's model catalog."""

    supports_reasoning: bool = False
    supports_max_tokens: bool = False
    supports_disable: bool = False
    supported_efforts: tuple[str, ...] = ()
    default_enabled: Optional[bool] = None
    mandatory: Optional[bool] = None
    source: str = "openrouter_models_catalog"

    def to_record(self) -> dict[str, object]:
        return asdict(self)


# Official per-million-token pricing used by the shipped API-backed profiles.
# Tuple order: (input, cached_input, output).
_OPENAI_MODEL_PRICING: tuple[tuple[str, PricingTuple], ...] = (
    ("gpt-5.6-sol", (5.0, 0.5, 30.0)),
    ("gpt-5.6-terra", (2.0, 0.20, 12.00)),
    ("gpt-5.6-luna", (0.2, 0.02, 1.20)),
    # The unsuffixed GPT-5.6 API alias resolves to the Sol tier.
    ("gpt-5.6", (5.0, 0.5, 30.0)),
    ("gpt-5.4", (2.5, 0.25, 15.0)),
    ("gpt-5.2", (1.75, 0.175, 14.0)),
)

_OPENAI_GPT56_LONG_CONTEXT_THRESHOLD = 272_000
_OPENAI_GPT56_LONG_CONTEXT_INPUT_MULTIPLIER = 2.0
_OPENAI_GPT56_LONG_CONTEXT_OUTPUT_MULTIPLIER = 1.5
_OPENAI_LONG_CONTEXT_MODEL_PREFIXES = (
    "gpt-5.4",
    "gpt-5.6",
    "gpt-5.6-sol",
    "gpt-5.6-terra",
    "gpt-5.6-luna",
)

_DEEPSEEK_MODEL_PRICING: tuple[tuple[str, PricingTuple], ...] = (
    ("deepseek-v4-flash", (0.14, 0.0028, 0.28)),
    ("deepseek-v4-pro", (0.435, 0.003625, 0.87)),
)

_KNOWN_PROVIDER_HOSTS: dict[str, tuple[str, ...]] = {
    "openai": ("api.openai.com",),
    "deepseek": ("api.deepseek.com",),
    "openrouter": ("openrouter.ai",),
}

_OPENROUTER_MODELS_URL = "https://openrouter.ai/api/v1/models"
_OPENROUTER_PRICING_CACHE_TTL_S = 60 * 60
_OPENROUTER_PRICING_CACHE: dict[str, PricingTuple] = {}
_OPENROUTER_REASONING_CAPABILITY_CACHE: dict[
    str, OpenRouterReasoningCapabilities
] = {}
_OPENROUTER_REASONING_CAPABILITY_FETCHED_AT = 0.0
_OPENROUTER_PRICING_FETCHED_AT = 0.0
_OPENROUTER_PRICING_LOCK = threading.Lock()
_OPENROUTER_REFRESH_IN_FLIGHT: Optional[threading.Event] = None
_OPENROUTER_REFRESH_ERROR: Optional[BaseException] = None
_OPENROUTER_ASYNC_REFRESH_FUTURE: Optional[
    concurrent.futures.Future[dict[str, PricingTuple]]
] = None

# Exact user-facing routes that OpenRouter publishes under a different request
# identity. These aliases must be canonicalized before both pricing and HTTP
# dispatch; pricing alone must never authorize a provider-invalid model ID.
_OPENROUTER_REQUEST_MODEL_ALIASES: dict[str, str] = {
    "deepseek/deepseek-v4-pro-0423": "deepseek/deepseek-v4-pro",
    "deepseek/deepseek-v4-flash-latest": "~deepseek/deepseek-v4-flash-latest",
    "dedeepseek/deepseek-v4-pro-0423": "deepseek/deepseek-v4-pro",
    "dedeepseek/deepseek-v4-pro-0813": "deepseek/deepseek-v4-pro-0813",
    "dedeepseek/deepseek-v4-flash-latest": (
        "~deepseek/deepseek-v4-flash-latest"
    ),
}

# Verified against OpenRouter's public catalog on 2026-08-16 and OpenAI pricing
# on 2026-08-03. Use undiscounted/conservative rates for outage fallbacks rather
# than baking in time-window promotions. The moving Flash alias falls back to
# the higher current non-promotional V4 Flash rate. A fresh catalog snapshot
# always wins and suppresses fallback for missing IDs.
_OPENROUTER_VERIFIED_FALLBACK_PRICING: dict[str, PricingTuple] = {
    "deepseek/deepseek-v4-pro": (1.32, 0.044, 3.96),
    "deepseek/deepseek-v4-pro-0813": (1.32, 0.044, 3.96),
    "~deepseek/deepseek-v4-flash-latest": (0.14, 0.028, 0.28),
    "openai/gpt-5.6-luna": (0.2, 0.02, 1.2),
    "openai/gpt-5.6-luna-pro": (0.2, 0.02, 1.2),
}


class _OpenRouterPricingCatalog(dict[str, PricingTuple]):
    """One fetched catalog snapshot, including its capability sidecar."""

    def __init__(
        self,
        pricing: dict[str, PricingTuple],
        reasoning_capabilities: dict[str, OpenRouterReasoningCapabilities],
    ) -> None:
        super().__init__(pricing)
        self.reasoning_capabilities = dict(reasoning_capabilities)


def _base_url_hostname(base_url: str) -> str:
    raw = str(base_url or "").strip()
    if not raw:
        return ""
    parsed = urlsplit(raw if "://" in raw or raw.startswith("//") else f"//{raw}")
    return str(parsed.hostname or "").strip().lower().strip(".")


def provider_for_base_url(base_url: str) -> Optional[str]:
    """Return the known provider for *base_url* based on its normalized hostname."""
    hostname = _base_url_hostname(base_url)
    for provider, hosts in _KNOWN_PROVIDER_HOSTS.items():
        if hostname in hosts:
            return provider
    return None


def base_url_matches_provider(base_url: str, provider: str) -> bool:
    """Whether *base_url* resolves to a known hostname for *provider*."""
    return provider_for_base_url(base_url) == str(provider or "").strip().lower()


def canonical_openrouter_model_id(model: str) -> str:
    """Return the provider-valid ID for supported OpenRouter user aliases."""

    name = str(model or "").strip()
    lowered = name.lower()
    canonical = _OPENROUTER_REQUEST_MODEL_ALIASES.get(lowered)
    if canonical is not None:
        return canonical
    if "/" in name or not lowered.startswith("gpt-"):
        return name
    return f"openai/{lowered}"


def _looks_like_snapshot_suffix(suffix: str) -> bool:
    compact = str(suffix or "").replace("-", "")
    return 4 <= len(compact) <= 8 and compact.isdigit()


def _model_matches_known_prefix(name: str, prefix: str) -> bool:
    if name == prefix:
        return True
    if not name.startswith(f"{prefix}-"):
        return False
    return _looks_like_snapshot_suffix(name[len(prefix) + 1 :])


def _direct_provider_model_aliases(name: str) -> tuple[str, ...]:
    raw = str(name or "").strip().lower()
    if "/" not in raw:
        return (raw,)
    suffix = raw.rsplit("/", 1)[-1].strip()
    if suffix and suffix != raw:
        return (raw, suffix)
    return (raw,)


def _direct_openai_model_matches_any(
    base_url: str,
    model: str,
    prefixes: tuple[str, ...],
) -> bool:
    if provider_for_base_url(base_url) != "openai":
        return False
    return any(
        _model_matches_known_prefix(alias, prefix)
        for alias in _direct_provider_model_aliases(model)
        for prefix in prefixes
    )


def _normalize_usage_counts(
    input_tokens: int,
    output_tokens: int,
    cached_input_tokens: int,
) -> tuple[int, int, int]:
    input_i = max(0, int(input_tokens))
    output_i = max(0, int(output_tokens))
    cached_i = max(0, int(cached_input_tokens))
    cached_i = min(cached_i, input_i)
    return input_i, output_i, cached_i


def _openrouter_price_per_million(value: object) -> Optional[float]:
    try:
        price_per_token = float(value)  # OpenRouter catalog stores USD/token.
    except Exception:
        return None
    if not math.isfinite(price_per_token) or price_per_token < 0:
        return None
    return price_per_token * 1_000_000


def _openrouter_model_pricing(entry: object) -> Optional[PricingTuple]:
    if not isinstance(entry, dict):
        return None
    pricing = entry.get("pricing")
    if not isinstance(pricing, dict):
        return None
    input_per_m = _openrouter_price_per_million(pricing.get("prompt"))
    output_per_m = _openrouter_price_per_million(pricing.get("completion"))
    if input_per_m is None or output_per_m is None:
        return None
    cached_per_m = _openrouter_price_per_million(pricing.get("input_cache_read"))
    if cached_per_m is None:
        cached_per_m = input_per_m
    rates: list[PricingTuple] = [(input_per_m, cached_per_m, output_per_m)]
    if "overrides" in pricing:
        raw_overrides = pricing["overrides"]
        if not isinstance(raw_overrides, list):
            return None
        for raw_override in raw_overrides:
            if not isinstance(raw_override, dict):
                return None
            override_rates: list[float] = []
            for field, inherited in (
                ("prompt", input_per_m),
                ("input_cache_read", cached_per_m),
                ("completion", output_per_m),
            ):
                if field not in raw_override:
                    override_rates.append(inherited)
                    continue
                parsed = _openrouter_price_per_million(raw_override[field])
                if parsed is None:
                    # A malformed advertised charged rate makes this model's
                    # dollar cost unknown. Falling back to a lower base rate
                    # would let a hard cost budget admit an unsafe request.
                    return None
                override_rates.append(parsed)
            rates.append(
                (override_rates[0], override_rates[1], override_rates[2])
            )
    return (
        max(rate[0] for rate in rates),
        max(rate[1] for rate in rates),
        max(rate[2] for rate in rates),
    )


def _parse_openrouter_pricing_catalog(payload: object) -> dict[str, PricingTuple]:
    if not isinstance(payload, dict):
        return {}
    data = payload.get("data")
    if not isinstance(data, list):
        return {}
    parsed: dict[str, PricingTuple] = {}
    for entry in data:
        if not isinstance(entry, dict):
            continue
        pricing = _openrouter_model_pricing(entry)
        if pricing is None:
            continue
        for key in (entry.get("id"), entry.get("canonical_slug")):
            name = str(key or "").strip().lower()
            if name:
                parsed[name] = pricing
    return parsed


def _openrouter_reasoning_capabilities(
    entry: object,
) -> OpenRouterReasoningCapabilities:
    if not isinstance(entry, dict):
        return OpenRouterReasoningCapabilities()
    supported_parameters = entry.get("supported_parameters")
    parameter_names = {
        str(value or "").strip().lower()
        for value in (
            supported_parameters if isinstance(supported_parameters, list) else []
        )
        if str(value or "").strip()
    }
    raw = entry.get("reasoning")
    reasoning = raw if isinstance(raw, dict) else {}
    raw_efforts = reasoning.get("supported_efforts")
    efforts = tuple(
        dict.fromkeys(
            str(value or "").strip().lower()
            for value in (raw_efforts if isinstance(raw_efforts, list) else [])
            if str(value or "").strip()
        )
    )
    default_enabled = (
        reasoning.get("default_enabled")
        if isinstance(reasoning.get("default_enabled"), bool)
        else None
    )
    mandatory = (
        reasoning.get("mandatory")
        if isinstance(reasoning.get("mandatory"), bool)
        else None
    )
    supports_reasoning = bool(reasoning) or "reasoning" in parameter_names
    supports_disable = bool(
        supports_reasoning
        and (
            mandatory is False
            or default_enabled is False
            or "none" in efforts
        )
    )
    return OpenRouterReasoningCapabilities(
        supports_reasoning=supports_reasoning,
        supports_max_tokens=(reasoning.get("supports_max_tokens") is True),
        supports_disable=supports_disable,
        supported_efforts=efforts,
        default_enabled=default_enabled,
        mandatory=mandatory,
    )


def _parse_openrouter_reasoning_catalog(
    payload: object,
) -> dict[str, OpenRouterReasoningCapabilities]:
    if not isinstance(payload, dict):
        return {}
    data = payload.get("data")
    if not isinstance(data, list):
        return {}
    parsed: dict[str, OpenRouterReasoningCapabilities] = {}
    for entry in data:
        if not isinstance(entry, dict):
            continue
        capabilities = _openrouter_reasoning_capabilities(entry)
        for key in (entry.get("id"), entry.get("canonical_slug")):
            name = str(key or "").strip().lower()
            if name:
                parsed[name] = capabilities
    return parsed


def _fetch_openrouter_pricing_catalog(
    *,
    timeout_s: float = 10.0,
) -> dict[str, PricingTuple]:
    headers = {
        "Accept": "application/json",
        "User-Agent": "automated-ensemble-theorem-prover/mini-prover",
    }
    api_key = str(os.environ.get("OPENROUTER_API_KEY") or "").strip()
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    request = Request(
        _OPENROUTER_MODELS_URL,
        headers=headers,
    )
    with urlopen(request, timeout=max(0.1, float(timeout_s or 0.0))) as response:
        payload = json.loads(response.read().decode("utf-8"))
    return _OpenRouterPricingCatalog(
        _parse_openrouter_pricing_catalog(payload),
        _parse_openrouter_reasoning_catalog(payload),
    )


def refresh_openrouter_pricing_cache(
    *,
    force: bool = False,
    timeout_s: float = 10.0,
) -> dict[str, PricingTuple]:
    """Refresh and return cached OpenRouter model pricing.

    The public model catalog exposes prices per token; the local pricing table
    stores per-million-token tuples so the existing cost math can be reused.
    """

    global _OPENROUTER_PRICING_CACHE, _OPENROUTER_PRICING_FETCHED_AT
    global _OPENROUTER_REASONING_CAPABILITY_CACHE
    global _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT
    global _OPENROUTER_REFRESH_IN_FLIGHT, _OPENROUTER_REFRESH_ERROR
    now = time.time()
    with _OPENROUTER_PRICING_LOCK:
        if (
            not force
            and _OPENROUTER_PRICING_FETCHED_AT > 0.0
            and now - _OPENROUTER_PRICING_FETCHED_AT
            < _OPENROUTER_PRICING_CACHE_TTL_S
            and _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT > 0.0
            and now - _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT
            < _OPENROUTER_PRICING_CACHE_TTL_S
        ):
            return dict(_OPENROUTER_PRICING_CACHE)
        stale_catalog = dict(_OPENROUTER_PRICING_CACHE)
        refresh_event = _OPENROUTER_REFRESH_IN_FLIGHT
        owns_refresh = refresh_event is None
        if owns_refresh:
            refresh_event = threading.Event()
            _OPENROUTER_REFRESH_IN_FLIGHT = refresh_event
            _OPENROUTER_REFRESH_ERROR = None

    if not owns_refresh:
        # Waiting releases the catalog lock. Lookups and unrelated event loops
        # must remain responsive while the one network owner fetches.
        assert refresh_event is not None
        if not refresh_event.wait(timeout=max(0.1, float(timeout_s or 0.0))):
            if stale_catalog:
                return stale_catalog
            raise TimeoutError("OpenRouter catalog refresh single-flight timed out")
        with _OPENROUTER_PRICING_LOCK:
            refreshed_catalog = dict(_OPENROUTER_PRICING_CACHE)
            refresh_error = _OPENROUTER_REFRESH_ERROR
        if refreshed_catalog:
            return refreshed_catalog
        if refresh_error is not None:
            raise refresh_error
        return refreshed_catalog

    assert refresh_event is not None
    try:
        # Never hold the shared snapshot lock across DNS, connect, or reads.
        catalog = _fetch_openrouter_pricing_catalog(timeout_s=timeout_s)
    except BaseException as exc:
        with _OPENROUTER_PRICING_LOCK:
            _OPENROUTER_REFRESH_ERROR = exc
            _OPENROUTER_REFRESH_IN_FLIGHT = None
            refresh_event.set()
            preserved_catalog = dict(_OPENROUTER_PRICING_CACHE)
        if preserved_catalog:
            return preserved_catalog
        raise

    capabilities = getattr(catalog, "reasoning_capabilities", {})
    refreshed_at = time.time()
    with _OPENROUTER_PRICING_LOCK:
        # Pricing, capabilities, and their freshness markers are one snapshot.
        _OPENROUTER_PRICING_CACHE = dict(catalog)
        _OPENROUTER_REASONING_CAPABILITY_CACHE = dict(capabilities)
        _OPENROUTER_PRICING_FETCHED_AT = refreshed_at
        _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT = refreshed_at
        _OPENROUTER_REFRESH_ERROR = None
        _OPENROUTER_REFRESH_IN_FLIGHT = None
        refresh_event.set()
        return dict(_OPENROUTER_PRICING_CACHE)


def _openrouter_async_refresh_future(
    *,
    timeout_s: float = 10.0,
) -> concurrent.futures.Future[dict[str, PricingTuple]]:
    """Return one process-wide refresh future without occupying waiter threads.

    ``asyncio.to_thread(refresh_openrouter_pricing_cache)`` single-flights the
    network owner, but every concurrent async waiter still consumes a default
    executor worker inside ``threading.Event.wait``.  A concurrent future is
    safely awaitable from any event loop, while exactly one daemon owner thread
    performs (or waits for) the synchronous refresh operation.
    """

    global _OPENROUTER_ASYNC_REFRESH_FUTURE
    with _OPENROUTER_PRICING_LOCK:
        current = _OPENROUTER_ASYNC_REFRESH_FUTURE
        if current is not None and not current.done():
            return current
        future: concurrent.futures.Future[dict[str, PricingTuple]] = (
            concurrent.futures.Future()
        )
        _OPENROUTER_ASYNC_REFRESH_FUTURE = future

        def run_refresh() -> None:
            try:
                result = refresh_openrouter_pricing_cache(timeout_s=timeout_s)
            except BaseException as exc:
                future.set_exception(exc)
            else:
                future.set_result(result)

        threading.Thread(
            target=run_refresh,
            name="openrouter-catalog-refresh",
            daemon=True,
        ).start()
        return future


async def _await_openrouter_refresh_future(
    future: concurrent.futures.Future[dict[str, PricingTuple]],
    *,
    timeout_s: Optional[float] = None,
) -> dict[str, PricingTuple]:
    """Await a process-wide refresh without threads or cross-loop callbacks.

    ``asyncio.wrap_future`` installs a cross-thread wakeup callback. If another
    executor callback wakes and drains the loop's self-pipe at the same time,
    the refresh callback can remain queued without another wakeup, leaving a
    caller hung even though the concurrent future is complete. Polling the
    process-wide future keeps waiters thread-free and cancellation-local while
    avoiding that lost-wakeup boundary.
    """

    loop = asyncio.get_running_loop()
    expires_at = (
        loop.time() + max(0.0, float(timeout_s))
        if timeout_s is not None
        else None
    )
    while not future.done():
        if expires_at is None:
            await asyncio.sleep(0.005)
            continue
        remaining_s = expires_at - loop.time()
        if remaining_s <= 0.0:
            raise asyncio.TimeoutError
        await asyncio.sleep(min(0.005, remaining_s))
    return future.result()


def lookup_known_token_pricing(base_url: str, model: str) -> Optional[PricingTuple]:
    """Return known pricing for shipped API models, or ``None`` when unknown."""
    name = str(model or "").strip().lower()
    provider = provider_for_base_url(base_url)
    if provider == "openai":
        for prefix, pricing in _OPENAI_MODEL_PRICING:
            for alias in _direct_provider_model_aliases(name):
                if _model_matches_known_prefix(alias, prefix):
                    return pricing
        return None
    if provider == "deepseek":
        for prefix, pricing in _DEEPSEEK_MODEL_PRICING:
            for alias in _direct_provider_model_aliases(name):
                if _model_matches_known_prefix(alias, prefix):
                    return pricing
        return None
    if provider == "openrouter":
        with _OPENROUTER_PRICING_LOCK:
            cached = _OPENROUTER_PRICING_CACHE.get(name)
            catalog_fresh = bool(
                _OPENROUTER_PRICING_FETCHED_AT > 0.0
                and time.time() - _OPENROUTER_PRICING_FETCHED_AT
                < _OPENROUTER_PRICING_CACHE_TTL_S
            )
            if cached is not None:
                if catalog_fresh:
                    return cached
                conservative = _OPENROUTER_VERIFIED_FALLBACK_PRICING.get(name)
                if conservative is not None:
                    return tuple(
                        max(stale_rate, fallback_rate)
                        for stale_rate, fallback_rate in zip(
                            cached,
                            conservative,
                            strict=True,
                        )
                    )
                return cached
            if catalog_fresh:
                return None
            return _OPENROUTER_VERIFIED_FALLBACK_PRICING.get(name)
    return None


def lookup_openrouter_reasoning_capabilities(
    base_url: str,
    model: str,
) -> Optional[OpenRouterReasoningCapabilities]:
    """Return the cached catalog capability record for one OpenRouter model."""

    if provider_for_base_url(base_url) != "openrouter":
        return None
    name = str(model or "").strip().lower()
    with _OPENROUTER_PRICING_LOCK:
        fresh = (
            _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT > 0.0
            and time.time() - _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT
            < _OPENROUTER_PRICING_CACHE_TTL_S
        )
        if not fresh:
            return None
        return _OPENROUTER_REASONING_CAPABILITY_CACHE.get(name)


async def ensure_openrouter_reasoning_capabilities_async(
    base_url: str,
    model: str,
    *,
    deadline: Optional[float] = None,
) -> Optional[OpenRouterReasoningCapabilities]:
    """Refresh capability discovery when needed, then return a fresh record."""

    if provider_for_base_url(base_url) != "openrouter":
        return None
    cached = lookup_openrouter_reasoning_capabilities(base_url, model)
    if cached is not None:
        return cached
    with _OPENROUTER_PRICING_LOCK:
        cache_fresh = (
            _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT > 0.0
            and time.time() - _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT
            < _OPENROUTER_PRICING_CACHE_TTL_S
        )
    if cache_fresh:
        # The model was absent from a successfully refreshed catalog.
        return None
    remaining_s: Optional[float] = None
    if deadline is not None and float(deadline) > 0.0:
        remaining_s = float(deadline) - time.time()
        if remaining_s <= 0.0:
            raise asyncio.TimeoutError(
                "OpenRouter capability preflight deadline expired"
            )
    try:
        # The shared owner retains the provider's ordinary watchdog. Each
        # caller independently enforces its absolute deadline without
        # cancelling or shortening the refresh needed by longer-lived peers.
        await _await_openrouter_refresh_future(
            _openrouter_async_refresh_future(timeout_s=10.0),
            timeout_s=remaining_s,
        )
    except asyncio.TimeoutError:
        raise
    except Exception:
        # A failed refresh is not evidence that the model lacks a reasoning
        # capability.  Preserve that distinction so Mini can yield before
        # transport instead of silently applying a low visible-output cap.
        raise
    with _OPENROUTER_PRICING_LOCK:
        capability_snapshot_fresh = (
            _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT > 0.0
            and time.time() - _OPENROUTER_REASONING_CAPABILITY_FETCHED_AT
            < _OPENROUTER_PRICING_CACHE_TTL_S
        )
        refresh_error = _OPENROUTER_REFRESH_ERROR
    if not capability_snapshot_fresh:
        if refresh_error is not None:
            raise refresh_error
        raise RuntimeError(
            "OpenRouter reasoning capability refresh completed without a "
            "fresh capability snapshot"
        )
    return lookup_openrouter_reasoning_capabilities(base_url, model)


def effective_token_pricing(
    base_url: str,
    model: str,
    *,
    input_tokens: int,
) -> Optional[PricingTuple]:
    """Return request-size-aware pricing for one concrete model request.

    GPT-5.6 requests above 272K input tokens use the provider's long-context
    rates for the full request.  Keeping this adjustment next to model lookup
    prevents budget reservations and final usage settlement from silently
    using different price policies.
    """
    pricing = lookup_known_token_pricing(base_url, model)
    if pricing is None:
        return None
    has_long_context_tier = _direct_openai_model_matches_any(
        base_url,
        model,
        _OPENAI_LONG_CONTEXT_MODEL_PREFIXES,
    )
    if (
        not has_long_context_tier
        or max(0, int(input_tokens or 0))
        <= _OPENAI_GPT56_LONG_CONTEXT_THRESHOLD
    ):
        return pricing
    input_per_m, cached_per_m, output_per_m = pricing
    return (
        input_per_m * _OPENAI_GPT56_LONG_CONTEXT_INPUT_MULTIPLIER,
        cached_per_m * _OPENAI_GPT56_LONG_CONTEXT_INPUT_MULTIPLIER,
        output_per_m * _OPENAI_GPT56_LONG_CONTEXT_OUTPUT_MULTIPLIER,
    )


def conservative_reservation_token_pricing(
    base_url: str,
    model: str,
    *,
    input_tokens: int,
) -> Optional[PricingTuple]:
    """Price a pre-dispatch reserve at the maximum plausible input rate."""
    pricing = effective_token_pricing(
        base_url,
        model,
        input_tokens=input_tokens,
    )
    if pricing is None:
        return None
    if _direct_openai_model_matches_any(
        base_url,
        model,
        ("gpt-5.6", "gpt-5.6-sol", "gpt-5.6-terra", "gpt-5.6-luna"),
    ):
        input_per_m, cached_per_m, output_per_m = pricing
        return (input_per_m * 1.25, cached_per_m, output_per_m)
    return pricing


def compute_model_cost_usd(
    base_url: str,
    model: str,
    *,
    input_tokens: int,
    output_tokens: int,
    cached_input_tokens: int,
    cache_write_tokens: int = 0,
) -> Optional[float]:
    """Compute model-aware cost, including GPT-5.6 cache-write billing."""
    pricing = effective_token_pricing(
        base_url,
        model,
        input_tokens=input_tokens,
    )
    if pricing is None:
        return None
    input_i, output_i, cached_i = _normalize_usage_counts(
        input_tokens,
        output_tokens,
        cached_input_tokens,
    )
    write_i = min(
        max(0, int(cache_write_tokens or 0)),
        max(0, input_i - cached_i),
    )
    input_per_m, cached_per_m, output_per_m = pricing
    write_multiplier = (
        1.25
        if _direct_openai_model_matches_any(
            base_url,
            model,
            ("gpt-5.6", "gpt-5.6-sol", "gpt-5.6-terra", "gpt-5.6-luna"),
        )
        else 1.0
    )
    ordinary_input = max(0, input_i - cached_i - write_i)
    return (
        ordinary_input * input_per_m / 1_000_000
        + cached_i * cached_per_m / 1_000_000
        + write_i * input_per_m * write_multiplier / 1_000_000
        + output_i * output_per_m / 1_000_000
    )


async def lookup_known_token_pricing_async(
    base_url: str,
    model: str,
) -> Optional[PricingTuple]:
    """Async pricing lookup that may refresh OpenRouter's public catalog."""

    if provider_for_base_url(base_url) != "openrouter":
        return lookup_known_token_pricing(base_url, model)
    now = time.time()
    with _OPENROUTER_PRICING_LOCK:
        cache_fresh = (
            bool(_OPENROUTER_PRICING_CACHE)
            and now - _OPENROUTER_PRICING_FETCHED_AT < _OPENROUTER_PRICING_CACHE_TTL_S
        )
    if cache_fresh:
        pricing = lookup_known_token_pricing(base_url, model)
        if pricing is not None:
            return pricing
    try:
        await _await_openrouter_refresh_future(
            _openrouter_async_refresh_future(timeout_s=10.0),
        )
    except Exception:
        pricing = lookup_known_token_pricing(base_url, model)
        return pricing
    return lookup_known_token_pricing(base_url, model)


async def effective_token_pricing_async(
    base_url: str,
    model: str,
    *,
    input_tokens: int,
) -> Optional[PricingTuple]:
    """Async catalog lookup followed by request-size price adjustment."""
    pricing = await lookup_known_token_pricing_async(base_url, model)
    if pricing is None:
        return None
    # OpenRouter returns its own concrete catalog price and does not inherit
    # direct OpenAI long-context rules through the provider hostname.
    if provider_for_base_url(base_url) != "openai":
        return pricing
    return effective_token_pricing(
        base_url,
        model,
        input_tokens=input_tokens,
    )


async def conservative_reservation_token_pricing_async(
    base_url: str,
    model: str,
    *,
    input_tokens: int,
) -> Optional[PricingTuple]:
    """Async catalog lookup plus conservative cache-write reservation rate."""
    pricing = await lookup_known_token_pricing_async(base_url, model)
    if pricing is None:
        return None
    if provider_for_base_url(base_url) != "openai":
        return pricing
    return conservative_reservation_token_pricing(
        base_url,
        model,
        input_tokens=input_tokens,
    )


def compute_cost_usd(
    input_tokens: int,
    output_tokens: int,
    cached_input_tokens: int,
    pricing: PricingTuple,
    *,
    round_digits: int | None = None,
) -> float:
    """Compute USD cost from usage counters and a pricing tuple.

    When ``round_digits`` is ``None`` the exact floating-point cost is returned.
    """
    input_per_m, cached_per_m, output_per_m = pricing
    input_i, output_i, cached_i = _normalize_usage_counts(
        input_tokens,
        output_tokens,
        cached_input_tokens,
    )
    cost = (
        (input_i - cached_i) * float(input_per_m) / 1_000_000
        + cached_i * float(cached_per_m) / 1_000_000
        + output_i * float(output_per_m) / 1_000_000
    )
    if round_digits is None:
        return cost
    return round(cost, int(round_digits))
