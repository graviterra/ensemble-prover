"""Internal raw response ownership across awaited provider-call boundaries."""

from __future__ import annotations

import copy
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any, Iterator, Mapping


_MAX_REJECTED_RESPONSE_BYTES = 16 * 1024 * 1024


@dataclass
class RejectedProviderResponseReceipt:
    """Untrusted completed content for its caller's format-validation loop."""

    content: str | None = field(default=None, repr=False)
    error: BaseException | None = field(default=None, repr=False)
    diagnostic: dict[str, Any] = field(default_factory=dict)
    _active: bool = field(default=True, repr=False)


_REJECTED_RESPONSE_CAPTURE: ContextVar[RejectedProviderResponseReceipt | None] = ContextVar(
    "rejected_provider_response_capture", default=None,
)


def publish_rejected_provider_response(
    error: BaseException, content: str, diagnostic: Mapping[str, Any],
) -> None:
    """Retain complete invalid content privately, without publishing an answer.

    The bound matches subscription stream storage. Oversized content is omitted
    as a whole; a clipped mathematical response cannot authorize correction.
    """
    receipt = _REJECTED_RESPONSE_CAPTURE.get()
    if receipt is None or not receipt._active:
        return
    retained = len(content.encode("utf-8", errors="surrogatepass")) <= _MAX_REJECTED_RESPONSE_BYTES
    receipt.content = content if retained else None
    receipt.error = error
    receipt.diagnostic = {**dict(diagnostic), "content_retained": retained}


@contextmanager
def capture_rejected_provider_response() -> Iterator[RejectedProviderResponseReceipt]:
    """Capture one call's rejection, excluding shared state and late results."""
    receipt = RejectedProviderResponseReceipt()
    token = _REJECTED_RESPONSE_CAPTURE.set(receipt)
    try:
        yield receipt
    finally:
        receipt._active = False
        _REJECTED_RESPONSE_CAPTURE.reset(token)


@dataclass
class ProviderResponseReceipt:
    """One call's detached response; deliberately separate from logged metadata."""

    response: dict[str, Any] | None = None
    _active: bool = field(default=True, repr=False)

    def resolve(self, client: Any) -> dict[str, Any] | None:
        """Prefer the captured response, retaining opaque-client compatibility."""

        if self.response is not None:
            return self.response
        legacy = getattr(client, "last_raw_response_data", None)
        return copy.deepcopy(legacy) if isinstance(legacy, dict) else None


_RESPONSE_CAPTURE: ContextVar[ProviderResponseReceipt | None] = ContextVar(
    "provider_response_capture", default=None
)


def publish_provider_response(response: Mapping[str, Any]) -> None:
    """Snapshot a normalized response into its nearest live call scope."""

    receipt = _RESPONSE_CAPTURE.get()
    if receipt is not None and receipt._active:
        receipt.response = copy.deepcopy(dict(response))


@contextmanager
def capture_provider_response() -> Iterator[ProviderResponseReceipt]:
    """Capture child-task responses without a shared client's mutable last slot."""

    receipt = ProviderResponseReceipt()
    token = _RESPONSE_CAPTURE.set(receipt)
    try:
        yield receipt
    finally:
        # Detached provider tasks inherit this receipt object. Closing it
        # prevents a late response from replacing a settled call's snapshot.
        receipt._active = False
        _RESPONSE_CAPTURE.reset(token)
