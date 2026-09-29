"""Internal raw response ownership across awaited provider-call boundaries."""

from __future__ import annotations

import copy
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any, Iterator, Mapping


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
