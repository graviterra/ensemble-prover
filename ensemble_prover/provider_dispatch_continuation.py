"""Request-local provider fallback continuation shared across package modules."""

from __future__ import annotations

import contextvars
from contextlib import contextmanager
from typing import Any, Iterator


# These variables form one request-local transport authority boundary.  Both
# package modules import the same instances so a Mini meter can authorize and
# observe concrete provider transports.
PROVIDER_DISPATCH_MARKER: contextvars.ContextVar[Any] = contextvars.ContextVar(
    "provider_dispatch_marker",
    default=None,
)
PROVIDER_DISPATCH_TARGET: contextvars.ContextVar[str] = contextvars.ContextVar(
    "provider_dispatch_target",
    default="",
)
PROVIDER_PENDING_DISPATCH_RECEIPT: contextvars.ContextVar[dict[str, Any]] = (
    contextvars.ContextVar("provider_pending_dispatch_receipt", default={})
)
PROVIDER_DISPATCH_OBSERVER: contextvars.ContextVar[Any] = contextvars.ContextVar(
    "provider_dispatch_observer",
    default=None,
)
PROVIDER_DISPATCH_EXPOSURE_TRACKER: contextvars.ContextVar[Any] = (
    contextvars.ContextVar("provider_dispatch_exposure_tracker", default=None)
)


_PROVIDER_DISPATCH_RESUME_TARGET: contextvars.ContextVar[str] = (
    contextvars.ContextVar("provider_dispatch_resume_target", default="")
)


@contextmanager
def provider_dispatch_resume_target(target_id: str) -> Iterator[None]:
    """Expose the concrete fallback leaf refused by the prior quantum."""

    token = _PROVIDER_DISPATCH_RESUME_TARGET.set(str(target_id or "").strip())
    try:
        yield
    finally:
        _PROVIDER_DISPATCH_RESUME_TARGET.reset(token)


def current_provider_dispatch_resume_target_id() -> str:
    return str(_PROVIDER_DISPATCH_RESUME_TARGET.get() or "").strip()
