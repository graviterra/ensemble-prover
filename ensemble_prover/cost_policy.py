"""Validate monetary policy before it can authorize provider work."""
from __future__ import annotations

import math
from decimal import Decimal
from typing import Any


def require_cost_budget_usd(value: Any) -> float:
    """Accept a finite nonnegative cap; exactly zero disables budget stops."""

    message = "cost budget must be a finite nonnegative representable dollar amount (0 disables stops)"
    if isinstance(value, bool):
        raise ValueError(message)
    try:
        amount = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(message) from exc
    if not math.isfinite(amount) or amount < 0:
        raise ValueError(message)
    # A positive decimal below float range must not become the disabled cap.
    exact_zero = Decimal(value) == 0 if isinstance(value, str) else value == 0
    if amount == 0 and not exact_zero:
        raise ValueError(message)
    return amount
