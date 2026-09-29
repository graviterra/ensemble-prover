"""Pure cost projections that retain subtotal and valuation authority."""
from __future__ import annotations

import math
from collections.abc import Mapping, Sequence
from typing import Any


COST_REPORT_KEYS = frozenset({
    "cost_usd", "cost_available", "cost_accounting_incomplete",
    "llm_cost_accounting_incomplete", "llm_observed_usage_cost_usd",
    "llm_unpriced_provider_exposure_count", "estimated_unknown_cost_usd",
    "llm_conservative_unknown_exposure_usd", "cost_source",
    "cost_valuation_source", "cost_valuation_assumptions", "pricing_policy",
    "llm_budget_accounted_cost_is_conservative_upper_bound",
})


def _amount(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    try:
        amount = float(value)
    except (TypeError, ValueError, OverflowError):
        return None
    return amount if math.isfinite(amount) and amount >= 0 else None


def is_cumulative_cost_snapshot(record: Mapping[str, Any]) -> bool:
    """Recognize a ledger bundle, including invalid totals that supersede older ones."""
    return "llm_observed_usage_cost_usd" in record and any(
        key in record for key in ("cost_accounting_incomplete", "llm_cost_accounting_incomplete")
    )


def cost_report(record: Mapping[str, Any], *, source: str = "record") -> dict[str, Any]:
    """Normalize a result/summary; absent cost remains an unavailable subtotal."""
    nested = record.get("metrics")
    values = {**(nested if isinstance(nested, Mapping) else {}), **record}
    amount = None
    for candidate in (record, nested if isinstance(nested, Mapping) else {}):
        if "llm_observed_usage_cost_usd" in candidate:
            # In ledger events cost_usd is only a per-call delta. An invalid
            # total cannot be replaced by that delta or an older nested total.
            amount = _amount(candidate["llm_observed_usage_cost_usd"])
            break
        amount = _amount(candidate.get("cost_usd"))
        if amount is not None:
            break
    available = amount is not None and values.get("cost_available") is not False
    exposure = _amount(values.get("llm_conservative_unknown_exposure_usd"))
    if exposure is None:
        exposure = _amount(values.get("estimated_unknown_cost_usd")) or 0.0
    elif "llm_observed_usage_cost_usd" not in values:
        # Outside a cumulative ledger bundle neither legacy exposure field
        # establishes that the other is only a per-event delta.
        exposure = max(exposure, _amount(values.get("estimated_unknown_cost_usd")) or 0.0)
    unpriced_value = _amount(values.get("llm_unpriced_provider_exposure_count"))
    unpriced = int(unpriced_value or 0)
    invalid_exposure = any(
        key in values and _amount(values[key]) is None
        for key in ("llm_conservative_unknown_exposure_usd", "estimated_unknown_cost_usd",
                    "llm_unpriced_provider_exposure_count")
    ) or (unpriced_value is not None and unpriced_value != unpriced)
    incomplete = bool(
        not available or exposure > 0 or unpriced or invalid_exposure
        or values.get("cost_accounting_incomplete", False)
        or values.get("llm_cost_accounting_incomplete", False)
        or (not any(key in values for key in ("cost_accounting_incomplete", "llm_cost_accounting_incomplete"))
            and values.get("pricing_known") is False)
    )
    assumptions = values.get("cost_valuation_assumptions")
    policy = values.get("pricing_policy")
    return {
        "cost_usd": amount if available else 0.0,
        "cost_available": available,
        "cost_accounting_incomplete": incomplete,
        "llm_unpriced_provider_exposure_count": unpriced,
        "estimated_unknown_cost_usd": exposure,
        "cost_source": str(values.get("cost_source") or source) if available else "unavailable",
        "cost_valuation_source": str(values.get("cost_valuation_source") or "unspecified"),
        "cost_valuation_assumptions": list(assumptions) if isinstance(assumptions, (list, tuple)) else [],
        "pricing_policy": dict(policy) if isinstance(policy, Mapping) else {},
    }


def select_cost_snapshot(
    summary: Mapping[str, Any], events: Sequence[Mapping[str, Any]],
    terminal_events: Sequence[Mapping[str, Any]], *, summary_current: bool = True,
) -> dict[str, Any]:
    """Select one coherent bundle; never add per-call deltas or maxima."""
    nested = summary.get("metrics")
    summary_has_cost = any(
        key in candidate for candidate in (
            summary, nested if isinstance(nested, Mapping) else {},
        ) for key in ("cost_usd", "llm_observed_usage_cost_usd")
    )
    if summary_current and summary_has_cost:
        return {**summary, **cost_report(summary, source="summary")}
    for record in reversed(events):
        if is_cumulative_cost_snapshot(record):
            return {**record, **cost_report(record, source="ledger_snapshot")}
    for record in reversed(terminal_events):
        if any(key in record for key in ("cost_usd", "max_cost_usd", "llm_budget_accounted_cost_usd")):
            return {**record, **cost_report(record, source="legacy_terminal")}
    return {**summary, **cost_report(summary if summary_current else {}, source="summary")}


def format_cost(record: Mapping[str, Any], *, digits: int = 4) -> str:
    """Render observed subtotal separately from completeness and valuation source."""
    report = cost_report(record)
    if not report["cost_available"]:
        return "unknown"
    value = f"${report['cost_usd']:.{digits}f}"
    if report["cost_accounting_incomplete"]:
        value += " known subtotal (partial; total unknown)"
    valuation = report["cost_valuation_source"]
    if valuation != "unspecified":
        value += f" [{valuation}]"
    if report["cost_valuation_assumptions"]:
        value += " (assumptions: " + "; ".join(
            str(assumption).replace("_", " ")
            for assumption in report["cost_valuation_assumptions"]
        ) + ")"
    return value
