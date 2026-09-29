"""Settings for frontier research control.

Selecting a mode does not raise the run authorization, enable experiments,
change providers, or turn formal-state search on globally.
"""

from __future__ import annotations

import math
from typing import Any

MODES = frozenset({"off", "observe", "adaptive"})
SUPPORTED_PROGRESS_POLICY = 1
SUPPORTED_TOOL_POLICY = 1

DEFAULTS: dict[str, Any] = {
    "mode": "off",
    "max_resident_approaches": 3,
    "max_consecutive_quanta": 2,
    "max_control_quanta_between_work": 1,
    "max_operation_execution_admissions": 3,
    "max_operation_admission_recoveries": 3,
    "max_consecutive_lane_failures": 3,
    "progress_policy_version": SUPPORTED_PROGRESS_POLICY,
    "tool_policy_version": SUPPORTED_TOOL_POLICY,
    "experiment_profile": "stdlib",
    "permit_lease_seconds": 60.0,
    "max_no_progress": 2,
}


def _positive_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or type(value) is not int or value < 1:
        raise ValueError(f"{name} must be a positive integer")
    return value


def normalize_config(
    value: dict[str, Any] | None,
    *,
    permit_lease_seconds: float | None = None,
    max_no_progress: int | None = None,
) -> dict[str, Any]:
    """Return a complete settings dict. Unknown keys are rejected."""
    if value is None:
        value = {}
    if not isinstance(value, dict):
        raise ValueError("frontier_research must be an object")
    unknown = set(value) - set(DEFAULTS)
    if unknown:
        raise ValueError("unknown frontier_research settings: " + ", ".join(sorted(unknown)))
    config = dict(DEFAULTS)
    config.update(value)
    if not isinstance(config["mode"], str) or config["mode"] not in MODES:
        raise ValueError("frontier_research.mode must be off, observe, or adaptive")
    for name in (
        "max_resident_approaches",
        "max_consecutive_quanta",
        "max_control_quanta_between_work",
        "max_operation_execution_admissions",
        "max_operation_admission_recoveries",
        "max_consecutive_lane_failures",
        "max_no_progress",
    ):
        config[name] = _positive_int(config[name], name)
    if type(config["progress_policy_version"]) is not int or config["progress_policy_version"] != SUPPORTED_PROGRESS_POLICY:
        raise ValueError("unsupported frontier progress policy version")
    if type(config["tool_policy_version"]) is not int or config["tool_policy_version"] != SUPPORTED_TOOL_POLICY:
        raise ValueError("unsupported frontier tool policy version")
    if not isinstance(config["experiment_profile"], str) or not config["experiment_profile"].strip():
        raise ValueError("experiment_profile must be a non-empty string")
    lease = config["permit_lease_seconds"] if permit_lease_seconds is None else (
        value["permit_lease_seconds"] if "permit_lease_seconds" in value else permit_lease_seconds
    )
    if (
        isinstance(lease, bool)
        or not isinstance(lease, (int, float))
        or not math.isfinite(lease)
        or lease <= 0
    ):
        raise ValueError("permit_lease_seconds must be finite and positive")
    config["permit_lease_seconds"] = float(lease)
    if max_no_progress is not None and "max_no_progress" not in value:
        config["max_no_progress"] = _positive_int(max_no_progress, "max_no_progress")
    return config
