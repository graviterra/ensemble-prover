"""Semantic identity projection for MiniRecursive configuration."""

from __future__ import annotations

from typing import Any, Mapping


# These knobs change only falsification batch pacing.  Witness generation is
# deterministic in semantic policy + absolute cursor index, so tuning them
# must not invalidate either a Mini checkpoint or a recursive mid-pass frame.
MINI_RECURSIVE_OPERATIONAL_CONFIG_FIELDS = frozenset(
    {
        "falsification_max_checks",
        "falsification_operation_timeout_s",
        "falsification_engine_timeout_s",
    }
)


def mini_recursive_semantic_config_record(config: Any) -> dict[str, Any]:
    """Return the config leaves that define recursive mathematical identity."""

    if isinstance(config, Mapping):
        raw = dict(config)
    else:
        raw = dict(vars(config))
    return {
        str(key): value
        for key, value in raw.items()
        if str(key) not in MINI_RECURSIVE_OPERATIONAL_CONFIG_FIELDS
    }


def mini_recursive_operational_action_spec_paths(
    *,
    prefix: str = "attrs.config",
) -> frozenset[str]:
    """Return exact action-spec leaves excluded from checkpoint identity."""

    normalized = str(prefix or "").strip(".")
    return frozenset(
        (
            f"{normalized}.{field_name}"
            if normalized
            else field_name
        )
        for field_name in MINI_RECURSIVE_OPERATIONAL_CONFIG_FIELDS
    )
