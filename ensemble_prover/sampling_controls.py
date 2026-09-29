"""Shared sampling-control sentinels for LLM client boundaries."""

from __future__ import annotations

from typing import Any


class _ApiDefaultTemperature:
    """Sentinel requesting provider-side default sampling controls."""

    def __repr__(self) -> str:
        return "API_DEFAULT_TEMPERATURE"


API_DEFAULT_TEMPERATURE = _ApiDefaultTemperature()


def is_api_default_temperature_override(value: Any) -> bool:
    return value is API_DEFAULT_TEMPERATURE
