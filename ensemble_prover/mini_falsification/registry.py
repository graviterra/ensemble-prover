"""Deterministic engine registry with explicit names."""

from __future__ import annotations

from typing import Iterable

from .engine import FalsificationEngine
from .engines import (
    BoundedNumericEngine,
    ExactAlgebraEngine,
    FiniteEnumerationEngine,
    FunctionWitnessEngine,
    GraphEnumerationEngine,
    PropertyGenerationEngine,
    SatSmtEngine,
    StructuralObstructionEngine,
)


def default_engines() -> tuple[FalsificationEngine, ...]:
    return (
        StructuralObstructionEngine(),
        FiniteEnumerationEngine(),
        PropertyGenerationEngine(),
        SatSmtEngine(),
        FunctionWitnessEngine(),
        ExactAlgebraEngine(),
        GraphEnumerationEngine(),
        BoundedNumericEngine(),
    )


def select_engines(names: Iterable[str]) -> tuple[FalsificationEngine, ...]:
    requested = tuple(str(name or "").strip() for name in names)
    available = {engine.name: engine for engine in default_engines()}
    unknown = sorted(set(requested) - set(available))
    if unknown:
        raise ValueError(f"unknown falsification engines: {', '.join(unknown)}")
    return tuple(available[name] for name in requested)
