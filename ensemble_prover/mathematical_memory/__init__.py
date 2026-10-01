"""Opt-in mathematical memory, preserving the existing proof authority."""

from .config import MemoryConfig, MemoryMode
from .catalog import AuthoritySnapshot, MemoryCatalog, MemoryUnavailable
from .experience import ExperienceIndex, ExperienceSummary, exact_attempt_key
from .model import (
    ApplicationOutcome,
    CatalogView,
    EligibilityPolicy,
    EvidenceReference,
    GenerationPin,
    MemoryEvent,
    MemoryProvenance,
    Provenance,
    StoreResult,
)

__all__ = [
    "MemoryConfig",
    "MemoryMode",
    "AuthoritySnapshot",
    "MemoryCatalog",
    "MemoryUnavailable",
    "ExperienceIndex",
    "ExperienceSummary",
    "exact_attempt_key",
    "ApplicationOutcome",
    "CatalogView",
    "EligibilityPolicy",
    "EvidenceReference",
    "GenerationPin",
    "MemoryEvent",
    "MemoryProvenance",
    "Provenance",
    "StoreResult",
]
