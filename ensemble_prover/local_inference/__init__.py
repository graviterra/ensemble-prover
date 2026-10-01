"""Local inference profiles, conserved compute budgets, and capacity permits.

Importing this package does not register a provider, open a socket, or consult
the dollar cost ledger. Callers wire the seams in ``seams`` at the existing
dispatch and continuation boundaries when those paths are ready.
"""

from __future__ import annotations

from .budget import LocalComputeLedger
from .capacity import CapacityCoordinator
from .config import load_profile_path, load_profile_text, resolve_run
from .errors import ContextCapacityInsufficient, LocalInferenceError

__all__ = [
    "CapacityCoordinator",
    "ContextCapacityInsufficient",
    "LocalComputeLedger",
    "LocalInferenceError",
    "load_profile_path",
    "load_profile_text",
    "resolve_run",
]
