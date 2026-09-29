"""Frontier research control: routes, approaches, and investigation evidence.

Policy modules propose and validate decisions. Dispatch, debit, and theorem
acceptance stay with the existing discovery and strategy owners.
"""

from .config import normalize_config
from .owner import FrontierOwner

__all__ = ["FrontierOwner", "normalize_config"]
