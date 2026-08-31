"""Small in-memory value copying helpers.

This module deliberately has no disk format, compatibility gate, capability
inventory, environment identity, or restore authority. It exists only for
places that need an isolated ordinary Python value while a run is live.
"""

from __future__ import annotations

import copy
from typing import Any


class StateSnapshotError(RuntimeError):
    """An in-memory state value could not be copied or validated."""


class StateSnapshotCompatibilityError(StateSnapshotError):
    """An in-memory state value has an unsupported shape."""


def clone_state_value(value: Any) -> Any:
    """Return an ordinary in-memory copy without imposing persistence rules."""

    try:
        return copy.deepcopy(value)
    except Exception as exc:
        raise StateSnapshotError(str(exc)) from exc


def encode_state_value(value: Any) -> Any:
    return clone_state_value(value)


def decode_state_value(value: Any) -> Any:
    return clone_state_value(value)
