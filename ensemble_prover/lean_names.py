"""Lean name spelling and component identity for declaration replay."""

from __future__ import annotations

import re

from .math_utils import _LEAN_ID_FIRST_CHARS, _LEAN_ID_REST_CHARS

# Keep Unicode word characters accepted by existing declaration readers, and
# include Lean's letter-like symbols and identifier suffixes explicitly.
LEAN_PLAIN_NAME_PATTERN = (
    rf"(?:[^\W\d]|[{_LEAN_ID_FIRST_CHARS}])[\w{_LEAN_ID_REST_CHARS}]*"
)
LEAN_NAME_COMPONENT_PATTERN = rf"(?:«[^»\r\n]+»|{LEAN_PLAIN_NAME_PATTERN})"
LEAN_QUALIFIED_NAME_PATTERN = (
    rf"{LEAN_NAME_COMPONENT_PATTERN}(?:\.{LEAN_NAME_COMPONENT_PATTERN})*"
)
_COMPONENT_RE = re.compile(LEAN_NAME_COMPONENT_PATTERN)
_QUALIFIED_RE = re.compile(LEAN_QUALIFIED_NAME_PATTERN)


def lean_name_components(name: str) -> tuple[str, ...]:
    """Compare quoted aliases without treating quoted dots as separators."""
    if _QUALIFIED_RE.fullmatch(name) is None:
        return ()
    return tuple(
        part[1:-1] if part.startswith("«") else part
        for part in _COMPONENT_RE.findall(name)
    )


def lean_name_key(name: str) -> str:
    """Return a common spelling for semantically equivalent Lean names."""
    components = lean_constant_name_components(name)
    return ".".join(f"«{part}»" for part in components) if components else name


def lean_constant_name_components(name: str) -> tuple[str, ...]:
    """A root qualifier controls resolution; it is not a constant component."""
    components = lean_name_components(name)
    if len(components) > 1 and components[0] == "_root_":
        return components[1:]
    return components
