"""Small, kernel-gated source repairs owned by the Mini prover."""

from __future__ import annotations

import re
from typing import Any, List, Optional

from .utils import (
    LEAN_CONTROL_TACTIC_HEADS,
    LEAN_TACTIC_START_KEYWORDS,
    _lean_lexical_skip_end,
    _scan_group,
)


_TACTIC_STARTS = frozenset(LEAN_TACTIC_START_KEYWORDS)
_REPAIRABLE_REJECTION_RE = re.compile(
    r"(?:unexpected\s+(?:identifier|token)|unknown\s+(?:identifier|constant)|"
    r"application\s+type\s+mismatch|function\s+expected|invalid\s+.*tactic|"
    r"unsolved\s+goals?)",
    flags=re.IGNORECASE,
)


def _split_single_line_tactic_segments(body: str) -> List[str]:
    source = str(body or "")
    atoms: list[tuple[str, str]] = []
    index = 0
    while index < len(source):
        if source[index].isspace():
            index += 1
            continue
        start = index
        while index < len(source) and not source[index].isspace():
            skip_end = _lean_lexical_skip_end(source, index)
            if skip_end is not None and skip_end > index:
                index = skip_end
                continue
            if source[index] in "([{⦃":
                group_end = _scan_group(source, index)
                if group_end is not None:
                    index = group_end
                    continue
            if source[index] == "`":
                quote_end = source.find("`", index + 1)
                index = len(source) if quote_end < 0 else quote_end + 1
                continue
            index += 1
        atom = source[start:index]
        code_head = (
            atom
            if atom in _TACTIC_STARTS
            or atom in LEAN_CONTROL_TACTIC_HEADS
            or atom == "first"
            else ""
        )
        atoms.append((atom, code_head))
    if not atoms:
        return []

    def consume(index: int) -> tuple[str, int]:
        head, code_head = atoms[index]
        if code_head == "first":
            return (
                " ".join(atom for atom, _code in atoms[index:]).strip(),
                len(atoms),
            )
        if code_head in LEAN_CONTROL_TACTIC_HEADS:
            if index + 1 >= len(atoms):
                return head, index + 1
            payload, next_index = consume(index + 1)
            return f"{head} {payload}".strip(), next_index
        next_index = index + 1
        while (
            next_index < len(atoms)
            and atoms[next_index][1] not in _TACTIC_STARTS
        ):
            next_index += 1
        return (
            " ".join(atom for atom, _code in atoms[index:next_index]).strip(),
            next_index,
        )

    segments: List[str] = []
    index = 0
    while index < len(atoms):
        segment, next_index = consume(index)
        if next_index <= index:
            break
        if segment:
            segments.append(segment)
        index = next_index
    return segments


def repair_single_line_by_tactic_block(proof: str) -> Optional[str]:
    """Split a flattened ``by`` block without touching ``by_*`` tactics."""

    stripped = str(proof or "").strip()
    if "\n" in stripped or re.match(r"^by(?:\s+|$)", stripped) is None:
        return None
    body = stripped[2:].strip()
    if not body:
        return None
    segments = _split_single_line_tactic_segments(body)
    if len(segments) < 2:
        return None
    repaired = "by\n  " + "\n  ".join(segments)
    return repaired if repaired != stripped else None


def rejection_supports_single_line_layout_repair(result: Any) -> bool:
    """Whether a rejected Lean result is compatible with flattened layout."""

    if bool(getattr(result, "ok", False)):
        return False
    text_parts = [str(getattr(result, "output", "") or "")]
    parsed = getattr(result, "parsed", None)
    if parsed is not None:
        text_parts.extend(
            str(getattr(item, "message", "") or getattr(item, "summary", "") or "")
            for item in list(getattr(parsed, "diagnostics", ()) or ())
        )
    return _REPAIRABLE_REJECTION_RE.search("\n".join(text_parts)) is not None
