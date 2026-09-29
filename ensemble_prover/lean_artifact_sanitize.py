"""Sanitizers for persisted Lean artifact text.

Lean comments are useful while generating and repairing proofs, but final
artifacts should contain only executable proof/helper source.  The scanner is
shared with the Lean extractor so comment markers inside strings stay intact.
"""

from __future__ import annotations

from typing import Iterable, Tuple

def sanitize_lean_artifact_text(source: str) -> str:
    """Strip Lean comments from persisted artifact text while preserving strings."""

    from .mini_lean_extract import _strip_lean_comments

    return _strip_lean_comments(str(source or "")).strip()


def sanitize_lean_artifact_texts(sources: Iterable[str]) -> Tuple[str, ...]:
    """Strip Lean comments from non-empty artifact blocks."""

    return tuple(
        sanitized
        for source in list(sources or ())
        for sanitized in [sanitize_lean_artifact_text(str(source or ""))]
        if sanitized
    )
