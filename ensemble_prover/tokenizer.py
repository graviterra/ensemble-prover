"""Shared BM25 tokenization and recursive JSON-value sanitization utilities.

The theorem-search retrieval modules use these leaf helpers without importing
provider, scheduler, or Lean runtime state.
"""

from __future__ import annotations

import math
import re
from typing import Any, List

try:
    import numpy as np

    _HAS_NUMPY = True
except ImportError:
    _HAS_NUMPY = False

# ── BM25 tokenizer ───────────────────────────────────────────────────

TOKEN_RE = re.compile(r"[^\W\d][\w'.]*|\d+|[∀∃→←↔=<>≤≥≠∈∉⊆⊂⊇⊃∣∧∨¬⊢ℤℕℝℚℂ∫∑∏]")

BM25_STOPWORDS: frozenset[str] = frozenset(
    # Single-character binder names (universal in Lean statements)
    set("abcdefghijklmnopqrstuvwxyz")
    | {
        # Lean keywords
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "let",
        "have",
        "show",
        "by",
        "sorry",
        "fun",
        "where",
        "import",
        "open",
        "section",
        "namespace",
        "end",
        "in",
        "do",
        "return",
        "if",
        "then",
        "else",
        "match",
        "with",
        # Type-universe words
        "prop",
        "type",
        "sort",
    }
)


def tokenize(text: str) -> List[str]:
    """Tokenize Lean text for BM25/relevance scoring.

    Splits identifiers on dots, underscores, and camelCase boundaries.
    Removes BM25 stop-words (single-char binders, Lean keywords).
    """
    if not text:
        return []
    tokens = TOKEN_RE.findall(text)
    out: List[str] = []
    for tok in tokens:
        if tok.isdigit():
            out.append(tok)
            continue
        for part in tok.replace(".", " ").replace("_", " ").split():
            # Split camelCase / PascalCase
            pieces = re.findall(
                r"[A-Z]+(?=[A-Z][a-z\u0370-\u03FF]|[0-9]|$)|[A-Z]?[a-z\u0370-\u03FF]+|[0-9]+",
                part,
            )
            if pieces:
                out.extend(p.lower() for p in pieces if p)
            else:
                out.append(part.lower())
    return [t for t in out if t not in BM25_STOPWORDS]


# ── JSON sanitization ────────────────────────────────────────────────


def sanitize_for_json(obj: Any) -> Any:
    """Recursively sanitize an object for JSON serialization.

    Replaces NaN, Infinity with 0.0.  Handles numpy arrays/scalars
    when numpy is available.
    """
    if _HAS_NUMPY:
        if isinstance(obj, np.ndarray):
            return [sanitize_for_json(float(v)) for v in obj.flat]
        if isinstance(obj, (np.floating, np.integer)):
            return sanitize_for_json(float(obj))
        if isinstance(obj, np.bool_):
            return bool(obj)
    if isinstance(obj, float):
        if math.isnan(obj) or math.isinf(obj):
            return 0.0
        return obj
    if isinstance(obj, dict):
        return {k: sanitize_for_json(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [sanitize_for_json(v) for v in obj]
    if isinstance(obj, (set, frozenset)):
        return [sanitize_for_json(v) for v in sorted(obj, key=str)]
    return obj
