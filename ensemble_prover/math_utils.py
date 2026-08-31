"""Shared numerics for the ensemble prover.

Canonical, numerically stable implementations of sigmoid, softmax,
cosine similarity, and related functions.  Every module in the package
should import from here rather than rolling its own copy.
"""

from __future__ import annotations

import math
import random
import re
import threading
from collections import defaultdict
from typing import Dict, List, Sequence, Tuple

# ------------------------------------------------------------------
# Activation / probability helpers
# ------------------------------------------------------------------


def _materialize_sequence(values) -> list | None:
    try:
        return list(values)
    except Exception:
        return None


def clamp_probability(value: float, *, default: float = 0.0) -> float:
    """Return a finite probability in ``[0, 1]`` with a safe fallback."""
    try:
        fallback = float(default)
    except Exception:
        fallback = 0.0
    if not math.isfinite(fallback):
        fallback = 0.0
    fallback = max(0.0, min(1.0, fallback))
    try:
        prob = float(value)
    except Exception:
        return fallback
    if not math.isfinite(prob):
        return fallback
    return max(0.0, min(1.0, prob))


def sigmoid(x: float) -> float:
    """Numerically stable sigmoid that never overflows.

    For x >= 0 we compute  1/(1+exp(-x))  (exp(-x) underflows to 0, safe).
    For x <  0 we compute  exp(x)/(1+exp(x))  (exp(x) underflows to 0, safe).
    """
    try:
        x_f = float(x)
    except Exception:
        return 0.5
    if not math.isfinite(x_f):
        return 0.5
    if x_f >= 0:
        z = math.exp(-x_f)
        return 1.0 / (1.0 + z)
    z = math.exp(x_f)
    return z / (1.0 + z)


def softmax(xs: Sequence[float]) -> List[float]:
    """Numerically stable softmax with max-subtraction.

    Returns uniform distribution when logits are invalid or all exponents underflow.
    """
    items = _materialize_sequence(xs)
    if not items:
        return []
    try:
        values = [float(x) for x in items]
    except Exception:
        return [1.0 / len(items)] * len(items)
    if any(not math.isfinite(x) for x in values):
        return [1.0 / len(values)] * len(values)
    m = max(values)
    exps = [math.exp(x - m) for x in values]
    s = sum(exps)
    if s <= 1e-12 or not math.isfinite(s):
        return [1.0 / len(exps)] * len(exps)
    return [e / s for e in exps]


def dot(a: Sequence[float], b: Sequence[float]) -> float:
    """Dot product of two vectors.

    Raises:
        ValueError: If vectors have different dimensions.
    """
    if len(a) != len(b):
        raise ValueError(
            f"dot product requires equal dimensions: got {len(a)} vs {len(b)}"
        )
    return sum(x * y for x, y in zip(a, b))


# ------------------------------------------------------------------
# Vector operations
# ------------------------------------------------------------------


def l2_normalize(vec: List[float]) -> List[float]:
    """L2-normalize a vector; zeroes out non-finite inputs."""
    items = _materialize_sequence(vec)
    if items is None:
        return []
    try:
        values = [float(v) for v in items]
    except Exception:
        return [0.0] * len(items)
    if any(not math.isfinite(v) for v in values):
        return [0.0] * len(values)
    n = math.sqrt(sum(v * v for v in values))
    if n <= 1e-9:
        return [0.0] * len(values)
    return [v / n for v in values]


def cosine_sim(a: Sequence[float], b: Sequence[float]) -> float:
    """Cosine similarity.  Returns 0.0 for empty or zero-norm inputs.

    Raises:
        ValueError: If vectors have different dimensions.
    """
    a_values = _materialize_sequence(a)
    b_values = _materialize_sequence(b)
    if not a_values or not b_values:
        return 0.0
    if len(a_values) != len(b_values):
        raise ValueError(
            f"cosine_sim requires equal dimensions: got {len(a_values)} vs {len(b_values)}"
        )
    try:
        a_nums = [float(x) for x in a_values]
        b_nums = [float(y) for y in b_values]
    except Exception:
        return 0.0
    num = 0.0
    da_sq = 0.0
    db_sq = 0.0
    for x, y in zip(a_nums, b_nums):
        if not (math.isfinite(x) and math.isfinite(y)):
            return 0.0
        num += x * y
        da_sq += x * x
        db_sq += y * y
    if not (math.isfinite(num) and math.isfinite(da_sq) and math.isfinite(db_sq)):
        return 0.0
    da = math.sqrt(da_sq)
    db = math.sqrt(db_sq)
    if da <= 1e-9 or db <= 1e-9:
        return 0.0
    den = da * db
    if den <= 1e-12 or not math.isfinite(den):
        return 0.0
    val = num / den
    if not math.isfinite(val):
        return 0.0
    return max(-1.0, min(1.0, val))


def distance(a: Sequence[float], b: Sequence[float]) -> float:
    """Cosine distance: 1 - cosine_sim."""
    return 1.0 - cosine_sim(a, b)


def mahalanobis_distance(
    a: Sequence[float], b: Sequence[float], inv_diag: Sequence[float]
) -> float:
    """Mahalanobis distance with diagonal precision matrix.

    d_M(a,b) = sqrt(sum((a_i - b_i)^2 * inv_diag_i))

    For unit precision (inv_diag all 1.0) this reduces to Euclidean distance.
    Uses diagonal approximation for O(D) instead of O(D^2) full covariance.
    """
    if len(a) != len(b) or len(a) != len(inv_diag):
        return float("inf")
    s = 0.0
    for x, y, w in zip(a, b, inv_diag):
        try:
            x_f = float(x)
            y_f = float(y)
            w_f = float(w)
        except Exception:
            return float("inf")
        if not (math.isfinite(x_f) and math.isfinite(y_f) and math.isfinite(w_f)):
            return float("inf")
        if w_f < 0.0:
            return float("inf")
        d = x_f - y_f
        term = d * d * w_f
        if not math.isfinite(term):
            return float("inf")
        s += term
    if not math.isfinite(s) or s < 0.0:
        return float("inf")
    return math.sqrt(s)


# ------------------------------------------------------------------
# Sampling
# ------------------------------------------------------------------


def sample_index(rng: random.Random, weights: Sequence[float]) -> int:
    """Sample an index from a probability distribution.

    Args:
        rng: Random number generator.
        weights: Non-negative weights (need not be pre-normalized).

    Returns:
        Sampled index.

    Raises:
        ValueError: If *weights* is empty.
    """
    items = _materialize_sequence(weights)
    if items is None:
        raise TypeError("sample_index requires an iterable of weights")
    if not items:
        raise ValueError("sample_index called with empty weights list")
    clean_weights: List[float] = []
    for weight in items:
        try:
            w_f = float(weight)
        except Exception:
            w_f = 0.0
        if not math.isfinite(w_f) or w_f < 0.0:
            w_f = 0.0
        clean_weights.append(w_f)
    max_weight = max(clean_weights) if clean_weights else 0.0
    if max_weight <= 1e-12:
        # Degenerate: fall back to uniform to avoid bias toward tail.
        return rng.randrange(len(items))
    scaled_weights = [w / max_weight for w in clean_weights]
    total = sum(scaled_weights)
    if total <= 1e-12:
        # Degenerate: fall back to uniform to avoid bias toward tail.
        return rng.randrange(len(items))
    r = rng.random() * total
    acc = 0.0
    for i, w in enumerate(scaled_weights):
        acc += w
        if r < acc:
            return i
    return len(items) - 1


# ------------------------------------------------------------------
# Lean syntax helpers
# ------------------------------------------------------------------


def balance_score(text: str) -> float:
    """Score bracket / begin-end balance of a Lean proof string.

    Returns 1.0 (balanced), 0.3 (partially balanced), or 0.0 (broken).
    """
    stripped, lexically_closed = _strip_lean_comments_and_strings(text)
    if not lexically_closed:
        return 0.0
    opens = {"(": ")", "[": "]", "{": "}"}
    closes = {")": "(", "]": "[", "}": "{"}
    stack: list[str] = []
    ok = True
    for ch in stripped:
        if ch in opens:
            stack.append(ch)
        elif ch in closes:
            if not stack or stack[-1] != closes[ch]:
                ok = False
                break
            stack.pop()
    paren_ok = ok and not stack
    begin_count = len(re.findall(r"\bbegin\b", stripped))
    end_count = len(re.findall(r"\bend\b", stripped))
    begin_ok = begin_count == end_count
    return 1.0 if (paren_ok and begin_ok) else 0.3 if (paren_ok or begin_ok) else 0.0


def _strip_lean_comments_and_strings(text: str) -> tuple[str, bool]:
    """Remove non-code literal content before balance heuristics."""
    out: List[str] = []
    _idx, ok = _scan_lean_code(text, 0, out)
    return "".join(out), ok


def _scan_lean_code(text: str, start: int, out: List[str]) -> tuple[int, bool]:
    i = start
    n = len(text)
    while i < n:
        interp_prefix = _interpolated_string_prefix_len(text, i)
        if interp_prefix > 0:
            i, ok = _scan_interpolated_string(text, i + interp_prefix, out)
            if not ok:
                return i, False
            continue

        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "/" and nxt == "-":
            i, ok = _skip_block_comment(text, i, out)
            if not ok:
                return i, False
            continue
        if ch == "-" and nxt == "-":
            i = _skip_line_comment(text, i, out)
            continue
        char_end = _char_literal_end(text, i)
        if char_end > i:
            i = char_end
            continue
        if ch == '"':
            i, ok = _skip_plain_string(text, i + 1)
            if not ok:
                return i, False
            continue
        out.append(ch)
        i += 1
    return i, True


def _scan_interpolated_string(
    text: str, start: int, out: List[str]
) -> tuple[int, bool]:
    i = start
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "\\" and i + 1 < n:
            i += 2
            continue
        if ch == '"':
            return i + 1, True
        if ch == "{" and nxt == "{":
            i += 2
            continue
        if ch == "}" and nxt == "}":
            i += 2
            continue
        if ch == "{":
            out.append("{")
            i, ok = _scan_interpolation_expr(text, i + 1, out)
            if not ok:
                return i, False
            continue
        i += 1
    return i, False


def _scan_interpolation_expr(text: str, start: int, out: List[str]) -> tuple[int, bool]:
    i = start
    n = len(text)
    depth = 0
    while i < n:
        interp_prefix = _interpolated_string_prefix_len(text, i)
        if interp_prefix > 0:
            i, ok = _scan_interpolated_string(text, i + interp_prefix, out)
            if not ok:
                return i, False
            continue

        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "/" and nxt == "-":
            i, ok = _skip_block_comment(text, i, out)
            if not ok:
                return i, False
            continue
        if ch == "-" and nxt == "-":
            i = _skip_line_comment(text, i, out)
            continue
        char_end = _char_literal_end(text, i)
        if char_end > i:
            i = char_end
            continue
        if ch == '"':
            i, ok = _skip_plain_string(text, i + 1)
            if not ok:
                return i, False
            continue
        if ch == "{":
            depth += 1
            out.append(ch)
            i += 1
            continue
        if ch == "}":
            out.append(ch)
            i += 1
            if depth == 0:
                return i, True
            depth -= 1
            continue
        out.append(ch)
        i += 1
    return i, False


def _skip_block_comment(text: str, start: int, out: List[str]) -> tuple[int, bool]:
    i = start
    n = len(text)
    depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "/" and nxt == "-":
            depth += 1
            i += 2
            continue
        if ch == "-" and nxt == "/" and depth > 0:
            depth -= 1
            i += 2
            if depth == 0:
                return i, True
            continue
        if ch == "\n":
            out.append("\n")
        i += 1
    return i, False


def _skip_line_comment(text: str, start: int, out: List[str]) -> int:
    i = start
    n = len(text)
    while i < n and text[i] != "\n":
        i += 1
    if i < n:
        out.append("\n")
        i += 1
    return i


def _skip_plain_string(text: str, start: int) -> tuple[int, bool]:
    i = start
    n = len(text)
    while i < n:
        if text[i] == "\\" and i + 1 < n:
            i += 2
            continue
        if text[i] == '"':
            return i + 1, True
        i += 1
    return i, False


def _char_literal_end(text: str, start: int) -> int:
    if start >= len(text) or text[start] != "'":
        return start
    if start + 2 < len(text) and text[start + 2] == "'":
        return start + 3
    if start + 3 < len(text) and text[start + 1] == "\\" and text[start + 3] == "'":
        return start + 4
    return start


def _interpolated_string_prefix_len(text: str, start: int) -> int:
    n = len(text)
    if start >= n or not (text[start].isalpha() or text[start] == "_"):
        return 0
    i = start + 1
    while i < n and (text[i].isalnum() or text[i] == "_"):
        i += 1
    if i + 1 < n and text[i] == "!" and text[i + 1] == '"':
        return i + 2 - start
    return 0


# ------------------------------------------------------------------
# BM25 inverted index
# ------------------------------------------------------------------


class IncrementalBM25:
    """Incremental BM25 inverted index supporting dynamic document additions.

    Supports both incremental ``add_document`` calls and full ``rebuild``
    from scratch.  Shared by PersistentMemory and ProvenLemmaIndex.
    """

    def __init__(self, k1: float = 1.2, b: float = 0.75) -> None:
        self.k1 = k1
        self.b = b
        # token -> [(doc_id, term_frequency)]
        self._inv: Dict[str, List[Tuple[int, int]]] = defaultdict(list)
        self._doc_len: Dict[int, int] = {}
        self._total_len: int = 0
        self._df: Dict[str, int] = defaultdict(int)
        self._n_docs: int = 0
        self._lock = threading.RLock()

    @property
    def _avg_len(self) -> float:
        return self._total_len / self._n_docs if self._n_docs else 1.0

    @staticmethod
    def _build_state(token_lists: Sequence[Sequence[str]]) -> tuple[
        Dict[str, List[Tuple[int, int]]],
        Dict[int, int],
        int,
        Dict[str, int],
        int,
    ]:
        inv: Dict[str, List[Tuple[int, int]]] = defaultdict(list)
        doc_len: Dict[int, int] = {}
        total_len = 0
        df: Dict[str, int] = defaultdict(int)
        n_docs = 0
        for doc_id, tokens in enumerate(token_lists):
            tf: Dict[str, int] = defaultdict(int)
            for t in tokens:
                tf[t] += 1
            seen: set[str] = set()
            for t, count in tf.items():
                inv[t].append((doc_id, count))
                if t not in seen:
                    df[t] += 1
                    seen.add(t)
            token_count = len(tokens)
            doc_len[doc_id] = token_count
            total_len += token_count
            n_docs += 1
        return inv, doc_len, total_len, df, n_docs

    def add_document(self, doc_id: int, tokens: List[str]) -> None:
        """Incrementally add one document to the index."""
        token_list = list(tokens)
        with self._lock:
            if doc_id in self._doc_len:
                raise ValueError(f"BM25 doc_id {doc_id} already exists")
            tf: Dict[str, int] = defaultdict(int)
            for t in token_list:
                tf[t] += 1
            seen: set[str] = set()
            for t, count in tf.items():
                self._inv[t].append((doc_id, count))
                if t not in seen:
                    self._df[t] += 1
                    seen.add(t)
            self._doc_len[doc_id] = len(token_list)
            self._total_len += len(token_list)
            self._n_docs += 1

    def rebuild(self, token_lists: List[List[str]]) -> None:
        """Full index rebuild from scratch (e.g. after eviction)."""
        materialized = [list(tokens) for tokens in token_lists]
        inv, doc_len, total_len, df, n_docs = self._build_state(materialized)
        with self._lock:
            self._inv = inv
            self._doc_len = doc_len
            self._total_len = total_len
            self._df = df
            self._n_docs = n_docs

    def score(self, query_tokens: List[str]) -> Dict[int, float]:
        """BM25-score all documents matching any query token.

        Returns ``{doc_id: score}`` for all documents that share at least
        one token with *query_tokens*.
        """
        with self._lock:
            if not self._n_docs or not query_tokens:
                return {}
            avg_dl = self._avg_len
            n = self._n_docs
            scores: Dict[int, float] = defaultdict(float)
            for qt in set(query_tokens):
                postings = self._inv.get(qt)
                if not postings:
                    continue
                df = self._df.get(qt, 0)
                # Standard BM25 IDF: log((N - df + 0.5) / (df + 0.5) + 1)
                idf = math.log((n - df + 0.5) / (df + 0.5) + 1.0)
                for doc_id, tf in postings:
                    dl = self._doc_len.get(doc_id, 1)
                    num = tf * (self.k1 + 1.0)
                    den = tf + self.k1 * (1.0 - self.b + self.b * dl / avg_dl)
                    scores[doc_id] += idf * num / den
            return dict(scores)
