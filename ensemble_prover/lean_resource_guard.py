"""Cheap preflight guards for Lean workloads known to explode locally."""

from __future__ import annotations

import re


DANGEROUS_NAT_POW_TOWER_REASON = (
    "dangerous Nat.pow tower: concrete evaluation or normalization can make "
    "Lean allocate enormous numerals"
)

_DANGEROUS_POW_PATTERNS = (
    re.compile(r"10\^10\^10\^"),
    re.compile(r"10\^\(10\^10\^"),
    re.compile(r"10\^\(10\^\(10\^"),
)
_DANGEROUS_NAT_POW_RAW_RE = re.compile(
    r"Nat\.pow\s+10\s*\(\s*Nat\.pow\s+10\s*\(\s*Nat\.pow\s+10"
)

_EXPENSIVE_NORMALIZER_RE = re.compile(
    r"\b(ring_nf|ring|norm_num|native_decide|decide)\b"
)


def _compact_lean_text(text: str) -> str:
    return re.sub(r"\s+", "", str(text or ""))


def _strip_lean_comments(text: str) -> str:
    no_block = re.sub(r"/-.*?-/", " ", str(text or ""), flags=re.DOTALL)
    return re.sub(r"--.*", " ", no_block)


def looks_like_dangerous_nat_pow_tower(text: str) -> bool:
    """Return true for Nat power towers that should not be concretely evaluated."""

    raw = str(text or "")
    if "10" not in raw or "^" not in raw:
        return bool(_DANGEROUS_NAT_POW_RAW_RE.search(raw))
    compact = _compact_lean_text(raw)
    return any(pattern.search(compact) for pattern in _DANGEROUS_POW_PATTERNS) or bool(
        _DANGEROUS_NAT_POW_RAW_RE.search(raw)
    )


def uses_expensive_normalizer(code: str) -> bool:
    """Detect tactics likely to normalize/evaluate enormous Nat expressions."""

    stripped = _strip_lean_comments(str(code or ""))
    return bool(_EXPENSIVE_NORMALIZER_RE.search(stripped))


def should_block_expensive_nat_pow_probe(*, goal_statement: str, code: str) -> bool:
    return looks_like_dangerous_nat_pow_tower(goal_statement) and uses_expensive_normalizer(
        code
    )


__all__ = [
    "DANGEROUS_NAT_POW_TOWER_REASON",
    "looks_like_dangerous_nat_pow_tower",
    "should_block_expensive_nat_pow_probe",
    "uses_expensive_normalizer",
]
