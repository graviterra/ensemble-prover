"""Cheap preflight guards for Lean workloads known to explode locally."""

from __future__ import annotations

import re

from .math_utils import _strip_lean_comments_and_strings


DANGEROUS_NAT_POW_TOWER_REASON = (
    "dangerous Nat.pow tower: concrete evaluation or normalization can make "
    "Lean allocate enormous numerals"
)

# A right-associated tower of at least three ``10`` bases, e.g. ``10^10^10``
# (= 10^(10^10)) or ``10^(10^10)``.  Optional opening parentheses are allowed
# before each base because Lean also accepts ``10^(10^(10))``.  The safe
# left-associated ``(10^10)^10`` (= 10^100) is deliberately not matched: the
# closing parenthesis breaks the chain before the following ``^``.
_DANGEROUS_POW_TOWER_RE = re.compile(r"10\^\(*10\^\(*10")

# The same tower spelled with ``Nat.pow``.  Three nested applications are
# always a tower; two nested applications are a tower once the innermost
# exponent is itself a concrete ``10``-headed numeral.
_DANGEROUS_NAT_POW_RAW_RE = re.compile(
    r"Nat\.pow\s+10\s*\(\s*Nat\.pow\s+10\s*(?:\(\s*Nat\.pow\s+10|10)"
)

_EXPENSIVE_NORMALIZER_RE = re.compile(
    r"\b(ring_nf|ring|norm_num|native_decide|decide)\b"
)


def _compact_lean_text(text: str) -> str:
    return re.sub(r"\s+", "", str(text or ""))


def _mask_lean_non_code(text: str) -> str:
    """Blank comments and string literals so scans only see executable code."""

    masked, _lexically_closed = _strip_lean_comments_and_strings(str(text or ""))
    return masked


def looks_like_dangerous_nat_pow_tower(text: str) -> bool:
    """Return true for Nat power towers that should not be concretely evaluated."""

    masked = _mask_lean_non_code(text)
    compact = _compact_lean_text(masked)
    return bool(_DANGEROUS_POW_TOWER_RE.search(compact)) or bool(
        _DANGEROUS_NAT_POW_RAW_RE.search(masked)
    )


def uses_expensive_normalizer(code: str) -> bool:
    """Detect tactics likely to normalize/evaluate enormous Nat expressions."""

    masked = _mask_lean_non_code(code)
    return bool(_EXPENSIVE_NORMALIZER_RE.search(masked))


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
