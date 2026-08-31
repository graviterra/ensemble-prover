"""Coercion-aware repair guidance for ``mini_prover``.

Hard Putnam formalizations often fail after the mathematics is right because
Lean sees arithmetic in the wrong carrier: ``Fin n`` instead of ``ℕ``/``ℤ``,
``Nat`` subtraction where ``Int`` subtraction was intended, or divisibility
mixed between ``ℕ`` and ``ℤ``/``ZMod``. This module keeps that diagnosis out of
``mini_prover.py`` and turns structured Lean failures into compact, targeted
repair instructions.
"""

from __future__ import annotations

import re
from typing import Any, Mapping


_FIN_INSTANCE_RE = re.compile(r"\b(?:AddCommMonoid|OfNat|HAdd|HMul|HSub)\s+\(Fin\b")
_CAST_MARKERS = ("↑", "Nat", "Int", "ℕ", "ℤ", "ZMod", "Int.subNatNat")
_NAT_EXPECTED_ANGLE_CONSTRUCTOR_RE = re.compile(
    r"Invalid\s+[`']?⟨\.\.\.⟩[`']?\s+notation.*?"
    r"expected\s+type\s+[`']?(?:ℕ|Nat)[`']?",
    re.IGNORECASE | re.DOTALL,
)


def coercion_repair_actions(analysis: Mapping[str, Any]) -> list[str]:
    """Return targeted coercion/cast repair actions for a Lean failure."""

    family = str(analysis.get("error_type") or "")
    details = dict(analysis.get("details") or {})
    goals = list(analysis.get("remaining_goals") or [])
    diagnostics = list(analysis.get("diagnostics") or [])
    text = _analysis_text(family, details, goals, diagnostics)
    actions: list[str] = []

    if _FIN_INSTANCE_RE.search(text) or "AddCommMonoid (Fin" in text:
        actions.append(
            "You are doing arithmetic in `Fin n`. Do not write `k * n`, `l + 1`, or numerals at type `Fin n`; first project/cast indices, e.g. `((k : ℕ) : ℤ)`, `(k.1 : ℤ)`, `((l : ℕ) : ℤ) + 1`, then use `norm_num`/`ring_nf`."
        )

    if _NAT_EXPECTED_ANGLE_CONSTRUCTOR_RE.search(text):
        actions.append(
            "Lean expected a natural number but saw constructor notation `⟨x, h⟩`. If a function has type `ℕ → ...`, apply it to `x`, not `⟨x, h⟩`; use `⟨x, h⟩` only when the expected type is `Fin n` or a subtype."
        )

    if "Fin.eq_zero_or_eq_one" in text:
        actions.append(
            "`Fin.eq_zero_or_eq_one` is not a Mathlib fact to cite. For a term `x : Fin 2`, split cases with `fin_cases x` or `cases x using Fin.cases`, then discharge numerals with `norm_num`/`simp`."
        )

    if "HSub Type ℕ Type" in text or "ℤ - 1" in text:
        actions.append(
            "Parenthesize casts before subtraction: write `((n : ℤ) - 1)` or `((p : ℕ) - 1 : ℕ)`, never an expression that Lean can parse as a type like `ℤ - 1`."
        )

    if family in {"type_mismatch", "missing_instance", "tactic_failed", "unsolved_goals"} and _has_cast_pressure(text):
        actions.append(
            "Normalize casts explicitly before automation: try `norm_num at *`, `norm_cast at *`, `push_cast at *`, or `zify at *` before `omega`/`ring_nf`; if a rewrite changes carrier, insert a small `have` with the exact casted type Lean shows."
        )

    if _looks_like_int_divisibility(text):
        actions.append(
            "For mixed `ℕ`/`ℤ` divisibility, choose one carrier early. Either move the goal to `ℕ` with `norm_num`/`norm_cast`, or move to modular arithmetic with `ZMod.intCast_zmod_eq_zero_iff_dvd`; avoid alternating `Nat` and `Int` divisibility in the same step."
        )

    return _dedupe(actions)


def _analysis_text(
    family: str,
    details: Mapping[str, Any],
    goals: list[Any],
    diagnostics: list[Any],
) -> str:
    parts = [family]
    for key in (
        "expected_type",
        "actual_type",
        "missing_instance",
        "failed_tactic",
        "unification_failure",
    ):
        value = details.get(key)
        if value:
            parts.append(str(value))
    for diag in diagnostics:
        if isinstance(diag, Mapping):
            parts.append(str(diag.get("summary") or ""))
            parts.append(str(diag.get("message") or ""))
    for goal in goals:
        if isinstance(goal, Mapping):
            parts.append(str(goal.get("target") or ""))
            parts.extend(str(item) for item in list(goal.get("hypotheses") or []))
    return "\n".join(parts)


def _has_cast_pressure(text: str) -> bool:
    return any(marker in text for marker in _CAST_MARKERS)


def _looks_like_int_divisibility(text: str) -> bool:
    """Mixed-carrier divisibility: a ``∣`` whose OWN expression involves an
    Int/ZMod carrier or a cast.

    Requires CO-LOCATION — the divisibility and the cast marker on the same line.
    ``_analysis_text`` joins the family, details, diagnostics, and every goal's
    target/hypotheses with newlines, so a bare ``"∣" in text and "ℤ" in text``
    flat scan fires whenever a ``∣`` on one goal coincides with an unrelated
    ``ℤ``/``Int``/``ZMod``/``↑`` on a *different* goal or hypothesis — mis-routing
    Nat-only divisibility toward Int/ZMod carrier changes. Scanning per line
    keeps the marker attached to the divisibility expression itself.
    """

    for line in text.splitlines():
        if "∣" in line and (
            "ℤ" in line or "Int" in line or "ZMod" in line or "↑" in line
        ):
            return True
    return False


def _dedupe(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


__all__ = ["coercion_repair_actions"]
