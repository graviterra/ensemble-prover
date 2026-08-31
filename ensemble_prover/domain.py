"""Problem domain classification and tactic palette selection.

Classifies Lean statements by mathematical domain and returns
domain-specific tactic suggestions and Mathlib lemma prefixes
for prompt augmentation.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Dict, List, Sequence, Tuple


@dataclass
class DomainHint:
    domain: str
    primary_tactics: List[str]
    useful_lemma_prefixes: List[str]
    avoidance_note: str = ""


@dataclass(frozen=True)
class DomainTacticPalette:
    """Structured tactic palette for one mathematical domain."""

    domain: str
    algebraic_tactics: Tuple[str, ...] = ()
    fast_path_safe_tactics: Tuple[str, ...] = ()
    structural_tactics: Tuple[str, ...] = ()
    search_tactics: Tuple[str, ...] = ()
    negation_tactics: Tuple[str, ...] = ()
    domain_specific_tactics: Tuple[str, ...] = ()
    opt_in_tactics: Tuple[str, ...] = ()
    oracle_domain_specific_tactics: Tuple[str, ...] = ()
    signature_tactics: Tuple[str, ...] = ()
    useful_lemma_prefixes: Tuple[str, ...] = ()
    avoidance_note: str = ""
    family_bias_order: Tuple[str, ...] = (
        "domain_specific",
        "structural",
        "search",
        "negation",
        "algebraic",
    )
    oracle_family_order: Tuple[str, ...] = (
        "domain_specific",
        "structural",
        "search",
        "simp",
        "analysis",
        "negation",
        "arithmetic",
    )


@dataclass(frozen=True)
class ProblemProfile:
    """Shared structural summary of a theorem statement / goal state."""

    statement_domain: str
    learning_domains: Tuple[str, ...]
    learning_family: str
    has_hypotheses: bool
    has_arithmetic: bool
    has_structure: bool
    has_negation: bool
    has_extensional: bool
    has_equality: bool
    has_finite_objects: bool
    has_measure: bool
    has_probability: bool


# Keyword -> domain mapping (checked in order, first match wins)
_DOMAIN_PATTERNS: List[Tuple[str, str]] = [
    (
        r"\b(ProbabilityTheory|RandomVariable|IdentDistrib|Indep(?:Fun|Set|Sets)?|expectation|variance|stdDev)\b",
        "probability",
    ),
    (
        r"\b(MeasureTheory|Measurable(?:Set)?|AEMeasurable|AEStronglyMeasurable|OuterMeasure|lintegral|ENNReal)\b",
        "measure_theory",
    ),
    (
        r"\b(Prime|Nat\.prime|Nat\.gcd|Nat\.lcm|ZMod|Int\.emod|dvd|Finset\.sum.*dvd)\b",
        "number_theory",
    ),
    (
        r"\b(Polynomial|Ring(?:Hom)?|Field|Ideal|algebraMap|CommRing|Semiring|Monoid|Group)\b",
        "algebra",
    ),
    (
        r"\b(Real\.|Complex\.|Filter\.|Tendsto|atTop|Continuous(?:On)?|"
        r"Differentiable|ContDiff|MeasureTheory|integral|deriv|summable|"
        r"Cauchy|ConvexOn|StrictConvexOn|ConcaveOn|StrictConcaveOn|"
        r"Monotone(?:On)?|Antitone(?:On)?|StrictMono|StrictAnti|"
        r"HasDeriv(?:At|WithinAt)?)\b|[∫∑∏]",
        "analysis",
    ),
    (r"\b(Finset\.|Fintype|Multiset|Nat\.choose|\.card\b|ncard)\b", "combinatorics"),
    (
        r"\b(Metric\.|TopologicalSpace|IsOpen|IsClosed|IsCompact|Connected)\b",
        "topology",
    ),
    (
        r"\b(EuclideanGeometry|Affine(?:Subspace)?|Collinear|convexHull|Orthogonal|"
        r"NormedAddTorsor|InnerProductGeometry|midpoint|angle)\b"
        r"|\bdist\b(?!\s*[:=])",
        "geometry",
    ),
    (
        r"\b(Matrix|LinearMap|Submodule|Basis|LinearIndependent|Module|eigenspace|eigenvector)\b"
        r"|\.rank\b|\b(?:rank|det|span)\b(?!\s*[:=])",
        "linear_algebra",
    ),
]

_SHARED_CORE_TACTICS: Dict[str, Tuple[str, ...]] = {
    "structural": (
        "have",
        "refine",
        "change",
        "convert",
        "by_cases",
        "calc",
        "constructor",
        "ext",
        "funext",
    ),
    "search": (
        "solve_by_elim",
        "apply?",
        "exact?",
        "rw?",
        "simp?",
        "aesop",
    ),
    "negation": (
        "by_contra",
        "contrapose",
        "push_neg",
    ),
}

_OPT_IN_TACTIC_FLAGS: Dict[str, str] = {
    "native_decide": "include_native_decide",
    "polyrith": "include_polyrith",
}
_OPT_IN_FLAG_ORDER: Tuple[str, ...] = tuple(
    dict.fromkeys(_OPT_IN_TACTIC_FLAGS.values())
)


def _coerce_text(value: Any) -> str:
    try:
        return str(value or "")
    except Exception:
        return ""


def _coerce_bool_flag(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return False
    if isinstance(value, (int, float)):
        return bool(value)
    text = _coerce_text(value).strip().lower()
    if not text:
        return False
    if text in {"1", "true", "yes", "on"}:
        return True
    if text in {"0", "false", "no", "off"}:
        return False
    return bool(value)


def _dedupe_tactics(*groups: Sequence[str]) -> List[str]:
    ordered: List[str] = []
    seen: set[str] = set()
    for group in groups:
        for tactic in group:
            text = str(tactic or "").strip()
            if not text or text in seen:
                continue
            seen.add(text)
            ordered.append(text)
    return ordered


def enabled_opt_in_tactics_from_config(cfg: Any) -> Tuple[str, ...]:
    """Return enabled opt-in tactic flags from a tactic-oracle-like config."""
    if cfg is None:
        return ()
    return tuple(
        flag
        for flag in _OPT_IN_FLAG_ORDER
        if _coerce_bool_flag(getattr(cfg, flag, False))
    )


def _ordered_domains_with_statement(
    domains: Sequence[str],
    *,
    statement_domain: str = "",
) -> List[str]:
    ordered_domains: List[str] = []
    for domain in domains:
        text = str(domain or "").strip()
        if text and text not in ordered_domains:
            ordered_domains.append(text)
    statement_text = str(statement_domain or "").strip()
    if statement_text and statement_text not in ordered_domains:
        ordered_domains.append(statement_text)
    return ordered_domains


def _merge_ordered_domains(*domain_groups: Sequence[str]) -> List[str]:
    ordered: List[str] = []
    for group in domain_groups:
        for domain in group:
            text = _coerce_text(domain).strip()
            if text and text not in ordered:
                ordered.append(text)
    return ordered


_DECLARED_BINDER_GROUP_RE = re.compile(r"[\(\{\[⦃]\s*([^:()\[\]{}⦃⦄]+?)\s*:")
_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def _mask_declared_binder_names(text: str) -> str:
    rendered = _coerce_text(text)
    if not rendered.strip():
        return ""
    declared_names: set[str] = set()
    for match in _DECLARED_BINDER_GROUP_RE.finditer(rendered):
        names = [
            token
            for token in re.split(r"\s+", str(match.group(1) or "").strip())
            if token and token != "_" and _IDENTIFIER_RE.fullmatch(token)
        ]
        declared_names.update(names)
    masked = rendered
    for name in sorted(declared_names, key=len, reverse=True):
        masked = re.sub(rf"\b{re.escape(name)}\b", " ", masked)
    return masked


def _enabled_opt_in_tactics_for_palette(
    palette: DomainTacticPalette,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> Tuple[str, ...]:
    enabled_flags = {
        str(flag or "").strip()
        for flag in enabled_opt_in_tactics
        if str(flag or "").strip()
    }
    if not palette.opt_in_tactics or not enabled_flags:
        return ()
    return tuple(
        tactic
        for tactic in palette.opt_in_tactics
        if _OPT_IN_TACTIC_FLAGS.get(str(tactic or "").strip()) in enabled_flags
    )


_DOMAIN_TACTIC_PALETTES: Dict[str, DomainTacticPalette] = {
    "number_theory": DomainTacticPalette(
        domain="number_theory",
        algebraic_tactics=(
            "omega",
            "norm_num",
            "ring",
            "ring_nf",
            "norm_cast",
            "zify",
            "linarith",
            "nlinarith",
            "positivity",
        ),
        fast_path_safe_tactics=(
            "omega",
            "norm_num",
            "norm_cast",
            "zify",
            "linarith",
            "nlinarith",
        ),
        structural_tactics=("cases", "rcases", "obtain", "induction"),
        search_tactics=("decide",),
        negation_tactics=("exfalso",),
        domain_specific_tactics=(
            "interval_cases",
            "mod_cases",
            "simp [Nat.prime_def_lt]",
        ),
        opt_in_tactics=("native_decide",),
        oracle_domain_specific_tactics=(
            "interval_cases",
            "mod_cases",
            "simp [Nat.prime_def_lt]",
            "apply Nat.dvd_iff_mod_eq_zero.mpr",
            "apply ZMod.val_natCast",
        ),
        signature_tactics=(
            "interval_cases",
            "mod_cases",
            "simp [Nat.prime_def_lt]",
        ),
        useful_lemma_prefixes=(
            "Nat.",
            "Int.",
            "ZMod.",
            "Finset.sum_",
            "Nat.gcd_",
            "Nat.lcm_",
        ),
        avoidance_note=(
            "Use interval_cases/mod_cases for bounded modular goals. Normalize "
            "dvd/gcd/lcm rewrites and transfer residue arguments through ZMod "
            "before heavy algebra."
        ),
        family_bias_order=(
            "domain_specific",
            "algebraic",
            "structural",
            "search",
            "negation",
        ),
        oracle_family_order=(
            "domain_specific",
            "arithmetic",
            "structural",
            "search",
            "negation",
            "simp",
            "analysis",
        ),
    ),
    "algebra": DomainTacticPalette(
        domain="algebra",
        algebraic_tactics=(
            "ring",
            "ring_nf",
            "field_simp",
            "norm_num",
            "norm_cast",
            "linarith",
            "nlinarith",
            "positivity",
            "gcongr",
            "abel",
            "group",
        ),
        fast_path_safe_tactics=(
            "ring",
            "ring_nf",
            "norm_num",
            "norm_cast",
            "linarith",
            "nlinarith",
        ),
        structural_tactics=("congr", "nth_rewrite"),
        domain_specific_tactics=(
            "linear_combination",
            "noncomm_ring",
            "simp_rw",
            "congr!",
        ),
        opt_in_tactics=("polyrith",),
        oracle_domain_specific_tactics=("noncomm_ring", "simp_rw"),
        signature_tactics=("polyrith", "linear_combination", "noncomm_ring"),
        useful_lemma_prefixes=(
            "Polynomial.",
            "RingHom.",
            "Ideal.",
            "MulZeroClass.",
            "MonoidHom.",
        ),
        avoidance_note=(
            "Use ring-side normalization plus simp_rw/congr lemmas before "
            "escalating to field_simp or broad search."
        ),
        family_bias_order=(
            "domain_specific",
            "algebraic",
            "structural",
            "search",
            "negation",
        ),
        oracle_family_order=(
            "domain_specific",
            "arithmetic",
            "structural",
            "search",
            "simp",
            "negation",
            "analysis",
        ),
    ),
    "analysis": DomainTacticPalette(
        domain="analysis",
        algebraic_tactics=(
            "linarith",
            "nlinarith",
            "norm_num",
            "ring",
            "ring_nf",
            "field_simp",
            "norm_cast",
            "positivity",
        ),
        fast_path_safe_tactics=("linarith", "nlinarith", "norm_num", "ring"),
        structural_tactics=("cases",),
        negation_tactics=("exfalso",),
        domain_specific_tactics=(
            "continuity",
            "fun_prop",
            "measurability",
            "mono",
            "filter_upwards",
        ),
        oracle_domain_specific_tactics=(
            "continuity",
            "fun_prop",
            "measurability",
            "mono",
            "filter_upwards",
            "apply ContinuousOn.intervalIntegrable",
        ),
        useful_lemma_prefixes=(
            "Real.",
            "Filter.",
            "MeasureTheory.",
            "ContinuousOn.",
            "Tendsto.",
        ),
        avoidance_note=(
            "For limits and integrals, get the goal into Tendsto/integral API "
            "shape before leaning on arithmetic cleanup. "
            "For IntervalIntegrable goals, use `apply ContinuousOn.intervalIntegrable` "
            "to reduce to ContinuousOn, then decompose with ContinuousOn.div/.sqrt/.log "
            "and close positivity/nonvanishing side goals with linarith."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "search",
            "negation",
            "algebraic",
        ),
        oracle_family_order=(
            "domain_specific",
            "analysis",
            "structural",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
    "combinatorics": DomainTacticPalette(
        domain="combinatorics",
        algebraic_tactics=("omega", "norm_num", "linarith", "nlinarith"),
        fast_path_safe_tactics=("omega", "norm_num", "linarith", "nlinarith"),
        structural_tactics=("cases", "rcases", "obtain", "induction"),
        search_tactics=("decide",),
        negation_tactics=("exfalso",),
        domain_specific_tactics=(
            "fin_cases",
            "choose",
            "simp [Finset.card_filter]",
            "rw [Finset.sum_filter]",
        ),
        oracle_domain_specific_tactics=(
            "fin_cases",
            "simp [Finset.card_filter]",
            "apply Finset.sum_comm",
            "apply Finset.sum_bij",
        ),
        signature_tactics=(
            "fin_cases",
            "choose",
            "simp [Finset.card_filter]",
            "rw [Finset.sum_filter]",
        ),
        useful_lemma_prefixes=("Finset.", "Fintype.", "Nat.choose_", "Pigeonhole."),
        avoidance_note=(
            "Open finite/cardinality goals with fin_cases, choose, and Finset "
            "cardinality rewrites before arithmetic fallback. "
            "For double-counting or sum rearrangement, use Finset.sum_comm "
            "to swap summation order."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "search",
            "negation",
            "algebraic",
        ),
        oracle_family_order=(
            "domain_specific",
            "structural",
            "search",
            "simp",
            "analysis",
            "negation",
            "arithmetic",
        ),
    ),
    "topology": DomainTacticPalette(
        domain="topology",
        algebraic_tactics=("linarith", "norm_num", "ring"),
        fast_path_safe_tactics=("linarith", "norm_num", "ring"),
        structural_tactics=("cases", "apply"),
        domain_specific_tactics=(
            "continuity",
            "fun_prop",
            "apply IsOpen.inter",
            "simp [Set.ext_iff]",
        ),
        oracle_domain_specific_tactics=(
            "continuity",
            "fun_prop",
            "apply IsOpen.inter",
            "apply IsCompact.isCompact_iUnion",
            "apply IsClosed.inter",
            "apply IsCompact.isBounded",
            "apply Metric.isCompact_iff_isClosed_isBounded.mpr",
        ),
        signature_tactics=("apply IsOpen.inter", "simp [Set.ext_iff]"),
        useful_lemma_prefixes=("TopologicalSpace.", "Metric.", "IsCompact.", "Set."),
        avoidance_note=(
            "Lean on IsOpen/IsClosed/IsCompact APIs and set extensionality "
            "before algebraic normalization. For compactness, use "
            "Metric.isCompact_iff_isClosed_isBounded to split into closedness "
            "and boundedness."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "search",
            "negation",
            "algebraic",
        ),
        oracle_family_order=(
            "domain_specific",
            "structural",
            "analysis",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
    "measure_theory": DomainTacticPalette(
        domain="measure_theory",
        algebraic_tactics=(
            "linarith",
            "nlinarith",
            "norm_num",
            "field_simp",
            "norm_cast",
        ),
        fast_path_safe_tactics=("linarith", "nlinarith", "norm_num", "norm_cast"),
        domain_specific_tactics=(
            "measurability",
            "fun_prop",
            "filter_upwards",
            "simp [MeasureTheory.ae_iff]",
        ),
        oracle_domain_specific_tactics=(
            "measurability",
            "fun_prop",
            "filter_upwards",
            "apply ContinuousOn.intervalIntegrable",
            "apply MeasureTheory.integral_congr",
            "apply MeasureTheory.setIntegral_congr",
            "apply MeasureTheory.integral_add",
        ),
        signature_tactics=("simp [MeasureTheory.ae_iff]",),
        useful_lemma_prefixes=(
            "MeasureTheory.",
            "Measure.",
            "MeasurableSet.",
            "ENNReal.",
            "MeasureTheory.ae_",
        ),
        avoidance_note=(
            "Use ae / a.e. rewrites and lintegral / ENNReal lemmas before "
            "algebraic cleanup. "
            "For IntervalIntegrable goals, use `apply ContinuousOn.intervalIntegrable` "
            "to reduce to ContinuousOn, then decompose structurally. "
            "For integral equalities, use integral_congr or setIntegral_congr "
            "to reduce to pointwise equality."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "search",
            "negation",
            "algebraic",
        ),
        oracle_family_order=(
            "domain_specific",
            "analysis",
            "structural",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
    "probability": DomainTacticPalette(
        domain="probability",
        algebraic_tactics=("norm_num", "linarith", "nlinarith", "field_simp"),
        fast_path_safe_tactics=("norm_num", "linarith", "nlinarith"),
        structural_tactics=("cases",),
        domain_specific_tactics=(
            "measurability",
            "fun_prop",
            "filter_upwards",
            "simp [MeasureTheory.ae_iff]",
        ),
        oracle_domain_specific_tactics=(
            "measurability",
            "fun_prop",
            "filter_upwards",
            "apply ProbabilityTheory.IndepFun.integral_mul_of_integrable",
            "apply MeasureTheory.integral_nonneg",
        ),
        useful_lemma_prefixes=(
            "ProbabilityTheory.",
            "MeasureTheory.",
            "ENNReal.",
            "ProbabilityTheory.variance",
        ),
        avoidance_note=(
            "Prefer expectation / variance / independence APIs and "
            "measurability facts before raw arithmetic. "
            "For E[XY] with independent X, Y use IndepFun.integral_mul_of_integrable."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "search",
            "negation",
            "algebraic",
        ),
        oracle_family_order=(
            "domain_specific",
            "analysis",
            "structural",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
    "geometry": DomainTacticPalette(
        domain="geometry",
        algebraic_tactics=(
            "linarith",
            "nlinarith",
            "norm_num",
            "ring",
            "ring_nf",
            "field_simp",
            "positivity",
            "gcongr",
        ),
        fast_path_safe_tactics=("linarith", "nlinarith", "norm_num", "ring"),
        structural_tactics=("cases", "rcases", "obtain"),
        domain_specific_tactics=("simp [dist_eq_norm]", "simp [sub_eq_add_neg]"),
        oracle_domain_specific_tactics=(
            "simp [dist_eq_norm]",
            "simp [sub_eq_add_neg]",
            "apply Convex.inner_smul_le_inner_smul_iff",
            "apply dist_triangle",
            "apply abs_le",
            "apply sq_nonneg",
        ),
        signature_tactics=("simp [dist_eq_norm]", "simp [sub_eq_add_neg]"),
        useful_lemma_prefixes=(
            "EuclideanGeometry.",
            "Affine.",
            "Metric.",
            "Convex.",
            "InnerProductSpace.",
        ),
        avoidance_note=(
            "Normalize affine/coordinate expressions and distance rewrites "
            "before heavy search. For triangle inequality and distance "
            "bounds, use dist_triangle and abs_le directly."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "algebraic",
            "search",
            "negation",
        ),
        oracle_family_order=(
            "domain_specific",
            "structural",
            "analysis",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
    "linear_algebra": DomainTacticPalette(
        domain="linear_algebra",
        algebraic_tactics=(
            "ring",
            "ring_nf",
            "linarith",
            "nlinarith",
            "norm_num",
            "field_simp",
            "norm_cast",
        ),
        fast_path_safe_tactics=(
            "ring",
            "ring_nf",
            "linarith",
            "nlinarith",
            "norm_num",
            "norm_cast",
        ),
        domain_specific_tactics=(
            "simp [Matrix.mul_apply]",
            "linear_combination",
            "simp [LinearMap.map_add]",
        ),
        oracle_domain_specific_tactics=(
            "simp [Matrix.mul_apply]",
            "linear_combination",
            "apply Matrix.ext",
            "apply LinearMap.ext",
            "apply Basis.ext",
            "apply Matrix.det_eq_prod_diag",
            "simp [Matrix.det_fin_two]",
        ),
        signature_tactics=("simp [Matrix.mul_apply]", "simp [LinearMap.map_add]"),
        useful_lemma_prefixes=(
            "Matrix.",
            "LinearMap.",
            "Submodule.",
            "Basis.",
            "Module.",
        ),
        avoidance_note=(
            "Use matrix extensionality (Matrix.ext), basis/submodule APIs, and "
            "linear_combination before scalar arithmetic. For determinants, "
            "use det_fin_two/det_fin_three for small matrices."
        ),
        family_bias_order=(
            "domain_specific",
            "structural",
            "algebraic",
            "search",
            "negation",
        ),
        oracle_family_order=(
            "domain_specific",
            "structural",
            "analysis",
            "search",
            "simp",
            "negation",
            "arithmetic",
        ),
    ),
}


def _domain_specific_tactics_for_palette(
    palette: DomainTacticPalette,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> Tuple[str, ...]:
    groups: List[Sequence[str]] = [
        palette.domain_specific_tactics,
        _enabled_opt_in_tactics_for_palette(
            palette,
            enabled_opt_in_tactics=enabled_opt_in_tactics,
        ),
    ]
    return tuple(_dedupe_tactics(*groups))


def _oracle_domain_specific_tactics_for_palette(
    palette: DomainTacticPalette,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> Tuple[str, ...]:
    groups: List[Sequence[str]] = []
    if palette.oracle_domain_specific_tactics:
        groups.append(palette.oracle_domain_specific_tactics)
    groups.append(palette.domain_specific_tactics)
    return tuple(_dedupe_tactics(*groups))


def _compose_domain_hint(
    palette: DomainTacticPalette,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> DomainHint:
    sections = {
        "domain_specific": _domain_specific_tactics_for_palette(
            palette,
            enabled_opt_in_tactics=enabled_opt_in_tactics,
        ),
        "algebraic": palette.algebraic_tactics,
        "structural": (
            *_SHARED_CORE_TACTICS["structural"],
            *palette.structural_tactics,
        ),
        "search": (*_SHARED_CORE_TACTICS["search"], *palette.search_tactics),
        "negation": (*_SHARED_CORE_TACTICS["negation"], *palette.negation_tactics),
    }
    ordered_families = tuple(palette.family_bias_order) + tuple(
        family for family in sections if family not in set(palette.family_bias_order)
    )
    primary_tactics = _dedupe_tactics(
        *(sections[family] for family in ordered_families)
    )
    return DomainHint(
        domain=palette.domain,
        primary_tactics=primary_tactics,
        useful_lemma_prefixes=list(palette.useful_lemma_prefixes),
        avoidance_note=palette.avoidance_note,
    )


_DOMAIN_HINTS = {
    domain: _compose_domain_hint(palette)
    for domain, palette in _DOMAIN_TACTIC_PALETTES.items()
}


def _normalize_tactic_signature_text(text: str) -> str:
    normalized = " ".join(str(text or "").strip().lower().split())
    if normalized.startswith("by "):
        normalized = normalized[3:].strip()
    return normalized


_TACTIC_DOMAIN_PREFERENCES: Tuple[Tuple[str, Tuple[str, ...]], ...] = (
    ("continuity", ("topology", "analysis")),
    ("fun_prop", ("probability", "measure_theory", "topology", "analysis")),
    ("measurability", ("probability", "measure_theory")),
    ("filter_upwards", ("probability", "measure_theory")),
    ("mono", ("analysis",)),
    ("linear_combination", ("linear_algebra", "algebra")),
)


_TACTIC_SIGNATURE_DOMAIN_PAIRS: Tuple[Tuple[str, str], ...] = tuple(
    (
        _normalize_tactic_signature_text(signature),
        palette.domain,
    )
    for palette in _DOMAIN_TACTIC_PALETTES.values()
    for signature in palette.signature_tactics
)


def _tactic_signature_matches(text: str, signature: str) -> bool:
    if text == signature:
        return True
    for suffix in (" ", ";", " at ", " <;>"):
        if text.startswith(signature + suffix):
            return True
    return False


def _select_tactic_domain_preference(
    domains: Sequence[str],
    *,
    statement: str = "",
) -> str:
    statement_domains = classify_learning_domains(statement)
    for domain in statement_domains:
        if domain in domains:
            return str(domain)
    if domains:
        return str(domains[-1])
    return "general"


def infer_tactic_domain_family(text: str, *, statement: str = "") -> str:
    """Infer a domain family from standalone tactic text when possible."""
    normalized = _normalize_tactic_signature_text(text)
    if not normalized:
        return "general"
    for signature, preferred_domains in _TACTIC_DOMAIN_PREFERENCES:
        if _tactic_signature_matches(normalized, signature):
            return _select_tactic_domain_preference(
                preferred_domains,
                statement=statement,
            )
    for signature, domain in _TACTIC_SIGNATURE_DOMAIN_PAIRS:
        if _tactic_signature_matches(normalized, signature):
            return str(domain)
    return "general"


_DEFAULT_HINT = DomainHint(
    domain="general",
    primary_tactics=_dedupe_tactics(
        _SHARED_CORE_TACTICS["search"],
        ("simp", "intro", "apply"),
        _SHARED_CORE_TACTICS["structural"],
        ("omega", "linarith", "ring", "norm_num"),
        _SHARED_CORE_TACTICS["negation"],
    ),
    useful_lemma_prefixes=[],
)

_DEFAULT_FAST_PATH_SAFE_TACTICS: Tuple[str, ...] = (
    "omega",
    "norm_num",
    "ring",
    "linarith",
)


_PROFILE_ASCII_ARROW_RE = re.compile(r"<->|->|=>|<-")
_PROFILE_ARITH_OPERATOR_RE = re.compile(
    r"[+*/^]|(?<![<])-(?![>])|≤|≥|≠|(?<!-)[<>](?![=>])"
)
_PROFILE_ARITH_TOKEN_RE = re.compile(
    r"\b(Nat|Int|Rat|Real|Complex|NNReal|ENNReal|ZMod|Polynomial|Semiring|Ring|Field)\b|[ℕℤℚℝℂ]"
)
_PROFILE_STRUCTURE_RE = re.compile(
    r"∀|∃|∧|∨|↔|→|<->|->|=>|<-|\b(And|Or|Iff|Exists|Forall|forall|exists)\b"
)
_PROFILE_NEGATION_RE = re.compile(r"¬|⊥|\b(False|Not)\b")
_PROFILE_EXTENSIONAL_RE = re.compile(
    r"∈|⊆|∪|∩|⋃|⋂|\\|ᶜ|\b("
    r"Set|SetLike|Finset|Multiset|Function|funext|extensional|"
    r"union|inter|subset|image|preimage|compl|insert|erase|"
    r"sUnion|iUnion|sInter|iInter"
    r")\b"
)
_PROFILE_EQUALITY_RE = re.compile(r"(?<![<>!:=-])=(?![=>])")
_PROFILE_FINITE_RE = re.compile(
    r"\b(Finset|Fintype|Multiset|Finite|Nat\.choose|ncard|encard|powerset)\b|\.card\b"
)
_PROFILE_STATEMENT_HYPOTHESIS_RE = re.compile(r"→|->|=>|<-")


# Learning families are broader than prompt-routing domains and may preserve
# bounded mixed-domain structure for higher-level clustering.
_LEARNING_DOMAIN_PATTERNS: List[Tuple[str, re.Pattern[str]]] = [
    (
        "probability",
        re.compile(
            r"\b("
            r"ProbabilityTheory|RandomVariable|IdentDistrib|Indep(?:Fun|Set|Sets)?|"
            r"CondDistrib|condexp|expectation|variance|stdDev"
            r")\b"
        ),
    ),
    (
        "measure_theory",
        re.compile(
            r"\b("
            r"MeasureTheory|Measurable(?:Set)?|AEMeasurable|AEStronglyMeasurable|"
            r"NullMeasurableSet|OuterMeasure|lintegral|ENNReal|snorm|ae_[A-Za-z_']*"
            r")\b"
        ),
    ),
    (
        "topology",
        re.compile(
            r"\b("
            r"Metric\.|TopologicalSpace|IsOpen|IsClosed|IsCompact|Connected|Homeomorph|"
            r"Dense|Closure|Interior|Frontier|LocallyCompact|Continuous(?:On)?|nhds"
            r")\b"
        ),
    ),
    (
        "geometry",
        re.compile(
            r"\b("
            r"EuclideanGeometry|Affine(?:Subspace)?|Collinear|convexHull|Simplex|"
            r"Orthogonal|NormedAddTorsor|InnerProductGeometry|midpoint|angle"
            r")\b"
            r"|\bdist\b(?!\s*[:=])"
        ),
    ),
    (
        "linear_algebra",
        re.compile(
            r"\b("
            r"Matrix|LinearMap|Submodule|Basis|LinearIndependent|Module|"
            r"eigenspace|eigenvector"
            r")\b"
            r"|\.rank\b|\b(?:span|rank|det)\b(?!\s*[:=])"
        ),
    ),
    (
        "number_theory",
        re.compile(
            r"\b("
            r"Prime|Nat\.prime|Nat\.(?:gcd|lcm|coprime)|Int\.(?:gcd|lcm|emod|ediv)|"
            r"ZMod|ModEq|QuadraticResidue|dvd"
            r")\b"
        ),
    ),
    (
        "combinatorics",
        re.compile(
            r"\b("
            r"Finset|Fintype|Multiset|Nat\.choose|ncard|encard|powerset|Pairwise|Perm"
            r")\b|\.card\b"
        ),
    ),
    (
        "algebra",
        re.compile(
            r"\b("
            r"Polynomial|Ring(?:Hom|Equiv)?|Field|Ideal|algebraMap|Semiring|CommRing|"
            r"Monoid(?:Hom)?|Group(?:Hom)?|IsLocalization"
            r")\b"
        ),
    ),
    (
        "analysis",
        re.compile(
            r"\b("
            r"Real|Complex|Filter|Tendsto|atTop|atBot|Differentiable|ContDiff|"
            r"HasDeriv(?:At|WithinAt)?|integral|summable|Cauchy|"
            r"ConvexOn|StrictConvexOn|ConcaveOn|StrictConcaveOn|"
            r"Monotone(?:On)?|Antitone(?:On)?|StrictMono|StrictAnti"
            r")\b"
            r"|[∫∑∏]"  # Unicode math operators used in Lean 4 printed forms
        ),
    ),
]

_LEARNING_DOMAIN_SUBSUMPTIONS: dict[str, tuple[str, ...]] = {
    "probability": ("measure_theory", "analysis"),
    "measure_theory": ("analysis",),
}


def classify_domain(statement: str) -> str:
    """Classify a Lean statement into a mathematical domain."""
    statement_text = _mask_declared_binder_names(statement).strip()
    if not statement_text:
        return "general"
    for pattern, domain in _DOMAIN_PATTERNS:
        if re.search(pattern, statement_text):
            return domain
    return "general"


def normalize_problem_domain(domain: str) -> str:
    """Return a canonical memory-scoping domain tag."""
    text = str(domain or "").strip().lower()
    if not text or text == "general":
        return ""
    return text


def memory_scope_domain_for_profile(profile: ProblemProfile) -> str:
    """Return the best available memory-scope tag for a problem profile.

    `statement_domain` is often too coarse and frequently falls back to
    `general`, so prefer the richer learning-family signal when it is known.
    """
    if profile is None:
        return ""
    learning_family = normalize_problem_domain(
        str(getattr(profile, "learning_family", "") or "")
    )
    if learning_family and not learning_family.startswith("mixed_"):
        return learning_family
    for domain in tuple(getattr(profile, "learning_domains", ()) or ()):
        normalized = normalize_problem_domain(str(domain or ""))
        if normalized:
            return normalized
    return normalize_problem_domain(str(getattr(profile, "statement_domain", "") or ""))


def classify_learning_domains(*texts: str) -> List[str]:
    """Return all matched learning domains in canonical order."""
    matched: set[str] = set()
    for text in texts:
        current = _mask_declared_binder_names(text)
        if not current.strip():
            continue
        for domain, pattern in _LEARNING_DOMAIN_PATTERNS:
            if pattern.search(current):
                matched.add(domain)
    if not matched:
        return []

    suppressed = {
        implied
        for domain in matched
        for implied in _LEARNING_DOMAIN_SUBSUMPTIONS.get(domain, ())
    }
    return [
        domain
        for domain, _ in _LEARNING_DOMAIN_PATTERNS
        if domain in matched and domain not in suppressed
    ]


def classify_learning_domain_family(*texts: str, max_domains: int = 2) -> str:
    """Return a stable learning-family tag, preserving bounded mixed domains."""
    domains = classify_learning_domains(*texts)
    if not domains:
        return "general"
    ordered = sorted(domains)
    if len(ordered) == 1:
        return ordered[0]
    head = ordered[: max(2, int(max_domains))]
    suffix = "_plus" if len(ordered) > len(head) else ""
    return f"mixed_{'_'.join(head)}{suffix}"


def _copy_domain_hint(hint: DomainHint) -> DomainHint:
    return DomainHint(
        domain=str(hint.domain),
        primary_tactics=list(hint.primary_tactics),
        useful_lemma_prefixes=list(hint.useful_lemma_prefixes),
        avoidance_note=str(hint.avoidance_note or ""),
    )


def get_oracle_family_order_for_domains(
    domains: Sequence[str],
    *,
    statement_domain: str = "",
) -> Tuple[str, ...]:
    """Return the preferred oracle family ordering for the first known domain."""
    ordered_domains = _ordered_domains_with_statement(
        domains,
        statement_domain=statement_domain,
    )
    for domain in ordered_domains:
        palette = _DOMAIN_TACTIC_PALETTES.get(domain)
        if palette is not None:
            return tuple(palette.oracle_family_order)
    return ()


def get_oracle_domain_specific_tactics(
    domains: Sequence[str],
    *,
    statement_domain: str = "",
    enabled_opt_in_tactics: Sequence[str] = (),
) -> List[str]:
    """Return a de-duplicated oracle-safe domain-specific tactic list."""
    ordered_domains = _ordered_domains_with_statement(
        domains,
        statement_domain=statement_domain,
    )
    groups: List[Sequence[str]] = []
    for domain in ordered_domains:
        palette = _DOMAIN_TACTIC_PALETTES.get(domain)
        if palette is not None:
            groups.append(
                _oracle_domain_specific_tactics_for_palette(
                    palette,
                    enabled_opt_in_tactics=enabled_opt_in_tactics,
                )
            )
    return _dedupe_tactics(*groups)


def get_domain_opt_in_tactics(
    domains: Sequence[str],
    *,
    statement_domain: str = "",
    enabled_opt_in_tactics: Sequence[str] = (),
) -> List[str]:
    """Return enabled domain opt-in tactics without mixing them into oracle-safe rows."""
    ordered_domains = _ordered_domains_with_statement(
        domains,
        statement_domain=statement_domain,
    )
    groups: List[Sequence[str]] = []
    for domain in ordered_domains:
        palette = _DOMAIN_TACTIC_PALETTES.get(domain)
        if palette is not None:
            groups.append(
                _enabled_opt_in_tactics_for_palette(
                    palette,
                    enabled_opt_in_tactics=enabled_opt_in_tactics,
                )
            )
    return _dedupe_tactics(*groups)


def get_domain_hint(
    statement: str,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> DomainHint:
    """Get domain-specific hints for a statement."""
    domain = classify_domain(statement)
    return get_domain_hint_for_name(
        domain,
        enabled_opt_in_tactics=enabled_opt_in_tactics,
    )


def get_domain_hint_for_name(
    domain: str,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> DomainHint:
    """Get domain-specific hints from a canonical domain name."""
    normalized = str(domain or "").strip()
    enabled_flags = [
        str(flag or "").strip()
        for flag in enabled_opt_in_tactics
        if str(flag or "").strip()
    ]
    if not enabled_flags:
        return _copy_domain_hint(_DOMAIN_HINTS.get(normalized, _DEFAULT_HINT))
    palette = _DOMAIN_TACTIC_PALETTES.get(normalized)
    if palette is None:
        return _copy_domain_hint(_DEFAULT_HINT)
    return _compose_domain_hint(palette, enabled_opt_in_tactics=enabled_flags)


def get_domain_hint_for_profile(
    profile: ProblemProfile,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> DomainHint:
    """Get domain-specific hints from a shared problem profile."""
    for domain in profile.learning_domains:
        if domain in _DOMAIN_HINTS:
            return get_domain_hint_for_name(
                domain,
                enabled_opt_in_tactics=enabled_opt_in_tactics,
            )
    if profile.statement_domain in _DOMAIN_HINTS:
        return get_domain_hint_for_name(
            profile.statement_domain,
            enabled_opt_in_tactics=enabled_opt_in_tactics,
        )
    return _copy_domain_hint(_DEFAULT_HINT)


def get_fast_path_safe_tactics_for_profile(
    profile: ProblemProfile,
    *,
    enabled_opt_in_tactics: Sequence[str] = (),
) -> List[str]:
    """Return a tiny deterministic tactic set safe for the pre-LLM fast path."""

    groups: List[Sequence[str]] = []
    # Allow arithmetic tactics when hypotheses contain arithmetic content
    # (e.g. h : n > 0 ⊢ n ≥ 1 should still try omega/linarith).
    # Block only when the goal has logical structure (∀, ∃, →, etc.)
    # that no fast-path tactic can discharge.
    safe_probe_eligible = not profile.has_structure and (
        not profile.has_hypotheses or profile.has_arithmetic
    )
    ordered_domains = _ordered_domains_with_statement(
        profile.learning_domains,
        statement_domain=profile.statement_domain,
    )
    if safe_probe_eligible:
        for domain in ordered_domains:
            palette = _DOMAIN_TACTIC_PALETTES.get(str(domain or "").strip())
            if palette is not None and palette.fast_path_safe_tactics:
                groups.append(palette.fast_path_safe_tactics)
    if not groups:
        if safe_probe_eligible and profile.has_arithmetic:
            groups.append(_DEFAULT_FAST_PATH_SAFE_TACTICS)
    elif safe_probe_eligible and profile.has_arithmetic:
        groups.append(_DEFAULT_FAST_PATH_SAFE_TACTICS)
    if (
        safe_probe_eligible
        and profile.has_finite_objects
        and not profile.has_extensional
        and not profile.has_measure
    ):
        groups.append(("decide",))
    return _dedupe_tactics(*groups)


_PROFILE_SIGNAL_LABELS: Tuple[Tuple[str, str], ...] = (
    ("has_finite_objects", "finite objects"),
    ("has_arithmetic", "arithmetic"),
    ("has_structure", "logical structure"),
    ("has_extensional", "extensional reasoning"),
    ("has_equality", "equality"),
    ("has_negation", "negation"),
    ("has_hypotheses", "hypotheses"),
    ("has_measure", "measure"),
    ("has_probability", "probability"),
)


def _goal_state_hypothesis_fragments(goal_text: str) -> List[str]:
    """Extract hypothesis-like lines that appear before the focused goal."""

    fragments: List[str] = []
    for raw_line in _coerce_text(goal_text).splitlines():
        line = str(raw_line or "").strip()
        if not line:
            continue
        if "⊢" in line or "|-" in line:
            break
        if line.startswith("case "):
            continue
        if ":" in line:
            fragments.append(line)
    return fragments


def render_problem_profile_summary(profile: ProblemProfile) -> str:
    """Render a compact profile summary suitable for prompt guidance."""

    family = str(profile.learning_family or "general")
    domains = [
        str(domain or "").strip()
        for domain in profile.learning_domains
        if str(domain or "").strip()
    ]
    if not domains and str(profile.statement_domain or "").strip():
        domains = [str(profile.statement_domain).strip()]
    signals = [
        label
        for field_name, label in _PROFILE_SIGNAL_LABELS
        if bool(getattr(profile, field_name, False))
    ]
    parts = [f"family={family}"]
    if domains:
        parts.append(f"domains={', '.join(domains[:3])}")
    if signals:
        parts.append(f"signals={', '.join(signals[:5])}")
    return "Problem profile: " + "; ".join(parts)


def build_problem_profile(
    statement: str,
    *,
    goal_text: str | None = None,
    goal_hypotheses: Sequence[str] = (),
) -> ProblemProfile:
    """Build a shared structural profile from statement and goal-state context."""
    statement_text = _coerce_text(statement).strip()
    goal_focus = _coerce_text(goal_text).strip()
    focus = goal_focus or statement_text
    hypothesis_parts = []
    for hypothesis in goal_hypotheses:
        rendered = _coerce_text(hypothesis).strip()
        if rendered:
            hypothesis_parts.append(rendered)
    hypothesis_parts.extend(_goal_state_hypothesis_fragments(goal_focus))
    hypo_text = " ".join(hypothesis_parts)
    text = f"{hypo_text} {focus}".strip() or statement_text
    profile_text = _PROFILE_ASCII_ARROW_RE.sub(" ", text)
    learning_domains = tuple(
        _merge_ordered_domains(
            classify_learning_domains(focus, statement_text),
            classify_learning_domains(hypo_text),
        )
    )
    learning_family = classify_learning_domain_family(focus, statement_text, hypo_text)
    arithmetic_domains = {"number_theory", "algebra"}
    has_arithmetic = bool(
        _PROFILE_ARITH_OPERATOR_RE.search(profile_text)
        or _PROFILE_ARITH_TOKEN_RE.search(profile_text)
        or arithmetic_domains.intersection(learning_domains)
    )
    return ProblemProfile(
        statement_domain=classify_domain(statement_text),
        learning_domains=learning_domains,
        learning_family=learning_family,
        has_hypotheses=bool(
            hypo_text or _PROFILE_STATEMENT_HYPOTHESIS_RE.search(statement_text)
        ),
        has_arithmetic=has_arithmetic,
        has_structure=bool(_PROFILE_STRUCTURE_RE.search(text)),
        has_negation=bool(_PROFILE_NEGATION_RE.search(text)),
        has_extensional=bool(_PROFILE_EXTENSIONAL_RE.search(text)),
        has_equality=bool(_PROFILE_EQUALITY_RE.search(text)),
        has_finite_objects=bool(_PROFILE_FINITE_RE.search(text)),
        has_measure=(
            "measure_theory" in learning_domains or "probability" in learning_domains
        ),
        has_probability=("probability" in learning_domains),
    )


# ---- strategy-tag -> tactic mapping for enrichment ----------------------

_STRATEGY_TO_TACTICS: dict[str, List[str]] = {
    "search": _dedupe_tactics(_SHARED_CORE_TACTICS["search"], ("decide",)),
    "intro": ["intro", "intros", "rintro"],
    "simp": ["simp", "simpa", "simp_all"],
    "omega": ["omega", "norm_num", "norm_cast", "zify", "interval_cases", "mod_cases"],
    "ring": [
        "ring",
        "ring_nf",
        "field_simp",
        "abel",
        "group",
        "noncomm_ring",
        "linear_combination",
    ],
    "linarith": ["linarith", "nlinarith", "positivity", "gcongr"],
    "aesop": ["aesop", "solve_by_elim"],
    "simp_chain": ["simp", "simp_all", "simp_rw"],
    "rewrite": ["rw", "rewrite", "simp_rw", "conv", "nth_rewrite", "change", "convert"],
    "ext": ["ext", "funext", "congr"],
    "strong_induction": [
        "strong_induction",
        "induction",
        "interval_cases",
        "fin_cases",
    ],
    "induction": ["induction", "strong_induction", "interval_cases", "fin_cases"],
    "cases": ["cases", "rcases", "obtain", "match", "by_cases", "choose", "fin_cases"],
    "push_neg": ["push_neg", "contrapose", "by_contra", "exfalso"],
    "by_contra": _dedupe_tactics(_SHARED_CORE_TACTICS["negation"], ("exfalso",)),
    "calc": ["calc", "change", "convert"],
    "apply": ["apply", "exact", "refine", "have"],
    "constructor": ["constructor", "left", "right"],
    "composition": ["have", "refine", "calc", "apply", "change", "convert"],
    "decomposition": [
        "cases",
        "rcases",
        "obtain",
        "by_cases",
        "by_contra",
        "contrapose",
    ],
    "other": ["solve_by_elim", "simp", "apply"],
}

_ENRICHMENT_RUNTIME_ALIASES: dict[str, str] = {
    "fast_path": "search",
    "fast_path_guard": "search",
    "oracle_goal": "search",
    "oracle_goal_start": "search",
    "oracle_repair": "search",
    "tactic_level": "search",
    "tactic_tree": "search",
    "sorry_decomp": "decomposition",
    "sorry_decomp_triage": "decomposition",
}


def _enrichment_tactics_for_tag(tag: str) -> List[str]:
    """Return only real tactic suggestions for an observed strategy tag."""
    normalized = str(tag or "").strip().lower()
    if normalized.startswith("failed_strategy:"):
        normalized = normalized.split(":", 1)[1].strip()
    normalized = _ENRICHMENT_RUNTIME_ALIASES.get(normalized, normalized)
    if normalized.startswith("heuristic."):
        normalized = normalized.split(".", 1)[1]

    if normalized in _STRATEGY_TO_TACTICS:
        return list(_STRATEGY_TO_TACTICS[normalized])

    domain_hint = get_domain_hint_for_name(normalized)
    if domain_hint.domain != "general":
        return list(domain_hint.primary_tactics)
    return []


def enrich_domain_hint(
    hint: DomainHint,
    strategy_outcomes: dict[str, list[int]],
) -> DomainHint:
    """Augment a static DomainHint with learned strategy outcome data.

    Promotes tactics that have succeeded on the current problem and
    demotes those that have consistently failed.  Returns a new
    DomainHint with reordered ``primary_tactics`` and an updated
    ``avoidance_note``.

    ``strategy_outcomes`` is ``ensemble._strategy_outcomes`` — a dict
    mapping strategy tags to lists of 1/0 outcomes.
    """
    if not strategy_outcomes:
        return hint

    # Compute success rate per strategy
    rates: dict[str, tuple[float, int]] = {}
    for tag, outcomes in strategy_outcomes.items():
        if outcomes:
            rate = sum(outcomes) / len(outcomes)
            rates[tag] = (rate, len(outcomes))

    if not rates:
        return hint

    # Identify tactics to promote (high success) and demote (low success)
    promote_tactics: List[str] = []
    demote_tactics: List[str] = []
    for tag, (rate, count) in rates.items():
        if count < 2:
            continue  # not enough data
        tactics = _enrichment_tactics_for_tag(tag)
        if not tactics:
            continue
        if rate >= 0.5:
            promote_tactics.extend(tactics)
        elif rate == 0.0:
            demote_tactics.extend(tactics)

    ordered_promote = _dedupe_tactics(promote_tactics)
    promote_set = set(ordered_promote)
    ordered_demote = [
        tactic
        for tactic in _dedupe_tactics(demote_tactics)
        if tactic not in promote_set
    ]
    demote_set = set(ordered_demote)

    # Reorder primary_tactics: promoted first, then original order, demoted last
    promoted = [t for t in hint.primary_tactics if t in promote_set]
    middle = [
        t for t in hint.primary_tactics if t not in promote_set and t not in demote_set
    ]
    demoted = [t for t in hint.primary_tactics if t in demote_set]
    # Add promoted tactics not already in original list
    for t in ordered_promote:
        if t not in hint.primary_tactics and t not in promoted:
            promoted.append(t)

    new_tactics = _dedupe_tactics(promoted, middle, demoted)

    # Build avoidance note
    notes = [hint.avoidance_note] if hint.avoidance_note else []
    if ordered_demote:
        notes.append(
            f"Tactics that failed on this problem: {', '.join(ordered_demote)}"
        )
    if ordered_promote:
        notes.append(
            f"Tactics that worked on this problem: {', '.join(ordered_promote)}"
        )

    return DomainHint(
        domain=hint.domain,
        primary_tactics=new_tactics if new_tactics else hint.primary_tactics,
        useful_lemma_prefixes=list(hint.useful_lemma_prefixes),
        avoidance_note=" | ".join(notes),
    )
