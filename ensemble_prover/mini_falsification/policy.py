"""Resource and trust policy for falsification runs."""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from numbers import Real

from .model import content_hash

# Single source of truth for the falsification watchdog defaults.  Every
# construction surface (CLI defaults, MiniRecursiveConfig, session-factory
# and prove_problem signatures) must reference these constants: re-stated
# literals silently pinned production at the old 8/30 after the 30/90 bump.
DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S = 30.0
DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S = 90.0
DEFAULT_FALSIFICATION_AGGREGATE_TIMEOUT_S = 90.0
# Instance probes are a cheap filter, not a prover.  Certification still
# uses ``operation_timeout_s``.  A 5s cap is enough for ``norm_num`` /
# ``decide`` / ``omega`` to close an obvious counterexample; hanging
# tactics used to burn the full 30s and then poison the campaign.
DEFAULT_FALSIFICATION_PROBE_TIMEOUT_S = 5.0


def require_falsification_search_bound(value: object, *, field: str) -> int:
    """Validate a search bound without accepting coercible lookalikes."""

    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{field} must be an integer")
    if value < 1:
        raise ValueError(f"{field} must be positive")
    return value


def require_falsification_watchdog(value: object, *, field: str) -> float:
    """Validate a finite positive watchdog before any numeric coercion."""

    if isinstance(value, bool) or not isinstance(value, Real):
        raise ValueError(f"{field} must be numeric")
    try:
        normalized = float(value)
    except (OverflowError, TypeError, ValueError):
        raise ValueError(f"{field} must be finite and positive") from None
    if not math.isfinite(normalized) or normalized <= 0.0:
        raise ValueError(f"{field} must be finite and positive")
    return normalized


@dataclass(frozen=True)
class FalsificationPolicy:
    enabled: bool = True
    engines: tuple[str, ...] = (
        "structural",
        "finite",
        "property",
        "sat_smt",
        "function",
        "exact_algebra",
        "graph",
        "numeric",
    )
    max_candidates_per_engine: int = 32
    max_finite_checks: int = 32
    max_property_examples: int = 128
    # NetworkX's immutable graph atlas gives an exact deterministic
    # isomorphism-representative catalogue through order seven.  Keep the
    # default at that audited boundary; larger orders require an explicitly
    # configured catalogue/generator.
    max_graph_vertices: int = 7
    max_numeric_examples: int = 64
    random_seed: int = 0
    # Execution settings (NOT part of the semantic campaign identity):
    # ``operation_timeout_s`` is the certification/elaboration budget.
    # Instance probes are separately capped at
    # ``DEFAULT_FALSIFICATION_PROBE_TIMEOUT_S`` so a true statement cannot
    # turn one engine into a 90s no-op.
    operation_timeout_s: float = DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S
    engine_timeout_s: float = DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S
    # One service invocation owns one wall-clock quantum.  Engine watchdogs
    # are subordinate limits, not additive entitlements: an overlapping
    # finite/property/numeric portfolio must never turn a 90 second policy
    # into 3 x 90 seconds of caller latency.
    aggregate_timeout_s: float = DEFAULT_FALSIFICATION_AGGREGATE_TIMEOUT_S
    stop_after_authoritative_refutation: bool = True
    require_axiom_audit: bool = True
    allowed_axioms: tuple[str, ...] = (
        "propext",
        "Classical.choice",
        "Quot.sound",
    )

    def __post_init__(self) -> None:
        if not self.require_axiom_audit:
            raise ValueError(
                "durable falsification authority always requires an axiom audit"
            )
        safe_axioms = {"propext", "Classical.choice", "Quot.sound"}
        if not set(self.allowed_axioms).issubset(safe_axioms):
            raise ValueError("allowed_axioms exceeds Mini's trusted axiom allowlist")
        integer_fields = {
            "max_candidates_per_engine": self.max_candidates_per_engine,
            "max_finite_checks": self.max_finite_checks,
            "max_property_examples": self.max_property_examples,
            "max_graph_vertices": self.max_graph_vertices,
            "max_numeric_examples": self.max_numeric_examples,
            "random_seed": self.random_seed,
        }
        for field_name, value in integer_fields.items():
            if field_name == "random_seed":
                if isinstance(value, bool) or not isinstance(value, int):
                    raise ValueError("random_seed must be an integer")
                continue
            require_falsification_search_bound(value, field=field_name)
        for field_name, value in {
            "operation_timeout_s": self.operation_timeout_s,
            "engine_timeout_s": self.engine_timeout_s,
            "aggregate_timeout_s": self.aggregate_timeout_s,
        }.items():
            require_falsification_watchdog(value, field=field_name)

    @property
    def policy_hash(self) -> str:
        # Semantic campaign identity ONLY.  Witnesses are a deterministic
        # function of random_seed and the ABSOLUTE cursor index, so batch
        # sizes and watchdogs change pacing, never what gets checked at
        # index i.  Including them meant every tune changed policy_hash ->
        # environment_hash -> reset ALL prior falsification coverage.
        # (random_seed, engines, max_graph_vertices and the trust settings
        # DO change the checked domain and stay in the hash.)
        data = asdict(self)
        for operational_field in (
            "operation_timeout_s",
            "engine_timeout_s",
            "aggregate_timeout_s",
            "max_candidates_per_engine",
            "max_finite_checks",
            "max_property_examples",
            "max_numeric_examples",
            "stop_after_authoritative_refutation",
        ):
            data.pop(operational_field, None)
        # Axiom authorization is set membership at both policy validation and
        # certificate enforcement. Canonicalize that set so harmless tuple
        # reordering/duplication cannot reset all accumulated coverage.
        data["allowed_axioms"] = sorted(set(self.allowed_axioms))
        return content_hash(data)


def instance_probe_timeout_s(policy: FalsificationPolicy) -> float:
    """Return the cheap instance-check budget, never the certification budget.

    ``operation_timeout_s`` remains the full-negation/axiom-audit window.
    Instance probes that inherit it turn a true statement into a 30s Lean
    hang and then a ``TRANSIENT_FAILURE`` retry. Clip to the probe cap so a
    miss stays a miss.
    """

    return min(
        float(policy.operation_timeout_s),
        DEFAULT_FALSIFICATION_PROBE_TIMEOUT_S,
    )
