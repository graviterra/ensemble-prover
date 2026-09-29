"""Typed, deterministic planning for one falsification service quantum.

The engine registry describes what is installed.  This module describes what
is applicable to one statement and prevents overlapping witness generators
from each claiming a full watchdog in the same service call.  It is only a
search scheduler: every candidate still crosses the shared full-negation and
axiom-audit authority boundary.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Mapping, Sequence

from ..falsification_cursor_identity import (
    right_pi_recipe_repair_disposition_is_valid,
)
from .engine import FalsificationEngine
from .generators import (
    binder_domain,
    function_binder_domain,
    leading_forall_binders,
    resolve_graph_carrier,
    surface_right_pi_slots,
)


@dataclass(frozen=True)
class FalsificationLane:
    engine: FalsificationEngine
    family: str
    expensive: bool
    priority: int
    applicability: str
    rotating: bool = False
    fallback_for: str = ""
    scheduler_quanta: int = 0


def _cursor_quanta(cursor: Mapping[str, Any] | None) -> int:
    value = dict(cursor or {}).get("lane_quanta", 0)
    if not isinstance(value, int) or isinstance(value, bool):
        return 0
    # Python integers are unbounded and the enclosing report is size-bounded.
    # Do not introduce a rollover value: a saturated/reset counter can itself
    # permanently prefer one lane.  Family normalization below heals hostile
    # relative skew before the value is used or written again.
    return value if value >= 0 else 0


def _family_scheduler_quanta(
    lanes: Sequence[FalsificationLane],
    cursors: Mapping[str, Mapping[str, Any]],
) -> dict[str, int]:
    """Return fair, self-healing per-family scheduler counters.

    A healthy minimum-count scheduler can only put an available lane one turn
    ahead of the family minimum.  Larger relative skew is untrusted pacing
    state, not coverage, so collapse it to the family minimum.  The selected
    lane then persists ``minimum + 1``, repairing the poison in one quantum
    without altering any mathematical witness index.
    """

    raw = {
        lane.engine.name: _cursor_quanta(cursors.get(lane.engine.name))
        for lane in lanes
    }
    if not raw:
        return {}
    family_minimum = min(raw.values())
    return {
        name: value if value <= family_minimum + 1 else family_minimum
        for name, value in raw.items()
    }


def _cursor_has_exhausted_recipe(cursor: Mapping[str, Any] | None) -> bool:
    record = dict(cursor or {})
    disposition = record.get("recipe_repair_disposition")
    return bool(
        isinstance(disposition, Mapping)
        and disposition.get("status") == "exhausted"
        and right_pi_recipe_repair_disposition_is_valid(
            disposition,
            cursor=record,
        )
    )


def _cursor_is_exactly_exhausted(cursor: Mapping[str, Any] | None) -> bool:
    """Trust an exhaustion marker only at its typed finite domain end."""

    record = dict(cursor or {})
    next_index = record.get("next_index")
    domain_size = record.get("domain_size")
    return bool(
        isinstance(next_index, int)
        and not isinstance(next_index, bool)
        and isinstance(domain_size, int)
        and not isinstance(domain_size, bool)
        and domain_size >= 0
        and next_index == domain_size
        and (
            record.get("exhausted") is True
            or record.get("phase") == "exhausted"
        )
    )


def _lane_cursor_is_closed(
    lane: FalsificationLane,
    cursor: Mapping[str, Any] | None,
) -> bool:
    record = dict(cursor or {})
    if lane.engine.name == "function" and record.get("cursor_schema"):
        if _cursor_has_exhausted_recipe(record):
            return True
        # Exhaustion is meaningful only for the plan hash recomputed from the
        # live statement. Let the function engine validate every plan-bound
        # cursor; otherwise a legacy, stale, or same-schema foreign plan could
        # suppress newly available coverage before validation runs.
        return False
    if _cursor_is_exactly_exhausted(record):
        return True
    if _cursor_has_exhausted_recipe(record):
        return True
    # Native SMT has one plan-bound query. Other engines must publish an
    # explicit exhausted disposition: trusting a bare index/domain pair here
    # would let a stale or poisoned domain identity suppress the engine before
    # its own fail-closed cursor validator can heal it.
    next_index = record.get("next_index")
    return bool(
        lane.engine.name == "sat_smt"
        and isinstance(record.get("plan_hash"), str)
        and isinstance(next_index, int)
        and not isinstance(next_index, bool)
        and next_index >= 1
    )


def _lane_for_engine(
    engine: FalsificationEngine,
    *,
    statement: str,
    preamble: str,
) -> FalsificationLane | None:
    """Conservatively classify an engine without executing it."""

    name = str(getattr(engine, "name", "") or "").strip()
    binders, body = leading_forall_binders(statement)
    domains = tuple(binder_domain(item.type_text) for item in binders)
    surface_slots, _conclusion = surface_right_pi_slots(statement)
    has_surface_data = any(
        slot.kind == "unknown" and binder_domain(slot.type_text) != "prop"
        for slot in surface_slots
    )
    has_surface_proof = any(
        slot.kind == "proof"
        or (slot.kind == "unknown" and binder_domain(slot.type_text) == "prop")
        for slot in surface_slots
    )
    has_function = any(function_binder_domain(item.type_text) for item in binders)
    mixed_right_pi = has_surface_data and has_surface_proof

    if name == "structural":
        return FalsificationLane(engine, "structural", False, 0, "syntax")
    if name == "function":
        if not (surface_slots or has_function):
            return None
        # Interleaved data/proof spines must reach the Lean-sorted right-Pi
        # lane before leading-binder generators erase that structure.
        return FalsificationLane(
            engine,
            "witness",
            True,
            0 if mixed_right_pi else (20 if has_function else 40),
            (
                "mixed_right_pi"
                if mixed_right_pi
                else ("function_binder" if has_function else "right_pi_probe")
            ),
        )
    if name == "finite":
        if not binders or any(
            domain not in {"bool", "fin", "nat", "pnat", "prop"} for domain in domains
        ):
            return None
        return FalsificationLane(engine, "witness", True, 10, "finite_binders")
    if name == "property":
        if not binders or any(
            domain not in {"nat", "pnat", "int"} for domain in domains
        ):
            return None
        return FalsificationLane(engine, "witness", True, 30, "integer_binders")
    if name == "numeric":
        if not binders or any(
            domain not in {"nat", "int", "rat"} for domain in domains
        ):
            return None
        return FalsificationLane(engine, "witness", True, 20, "numeric_binders")
    if name == "exact_algebra":
        if (
            not binders
            or any(
                domain not in {"int", "rat", "real", "complex"} for domain in domains
            )
            or not any(
                token in body
                for token in ("=", "≠", "<", "≤", ">", "≥", "+", "-", "*", "^", "/")
            )
        ):
            return None
        return FalsificationLane(engine, "witness", True, 5, "exact_algebra")
    if name == "graph":
        if not binders or not any(
            resolve_graph_carrier(item.type_text, preamble=preamble) is not None
            for item in binders
        ):
            return None
        return FalsificationLane(engine, "graph", True, 0, "finite_graph")
    if name == "sat_smt":
        # Bool is known-applicable.  Native SMT's translator is deliberately
        # conservative and remains the final applicability check for scalar
        # arithmetic; keep it in its own family so a solver transient cannot
        # suppress the independently Lean-enumerated witness lane.
        if not binders or any(
            domain not in {"bool", "nat", "int", "rat", "real"} for domain in domains
        ):
            return None
        return FalsificationLane(engine, "solver", True, 0, "scalar_smt")

    # Dependency-injected engines are used by integrations/tests.  Preserve
    # their behavior and isolate their budgets rather than guessing overlap.
    if name:
        return FalsificationLane(engine, f"custom:{name}", True, 0, "custom")
    return None


def plan_falsification_lanes(
    engines: Sequence[FalsificationEngine],
    *,
    statement: str,
    preamble: str,
    cursors: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[FalsificationLane, ...]:
    """Select at most one expensive lane per overlapping search family.

    ``lane_quanta`` is persisted inside each ordinary engine cursor.  Sorting
    by it gives deterministic round-robin coverage across calls without a
    second cursor authority or a lossy canonical statement key.
    """

    active_cursors = dict(cursors or {})
    classified = tuple(
        lane
        for engine in engines
        if (
            lane := _lane_for_engine(
                engine,
                statement=statement,
                preamble=preamble,
            )
        )
        is not None
    )
    cheap = [lane for lane in classified if not lane.expensive]
    cheap.extend(
        replace(
            lane,
            family="preserved_evidence",
            expensive=False,
            rotating=False,
        )
        for lane in classified
        if _cursor_has_exhausted_recipe(active_cursors.get(lane.engine.name))
    )
    families: dict[str, list[FalsificationLane]] = {}
    for lane in classified:
        if lane.expensive:
            families.setdefault(lane.family, []).append(lane)
    selected = list(cheap)
    for family in sorted(families):
        lanes = families[family]
        available = [
            lane
            for lane in lanes
            if not _lane_cursor_is_closed(
                lane,
                active_cursors.get(lane.engine.name),
            )
        ]
        if not available:
            continue
        # Mixed right-Pi is not merely a tie-break: while applicable it must
        # flatten the typed outer spine first.  Also plan one invocation-local
        # peer fallback.  The service runs that peer only when the mixed lane
        # is unsupported or transiently fails, so no unauthenticated durable
        # "unavailable" bit can suppress right-Pi search on a later call and
        # one broken generator cannot mask an independent witness lane.
        mixed = [lane for lane in available if lane.applicability == "mixed_right_pi"]
        if mixed:
            preferred = min(mixed, key=lambda lane: (lane.priority, lane.engine.name))
            selected.append(preferred)
            peers = [lane for lane in available if lane not in mixed]
            if peers:
                peer_quanta = _family_scheduler_quanta(peers, active_cursors)
                fallback = min(
                    peers,
                    key=lambda lane: (
                        peer_quanta[lane.engine.name],
                        lane.priority,
                        lane.engine.name,
                    ),
                )
                selected.append(
                    replace(
                        fallback,
                        rotating=len(peers) > 1,
                        fallback_for=preferred.engine.name,
                        scheduler_quanta=peer_quanta[fallback.engine.name],
                    )
                )
            continue
        family_quanta = _family_scheduler_quanta(available, active_cursors)
        chosen = min(
            available,
            key=lambda lane: (
                family_quanta[lane.engine.name],
                lane.priority,
                lane.engine.name,
            ),
        )
        selected.append(
            replace(
                chosen,
                rotating=len(available) > 1,
                scheduler_quanta=family_quanta[chosen.engine.name],
            )
        )
    return tuple(
        sorted(
            selected,
            key=lambda lane: (
                lane.expensive,
                lane.priority,
                lane.engine.name,
            ),
        )
    )


def advance_lane_cursor(
    cursor: Mapping[str, Any] | None,
    *,
    prior_cursor: Mapping[str, Any] | None,
    scheduler_quanta: int | None = None,
) -> dict[str, Any]:
    """Attach a monotone durable scheduler disposition to an engine cursor."""

    advanced = dict(cursor or {})
    if not advanced:
        # A lane that failed before publishing domain progress must still yield
        # to an unrelated peer on the next quantum.  ``next_index=0`` is a
        # valid, fail-closed resume position for all index engines.
        advanced["next_index"] = 0
    prior = (
        scheduler_quanta
        if isinstance(scheduler_quanta, int)
        and not isinstance(scheduler_quanta, bool)
        and scheduler_quanta >= 0
        else _cursor_quanta(prior_cursor)
    )
    advanced["lane_quanta"] = prior + 1
    return advanced
