"""Advisory root-obstruction profiles and native scheduling accounting.

A validated route contract declares intended prerequisites. It does not prove
that they imply the root. These profiles never create proof or budget authority.
"""

from __future__ import annotations

import copy
from dataclasses import fields
from typing import Any, Iterable, Mapping

from ensemble_prover.proof_graph import ProofGraph

EXPLORATION_INTERVAL = 8
_EXPLANATION_LIMIT = 32
# These lanes attempt or investigate mathematics. Administrative materialization,
# verifier replay, acceptance, and root repair do not spend exploration slots.
SPECULATIVE_WORK_TYPES = frozenset(
    {
        "prove_claim_variant",
        "formalize_claim",
        "formalize_missing_obligation",
        "mine_missing_obligation",
        "retrieval",
        "decl_probe",
        "tactic_swarm",
        "formal_state_expand",
        "child_llm_prove",
    }
)
_VALID_CONTRACT_VERDICTS = frozenset(
    {
        "route_assembly_contract_ready",
        "route_assembly_contract_authoring_ready_missing_bridge",
        "route_assembly_contract_incomplete",
    }
)


def _counter(value: Any) -> int:
    return (
        max(0, value) if isinstance(value, int) and not isinstance(value, bool) else 0
    )


def native_exploration_due(state: Any) -> bool:
    return (
        isinstance(state, Mapping)
        and _counter(state.get("services_since_exploration"))
        >= EXPLORATION_INTERVAL - 1
    )


def native_service_state(state: Any, *, exploration: bool) -> dict[str, int]:
    """Return accounting after one actual, budget-consuming non-assembly service."""
    previous = state if isinstance(state, Mapping) else {}
    return {
        "schema_version": 1,
        "services": _counter(previous.get("services")) + 1,
        "exploration_services": _counter(previous.get("exploration_services"))
        + int(exploration),
        "services_since_exploration": 0
        if exploration
        else min(
            EXPLORATION_INTERVAL - 1,
            _counter(previous.get("services_since_exploration")) + 1,
        ),
    }


def root_blocker_profiles(
    graph: Any,
    *,
    route_ids: Iterable[str] | None = None,
) -> dict[str, dict[str, Any]]:
    """Index unresolved declared root requirements without mutating live evidence.

    Route validation may refresh derived node metadata even with mutate=False.
    Isolate dataclass graph state while retaining no copied dossier callbacks.
    Malformed/unavailable contracts simply provide no scheduling bonus.
    """
    if not isinstance(graph, ProofGraph):
        return {}
    try:
        # Do not copy dynamic admission registries or bound owner callbacks.
        # Only graph-owned dataclass state participates in route validation.
        snapshot = object.__new__(ProofGraph)
        for field in fields(graph):
            setattr(snapshot, field.name, copy.deepcopy(getattr(graph, field.name)))
    except (TypeError, ValueError, RecursionError):
        return {}
    ids = (
        sorted(set(route_ids))
        if route_ids is not None
        else sorted(
            node.node_id
            for node in snapshot.nodes.values()
            if node.kind == "strategy_route"
        )
    )
    profiles: dict[str, dict[str, Any]] = {}
    for route_id in ids:
        try:
            status = snapshot.route_assembly_contract_status(route_id, mutate=False)
        except (AttributeError, KeyError, TypeError, ValueError, RecursionError):
            continue
        if (
            status.get("verdict") not in _VALID_CONTRACT_VERDICTS
            or status.get("route_scope") != "root_assembly"
            or status.get("target_node_id") != snapshot.root_node_id
            or status.get("contract_target_node_id") != snapshot.root_node_id
        ):
            continue
        required = set(status.get("required_node_ids") or ())
        unresolved = required.intersection(
            {
                *status.get("missing_node_ids", ()),
                *status.get("unproved_node_ids", ()),
            }
        )
        replay = set(status.get("replay_materialization_node_ids") or ())
        blockers = sorted(unresolved | replay)
        missing_helpers = sorted(set(status.get("missing_helper_names") or ()))
        open_count = len(blockers) + len(missing_helpers)
        # Keep a bounded view of one route, rather than copying N sibling IDs
        # into each of its N blocker profiles. Counts still use the full route.
        explanation = {
            "explanation_route_id": route_id,
            "open_obligation_ids": blockers[:_EXPLANATION_LIMIT],
            "open_obligation_count": len(blockers),
            "missing_helper_names": missing_helpers[:_EXPLANATION_LIMIT],
            "missing_helper_count": len(missing_helpers),
            "explanation_truncated": (
                len(blockers) > _EXPLANATION_LIMIT
                or len(missing_helpers) > _EXPLANATION_LIMIT
            ),
        }
        # An exact requirement on one live route is a useful hypothesis about
        # work value, even though no implication to the root has been checked.
        for node_id in blockers:
            if node_id not in snapshot.nodes:
                continue
            profile = profiles.setdefault(
                node_id,
                {
                    "heuristic_only": True,
                    "evidence": "declared_route_requirement",
                    "root_consumer_ids": [],
                    "shared_route_count": 0,
                    "open_and_siblings": open_count,
                    "completion_bonus": 0.0,
                },
            )
            profile["shared_route_count"] += 1
            if len(profile["root_consumer_ids"]) < _EXPLANATION_LIMIT:
                profile["root_consumer_ids"].append(route_id)
            if (
                "explanation_route_id" not in profile
                or open_count < profile["open_and_siblings"]
            ):
                profile.update(copy.deepcopy(explanation))
            profile["open_and_siblings"] = min(profile["open_and_siblings"], open_count)
            profile["completion_bonus"] = max(
                profile["completion_bonus"], 0.35 + 0.45 / max(1, open_count)
            )
    for profile in profiles.values():
        profile["root_consumers_truncated"] = (
            profile["shared_route_count"] > _EXPLANATION_LIMIT
        )
        # Shared pressure is bounded: copying routes cannot grow it unboundedly.
        profile["completion_bonus"] += min(
            0.15, 0.05 * (profile["shared_route_count"] - 1)
        )
    return profiles
