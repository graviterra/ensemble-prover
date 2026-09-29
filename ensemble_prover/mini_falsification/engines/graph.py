"""Deterministic small-graph counterexample generation and replay."""

from __future__ import annotations

import bisect
import itertools
import math
from dataclasses import dataclass, replace
from functools import lru_cache
from typing import Any

import networkx as nx

from ...falsification_cursor_identity import GRAPH_PLAN_CURSOR_SCHEMA
from ...proof_graph import graph_statement_key
from ..engine import FalsificationContext
from ..generators import (
    GraphCarrier,
    binder_domain,
    deterministic_terms,
    graph_term_for_carrier,
    leading_forall_binders,
    resolve_graph_carrier,
)
from ..model import FalsificationFinding, FalsificationOutcome, content_hash
from .common import check_witnesses


_GRAPH_PLAN_SCHEMA = GRAPH_PLAN_CURSOR_SCHEMA
_ATLAS_MAX_ORDER = 7


def _edge_mask(graph: nx.Graph, possible_edges: tuple[tuple[int, int], ...]) -> int:
    edges = {tuple(sorted((int(left), int(right)))) for left, right in graph.edges()}
    return sum(1 << index for index, edge in enumerate(possible_edges) if edge in edges)


@lru_cache(maxsize=None)
def _atlas_representative_masks(order: int) -> tuple[int, ...]:
    """One deterministic labeled representative of every class through order 7."""

    if order < 0 or order > _ATLAS_MAX_ORDER:
        return ()
    possible_edges = tuple(itertools.combinations(range(order), 2))
    masks = {
        _edge_mask(graph, possible_edges)
        for graph in nx.graph_atlas_g()
        if graph.number_of_nodes() == order
    }
    return tuple(sorted(masks))


def _catalog_hash(order: int, representative_masks: tuple[int, ...]) -> str:
    return content_hash(
        {
            "schema": _GRAPH_PLAN_SCHEMA,
            "catalog": "networkx.graph_atlas_g",
            "networkx_version": nx.__version__,
            "order": order,
            "representative_masks": representative_masks,
        }
    )


def _complement_mask_at(
    index: int,
    *,
    graph_count: int,
    excluded_sorted: tuple[int, ...],
) -> int:
    """Select a rank from ``range(graph_count) - excluded`` without scanning."""

    if index < 0 or index >= graph_count - len(excluded_sorted):
        raise IndexError(index)
    target = index + 1
    low, high = 0, graph_count - 1
    while low < high:
        middle = (low + high) // 2
        available = middle + 1 - bisect.bisect_right(excluded_sorted, middle)
        if available >= target:
            high = middle
        else:
            low = middle + 1
    return low


@dataclass(frozen=True)
class GraphSearchPlan:
    carrier: GraphCarrier
    graph_binder_index: int
    binder_types: tuple[str, ...]
    ancillary_domains: tuple[tuple[str, ...], ...]
    possible_edges: tuple[tuple[int, int], ...]
    representative_masks: tuple[int, ...]
    catalog_hash: str
    plan_hash: str

    @property
    def graph_count(self) -> int:
        return 1 << len(self.possible_edges)

    @property
    def ancillary_count(self) -> int:
        if not self.ancillary_domains:
            return 1
        return math.prod(len(domain) for domain in self.ancillary_domains)

    @property
    def total_domain_size(self) -> int:
        return self.graph_count * self.ancillary_count

    @property
    def representative_boundary(self) -> int:
        return len(self.representative_masks) * self.ancillary_count

    def graph_mask_at(self, graph_rank: int) -> int:
        if graph_rank < len(self.representative_masks):
            return self.representative_masks[graph_rank]
        return _complement_mask_at(
            graph_rank - len(self.representative_masks),
            graph_count=self.graph_count,
            excluded_sorted=self.representative_masks,
        )

    def witness_at(self, index: int) -> tuple[str, ...]:
        if index < 0 or index >= self.total_domain_size or self.ancillary_count == 0:
            raise IndexError(index)
        graph_rank, ancillary_rank = divmod(index, self.ancillary_count)
        mask = self.graph_mask_at(graph_rank)
        edges = tuple(
            edge
            for edge_index, edge in enumerate(self.possible_edges)
            if mask & (1 << edge_index)
        )
        ancillary_values: list[str] = [""] * len(self.ancillary_domains)
        remainder = ancillary_rank
        for domain_index in range(len(self.ancillary_domains) - 1, -1, -1):
            domain = self.ancillary_domains[domain_index]
            remainder, term_index = divmod(remainder, len(domain))
            ancillary_values[domain_index] = domain[term_index]
        graph_value = graph_term_for_carrier(self.carrier, edges)
        witness: list[str] = []
        ancillary_index = 0
        for binder_index in range(len(self.binder_types)):
            if binder_index == self.graph_binder_index:
                witness.append(graph_value)
            else:
                witness.append(ancillary_values[ancillary_index])
                ancillary_index += 1
        return tuple(witness)


def _build_graph_plan(
    context: FalsificationContext,
) -> tuple[GraphSearchPlan | None, str]:
    binders, _body = leading_forall_binders(context.statement)
    graph_binders: list[tuple[int, GraphCarrier]] = []
    for index, binder in enumerate(binders):
        carrier = resolve_graph_carrier(binder.type_text, preamble=context.preamble)
        if carrier is not None:
            graph_binders.append((index, carrier))
    if len(graph_binders) != 1:
        return (
            None,
            "requires exactly one visible SimpleGraph over a supported finite carrier",
        )
    graph_index, carrier = graph_binders[0]
    if carrier.order > context.policy.max_graph_vertices:
        return None, "graph order exceeds configured bound"
    ancillary_domains: list[tuple[str, ...]] = []
    for index, binder in enumerate(binders):
        if index == graph_index:
            continue
        domain = binder_domain(binder.type_text)
        if domain not in {"bool", "fin"}:
            return None, "non-graph binders must have explicit finite Bool/Fin domains"
        ancillary_domains.append(deterministic_terms(domain, binder.type_text))
    possible_edges = tuple(itertools.combinations(range(carrier.order), 2))
    representatives = _atlas_representative_masks(carrier.order)
    catalog_hash = _catalog_hash(carrier.order, representatives)
    plan_payload = {
        "schema": _GRAPH_PLAN_SCHEMA,
        # Use the exact canonical identity that keys dossier cursor memory.
        # Raw surface whitespace previously changed plan_hash while resolving
        # to the same dossier key/environment, pinning the old incompatible
        # cursor and restarting graph enumeration at zero forever.
        "statement": graph_statement_key(context.statement),
        "preamble_hash": content_hash(context.preamble),
        "carrier": {
            "vertex_type": carrier.vertex_type,
            "vertex_terms": carrier.vertex_terms,
            "order": carrier.order,
            "source": carrier.source,
        },
        "graph_binder_index": graph_index,
        "binder_types": tuple(binder.type_text for binder in binders),
        "ancillary_domains": tuple(ancillary_domains),
        "possible_edges": possible_edges,
        "catalog_hash": catalog_hash,
    }
    return (
        GraphSearchPlan(
            carrier=carrier,
            graph_binder_index=graph_index,
            binder_types=tuple(binder.type_text for binder in binders),
            ancillary_domains=tuple(ancillary_domains),
            possible_edges=possible_edges,
            representative_masks=representatives,
            catalog_hash=catalog_hash,
            plan_hash=content_hash(plan_payload),
        ),
        "",
    )


def _compatible_cursor_start(
    context: FalsificationContext, plan: GraphSearchPlan
) -> int:
    cursor = context.cursor
    if not cursor:
        return 0
    if (
        cursor.get("cursor_schema") != _GRAPH_PLAN_SCHEMA
        or cursor.get("plan_hash") != plan.plan_hash
        or cursor.get("catalog_hash") != plan.catalog_hash
        or cursor.get("domain_size") != plan.total_domain_size
    ):
        return 0
    raw_index = cursor.get("next_index")
    if not isinstance(raw_index, int) or isinstance(raw_index, bool):
        return 0
    index = raw_index
    return index if 0 <= index <= plan.total_domain_size else 0


def _phase_for_cursor(plan: GraphSearchPlan, next_index: int) -> str:
    if next_index >= plan.total_domain_size:
        return "exhausted"
    if next_index < plan.representative_boundary:
        return "unlabeled_probe"
    return "labeled_complete"


class GraphEnumerationEngine:
    name = "graph"

    async def search(
        self, context: FalsificationContext, lean: Any
    ) -> FalsificationFinding:
        plan, unsupported_reason = _build_graph_plan(context)
        if plan is None:
            outcome = (
                FalsificationOutcome.INCONCLUSIVE
                if unsupported_reason == "graph order exceeds configured bound"
                else FalsificationOutcome.UNSUPPORTED
            )
            return FalsificationFinding(self.name, outcome, unsupported_reason)
        start = _compatible_cursor_start(context, plan)
        limit = min(
            context.policy.max_finite_checks,
            context.policy.max_candidates_per_engine,
        )
        stop = min(plan.total_domain_size, start + limit)
        witnesses = tuple(plan.witness_at(index) for index in range(start, stop))
        observation_pairs = tuple(
            (
                plan.carrier.vertex_terms[left],
                plan.carrier.vertex_terms[right],
            )
            for left, right in plan.possible_edges
        )
        graph_observation_tactics = tuple(
            "dsimp; intro h; have hbad := congrArg "
            f"(fun G : SimpleGraph ({plan.carrier.vertex_type}) => "
            f"G.Adj {left} {right}) h; simp at hbad"
            for left, right in observation_pairs
        )
        sanitized_context = replace(context, cursor={"next_index": start})
        # Full plan identity for TRANSIENT cursor publications too: the
        # progress sink's cursor survives a watchdog cancellation, and
        # without these fields _compatible_cursor_start rejects it (restart
        # at zero) while the dossier merge pins the schema-less cursor.
        plan_identity_extras = {
            "cursor_schema": _GRAPH_PLAN_SCHEMA,
            "plan_hash": plan.plan_hash,
            "catalog_hash": plan.catalog_hash,
            "domain_size": plan.total_domain_size,
            "representative_boundary": plan.representative_boundary,
            "representative_graph_count": len(plan.representative_masks),
            "labeled_graph_count": plan.graph_count,
        }
        finding = await check_witnesses(
            engine=self.name,
            context=sanitized_context,
            lean=lean,
            witnesses=witnesses,
            complete_domain=True,
            total_domain_size=plan.total_domain_size,
            transient_cursor_extras=plan_identity_extras,
            explanation=(
                "isomorphism-diverse graph probing followed by complete labeled "
                "finite graph enumeration replayed in Lean"
            ),
            cursor_window=True,
            extra_tactics_by_witness=tuple(
                graph_observation_tactics for _ in witnesses
            ),
        )
        if finding.candidates:
            candidate = replace(
                finding.candidates[0],
                metadata={
                    **dict(finding.candidates[0].metadata),
                    "graph_vertex_type": plan.carrier.vertex_type,
                    "graph_observation_pairs": observation_pairs,
                },
            )
            finding = replace(finding, candidates=(candidate,))
        cursor = dict(finding.cursor)
        next_index = max(
            0, min(plan.total_domain_size, int(cursor.get("next_index") or 0))
        )
        cursor.update(
            {
                "cursor_schema": _GRAPH_PLAN_SCHEMA,
                "plan_hash": plan.plan_hash,
                "catalog_hash": plan.catalog_hash,
                "domain_size": plan.total_domain_size,
                "phase": _phase_for_cursor(plan, next_index),
                "representative_boundary": plan.representative_boundary,
                "representative_graph_count": len(plan.representative_masks),
                "labeled_graph_count": plan.graph_count,
            }
        )
        return replace(finding, cursor=cursor)
