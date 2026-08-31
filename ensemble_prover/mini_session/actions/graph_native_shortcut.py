"""Deterministic shortcuts for graph-native proposal work."""

from __future__ import annotations

import time
from typing import Any, ClassVar, Dict, FrozenSet, Optional

from ensemble_prover.proof_graph import (
    _graph_statement_is_context_bare_prop_atom,
    graph_statement_is_executable,
    graph_node_frontier_promoted_to_proof_state,
    graph_node_frontier_quarantined,
)

from ..action import MiniOutcome


_FORMAL_PARENT_CONTEXT_KEYS = {
    "materialization_parent_statement",
    "formalization_bridge_parent_statement",
    "parent_repair_target_statement",
    "parent_statement",
    "parent_goal_statement",
}


class GraphNativeShortcutAction:
    """Resolve graph-native work that already has enough durable evidence."""

    id: str = "graph_native_shortcut"
    priority: int = 13
    cost_estimate_s: float = 1.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier"})
    WORK_TYPES: ClassVar[FrozenSet[str]] = frozenset(
        {
            "formalize_claim",
            "prove_claim_variant",
            "mine_missing_obligation",
            "route_replan",
        }
    )

    @staticmethod
    def _selected_item(session: Any) -> Any:
        getter = getattr(session, "selected_work_item_for", None)
        if not callable(getter):
            return None
        return getter(
            GraphNativeShortcutAction.id,
            work_types=tuple(sorted(GraphNativeShortcutAction.WORK_TYPES)),
        )

    @staticmethod
    def _field(item: Any, key: str, default: Any = "") -> Any:
        if isinstance(item, dict):
            return item.get(key, default)
        return getattr(item, key, default)

    @staticmethod
    def _work_type(item: Any) -> str:
        return str(GraphNativeShortcutAction._field(item, "work_type", "") or "").strip()

    @staticmethod
    def _graph_record(item: Any) -> dict[str, Any]:
        if isinstance(item, dict):
            return dict(item)
        record = getattr(item, "graph_record", None)
        return dict(record) if isinstance(record, dict) else {}

    @staticmethod
    def _selected_work_record(session: Any) -> dict[str, Any]:
        record = getattr(session, "selected_work_item_record", None)
        return dict(record) if isinstance(record, dict) else {}

    @classmethod
    def _node_id_for_item(cls, item: Any) -> str:
        record = cls._graph_record(item)
        work_type = cls._work_type(item)
        field_by_work_type = {
            "formalize_claim": "claim_id",
            "prove_claim_variant": "variant_id",
            "mine_missing_obligation": "obligation_id",
            "route_replan": "replan_id",
        }
        field = field_by_work_type.get(work_type, "")
        if field:
            node_id = str(record.get(field) or "").strip()
            if node_id:
                return node_id
        return str(cls._field(item, "node_id", "") or "").strip()

    @staticmethod
    def _graph(session: Any) -> Any:
        return getattr(getattr(session, "dossier", None), "proof_graph", None)

    @staticmethod
    def _answer_safety_kwargs(session: Any = None) -> Dict[str, bool]:
        conv = getattr(session, "conv", None)
        return {
            "suppress_solution_placeholders": bool(
                getattr(conv, "suppress_solution_placeholders", True)
            ),
            "opaque_mode": bool(getattr(conv, "opaque_mode", True)),
            "allow_official_answer_visibility": bool(
                getattr(conv, "allow_official_answer_visibility", False)
            ),
            "official_answer_payload_present": getattr(
                conv,
                "official_answer_payload_present",
                getattr(
                    getattr(session, "dossier", None),
                    "official_answer_payload_present",
                    None,
                ),
            ),
        }

    @classmethod
    def _statement_answer_unsafe(cls, statement: str, session: Any = None) -> bool:
        try:
            from ensemble_prover.proof_dossier import is_answer_unsafe_statement_text
        except Exception:
            return False
        return bool(
            is_answer_unsafe_statement_text(
                statement,
                **cls._answer_safety_kwargs(session),
            )
        )

    @classmethod
    def _node_answer_unsafe(cls, node: Any, session: Any = None) -> bool:
        return cls._statement_answer_unsafe(
            str(getattr(node, "statement", "") or ""),
            session,
        )

    @staticmethod
    def _helper_match(
        graph: Any,
        node: Any,
        *,
        require_replayable_source: bool = False,
    ) -> Optional[Any]:
        matcher = getattr(graph, "_proved_helper_for_statement", None)
        if not callable(matcher) or node is None:
            return None
        return matcher(
            str(getattr(node, "statement", "") or ""),
            require_replayable_source=require_replayable_source,
        )

    @staticmethod
    def _looks_like_formal_statement(statement: str, informal_statement: str) -> bool:
        text = " ".join(str(statement or "").split()).strip()
        informal = " ".join(str(informal_statement or "").split()).strip()
        if not text or (informal and text == informal):
            return False
        if text.lower().startswith(("for ", "find ", "show ", "prove ")):
            return False
        formal_markers = (
            "∀",
            "∃",
            "→",
            "↔",
            ":",
            "Prop",
            "Nat",
            "ℕ",
            "Int",
            "ℤ",
            "Real",
            "Set.",
            "∈",
            "≤",
            "≥",
            "=",
            "True",
            "False",
        )
        return any(marker in text for marker in formal_markers)

    @classmethod
    def _matching_variant_exists(cls, graph: Any, claim_id: str, statement: str) -> bool:
        from ensemble_prover.proof_graph import graph_statement_key

        target_key = graph_statement_key(statement)
        if not target_key:
            return False
        for edge in graph.outgoing(claim_id, kind="claim_formalized_as"):
            variant = graph.nodes.get(edge.target)
            if variant is None or getattr(variant, "kind", "") != "formal_variant":
                continue
            if graph.is_superseded_tombstone(variant):
                continue
            if graph_statement_key(getattr(variant, "statement", "")) == target_key:
                return True
        return False

    @staticmethod
    def _context_parent_statement(*records: Dict[str, Any]) -> str:
        for record in records:
            if not isinstance(record, dict):
                continue
            for key in (
                "materialization_parent_statement",
                "formalization_bridge_parent_statement",
                "parent_repair_target_statement",
                "parent_statement",
                "parent_goal_statement",
            ):
                value = str(record.get(key) or "").strip()
                if value:
                    return value
        return ""

    @classmethod
    def _can_formalize_claim(
        cls,
        graph: Any,
        claim: Any,
        session: Any = None,
        work_item: Any = None,
    ) -> bool:
        if claim is None or getattr(claim, "kind", "") != "proposed_claim":
            return False
        if getattr(claim, "status", "") != "open" or graph.is_superseded_tombstone(claim):
            return False
        statement = str(getattr(claim, "statement", "") or "").strip()
        if cls._statement_answer_unsafe(statement, session):
            return False
        metadata = getattr(claim, "metadata", None) or {}
        informal = str(metadata.get("informal_statement") or "").strip()
        root_statement = str(
            getattr(getattr(session, "dossier", None), "root_statement", "") or ""
        )
        graph_record = cls._graph_record(work_item)
        selected_record = cls._selected_work_record(session)
        parent_statement = cls._context_parent_statement(
            graph_record,
            selected_record,
            metadata,
        )
        context_bare_prop_atom = _graph_statement_is_context_bare_prop_atom(
            statement,
            parent_statement=parent_statement,
            root_statement=root_statement,
            metadata=metadata,
        )
        if (
            not cls._looks_like_formal_statement(statement, informal)
            and not context_bare_prop_atom
        ):
            return False
        if not graph_statement_is_executable(
            statement
        ) and not context_bare_prop_atom:
            return False
        return not cls._matching_variant_exists(graph, claim.node_id, statement)

    @staticmethod
    def _replan_obligation_id(graph: Any, replan: Any) -> str:
        metadata = getattr(replan, "metadata", None) or {}
        obligation_id = str(
            metadata.get("obligation_id")
            or metadata.get("resolved_by_obligation_id")
            or ""
        ).strip()
        if obligation_id:
            return obligation_id
        for edge in graph.incoming(getattr(replan, "node_id", ""), kind="obligation_replan"):
            return str(edge.source or "").strip()
        return ""

    @classmethod
    def _can_resolve_replan(cls, graph: Any, replan: Any) -> bool:
        if replan is None or getattr(replan, "kind", "") != "replan_queue_item":
            return False
        if getattr(replan, "status", "") == "proved":
            return False
        if cls._frontier_suppressed(graph, replan, "route_replan"):
            return False
        obligation = graph.nodes.get(cls._replan_obligation_id(graph, replan))
        proved = getattr(graph, "_proved_node_has_durable_certificate", None)
        return bool(callable(proved) and proved(obligation))

    @classmethod
    def _frontier_suppressed(cls, graph: Any, node: Any, work_type: str) -> bool:
        if graph_node_frontier_quarantined(node):
            return True
        if graph_node_frontier_promoted_to_proof_state(node):
            return True
        if work_type != "route_replan":
            return False
        replan_quarantined = getattr(
            graph,
            "replan_queue_item_frontier_quarantined",
            None,
        )
        if callable(replan_quarantined) and replan_quarantined(node):
            return True
        replan_promoted = getattr(
            graph,
            "replan_queue_item_frontier_promoted_to_proof_state",
            None,
        )
        if callable(replan_promoted) and replan_promoted(node):
            return True
        obligation = graph.nodes.get(cls._replan_obligation_id(graph, node))
        if obligation is None:
            return False
        return bool(
            graph_node_frontier_quarantined(obligation)
            or graph_node_frontier_promoted_to_proof_state(obligation)
        )

    @classmethod
    def _can_progress(cls, session: Any) -> bool:
        graph = cls._graph(session)
        item = cls._selected_item(session)
        if graph is None or item is None:
            return False
        work_type = cls._work_type(item)
        if work_type not in cls.WORK_TYPES:
            return False
        node = graph.nodes.get(cls._node_id_for_item(item))
        if node is None or graph.is_superseded_tombstone(node):
            return False
        if cls._frontier_suppressed(graph, node, work_type):
            return False
        if cls._node_answer_unsafe(node, session):
            return False
        if (
            work_type
            in {"formalize_claim", "prove_claim_variant", "mine_missing_obligation"}
            and cls._helper_match(
                graph,
                node,
                require_replayable_source=work_type == "mine_missing_obligation",
            )
            is not None
        ):
            return True
        if work_type == "formalize_claim":
            return cls._can_formalize_claim(graph, node, session, item)
        if work_type == "route_replan":
            return cls._can_resolve_replan(graph, node)
        return False

    def is_applicable(self, session: Any) -> bool:
        return self._can_progress(session)

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Graph-native applicability is observational by construction."""

        return self._can_progress(session)

    async def run(self, session: Any) -> MiniOutcome:
        started = time.monotonic()
        graph = self._graph(session)
        item = self._selected_item(session)
        if graph is None or item is None:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={"verdict": "missing_graph_work"},
            )

        work_type = self._work_type(item)
        node_id = self._node_id_for_item(item)
        node = graph.nodes.get(node_id)
        if node is not None and self._node_answer_unsafe(node, session):
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "answer_unsafe_skipped",
                    "work_type": work_type,
                    "node_id": node_id,
                },
            )
        before_status = str(getattr(node, "status", "") or "")
        before_proof_hash = str(getattr(node, "proof_hash", "") or "")
        progress_reasons: list[str] = []

        resolver = getattr(graph, "resolve_existing_proved_helper_matches", None)
        if callable(resolver):
            resolver()
        node = graph.nodes.get(node_id)
        if (
            node is not None
            and getattr(node, "status", "") == "proved"
            and (before_status != "proved" or not before_proof_hash)
        ):
            progress_reasons.append("matched_existing_helper")

        if work_type == "formalize_claim" and self._can_formalize_claim(
            graph,
            node,
            session,
            item,
        ):
            statement = str(getattr(node, "statement", "") or "").strip()
            node_metadata = dict(getattr(node, "metadata", {}) or {})
            selected_record = self._selected_work_record(session)
            graph_record = self._graph_record(item)
            parent_statement = self._context_parent_statement(
                graph_record,
                selected_record,
                node_metadata,
            )
            variant_metadata = {
                "formalized_by_action": self.id,
                **{
                    key: value
                    for source in (graph_record, selected_record, node_metadata)
                    for key, value in source.items()
                    if key in (_FORMAL_PARENT_CONTEXT_KEYS | {"informal_statement"})
                    and str(value or "").strip()
                },
            }
            if parent_statement:
                variant_metadata.setdefault(
                    "formalization_bridge_parent_statement",
                    parent_statement,
                )
                variant_metadata.setdefault(
                    "parent_repair_target_statement",
                    parent_statement,
                )
            variant_metadata.update(
                session.dossier.statement_environment_metadata()
            )
            variant = graph.record_formal_variant(
                claim_node_id=node.node_id,
                claim_name=str(getattr(node, "name", "") or ""),
                statement=statement,
                variant_name=str(getattr(node, "name", "") or "formal"),
                source=self.id,
                phase=self.id,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                variant_key=statement,
                metadata=variant_metadata,
            )
            progress_reasons.append(f"created_formal_variant:{variant.node_id}")
            if callable(resolver):
                resolver()

        if work_type == "route_replan":
            node = graph.nodes.get(node_id)
            if self._can_resolve_replan(graph, node):
                resolver_fn = getattr(graph, "_resolve_replan_if_obligation_proved", None)
                if callable(resolver_fn):
                    resolver_fn(node, self._replan_obligation_id(graph, node))
                refreshed = graph.nodes.get(node_id)
                if refreshed is not None and getattr(refreshed, "status", "") == "proved":
                    progress_reasons.append("resolved_replan_from_proved_obligation")

        progress = bool(progress_reasons)
        parent_progress_reasons = [
            reason
            for reason in progress_reasons
            if reason
            in {
                "matched_existing_helper",
                "resolved_replan_from_proved_obligation",
            }
        ]
        parent_progress = bool(parent_progress_reasons)
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=progress,
            cost_seconds=time.monotonic() - started,
            metadata={
                "verdict": "graph_native_shortcut" if progress else "no_shortcut",
                "work_type": work_type,
                "node_id": node_id,
                "progress_reasons": list(dict.fromkeys(progress_reasons)),
                "parent_progress": parent_progress,
                "strong_progress": parent_progress,
                "strong_progress_reason": (
                    "parent_progress" if parent_progress else "none"
                ),
                "selected_work_item": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
            },
        )
