"""GraphRouteAssemblyAction — deterministic assembly for ready proof routes."""

from __future__ import annotations

import json
import time
from typing import Any, ClassVar, Dict, FrozenSet, List, Optional, Sequence, Tuple

from ensemble_prover.proof_dossier import helper_decl_name
from ensemble_prover.proof_graph import (
    graph_statement_explicit_arity,
    graph_statement_forall_application_entries,
)
from ensemble_prover.root_finalization import (
    RootFinalizationCandidate,
    root_verification_certificate,
)

from ..action import MiniOutcome
from ..tactic_source_suppression import (
    excluded_tactic_source_prefixes_for_context,
    tactic_source_suppression_records,
)


def _unique_helper_blocks_by_decl(blocks: Sequence[str]) -> List[str]:
    unique: List[str] = []
    seen: set[str] = set()
    for block in list(blocks or ()):
        text = str(block or "").strip()
        if not text:
            continue
        name = str(helper_decl_name(text) or "").strip()
        key = name or text
        if key in seen:
            continue
        seen.add(key)
        unique.append(text)
    return unique


class GraphRouteAssemblyAction:
    id: str = "graph_route_assembly"
    priority: int = 14
    cost_estimate_s: float = 1.0
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"dossier"})

    def __init__(
        self,
        *,
        max_routes: int = 3,
        root_tactic_timeout_s: float = 20.0,
        root_tactic_max_candidates: int = 32,
    ) -> None:
        self.max_routes = int(max_routes or 0)
        self.root_tactic_timeout_s = float(root_tactic_timeout_s or 0.0)
        self.root_tactic_max_candidates = int(root_tactic_max_candidates or 0)

    @staticmethod
    def _selected_item(session: Any) -> Any:
        getter = getattr(session, "selected_work_item_for", None)
        if not callable(getter):
            return None
        return getter(
            GraphRouteAssemblyAction.id,
            work_types=("assemble_route",),
        )

    @staticmethod
    def _route_id_from_item(item: Any) -> str:
        if item is None:
            return ""
        if isinstance(item, dict):
            route_id = str(item.get("route_id") or "").strip()
            if route_id:
                return route_id
            return str(item.get("node_id") or "").strip()
        graph_record = getattr(item, "graph_record", None)
        if isinstance(graph_record, dict):
            route_id = str(graph_record.get("route_id") or "").strip()
            if route_id:
                return route_id
        return str(
            getattr(item, "route_id", "") or getattr(item, "node_id", "") or ""
        ).strip()

    @staticmethod
    def _route_dependencies(graph: Any, route_id: str) -> List[str]:
        deps: List[str] = []
        for edge in graph.outgoing(route_id):
            if edge.kind not in {"route_requires", "route_blocked_by", "route_replan"}:
                continue
            deps.append(edge.target)
        return list(dict.fromkeys(deps))

    @staticmethod
    def _route_helper_names(graph: Any, deps: List[str], dossier: Any) -> List[str]:
        names: List[str] = []
        nodes = getattr(graph, "nodes", {}) or {}
        verified_helpers = getattr(dossier, "verified_helpers", {}) or {}
        for dep_id in deps:
            node = nodes.get(dep_id)
            if node is None:
                continue
            metadata = dict(getattr(node, "metadata", {}) or {})
            candidates = []
            if getattr(node, "kind", "") == "helper":
                candidates.append(str(getattr(node, "name", "") or ""))
            candidates.append(str(metadata.get("verified_by_helper_name") or ""))
            candidates.append(str(metadata.get("resolved_by_helper_name") or ""))
            candidates.append(
                str(metadata.get("formalization_bridge_support_helper_name") or "")
            )
            for support in list(metadata.get("formalization_bridge_supports") or []):
                if not isinstance(support, dict):
                    continue
                candidates.append(str(support.get("helper_name") or ""))
                support_helper_node_id = str(support.get("helper_node_id") or "")
                support_helper_node = nodes.get(support_helper_node_id)
                if (
                    support_helper_node is not None
                    and getattr(support_helper_node, "kind", "") == "helper"
                ):
                    candidates.append(
                        str(getattr(support_helper_node, "name", "") or "")
                    )
            helper_node_id = str(metadata.get("verified_by_helper_node_id") or "")
            helper_node = nodes.get(helper_node_id)
            if helper_node is not None and getattr(helper_node, "kind", "") == "helper":
                candidates.append(str(getattr(helper_node, "name", "") or ""))
            resolved_helper_node_id = str(
                metadata.get("resolved_by_helper_node_id") or ""
            )
            resolved_helper_node = nodes.get(resolved_helper_node_id)
            if (
                resolved_helper_node is not None
                and getattr(resolved_helper_node, "kind", "") == "helper"
            ):
                candidates.append(str(getattr(resolved_helper_node, "name", "") or ""))
            bridge_support_helper_node_id = str(
                metadata.get("formalization_bridge_support_helper_node_id") or ""
            )
            bridge_support_helper_node = nodes.get(bridge_support_helper_node_id)
            if (
                bridge_support_helper_node is not None
                and getattr(bridge_support_helper_node, "kind", "") == "helper"
            ):
                candidates.append(
                    str(getattr(bridge_support_helper_node, "name", "") or "")
                )
            for name in candidates:
                clean = str(name or "").strip()
                if not clean or clean in names:
                    continue
                helper = (
                    verified_helpers.get(clean)
                    if isinstance(verified_helpers, dict)
                    else None
                )
                if helper is None:
                    continue
                render_policy = str(getattr(helper, "render_policy", "") or "")
                if render_policy:
                    helper_node_id_for_name = str(
                        getattr(graph, "helper_name_to_node_id", {}).get(clean, "")
                        or ""
                    )
                    helper_node = nodes.get(helper_node_id_for_name)
                    certifies = getattr(graph, "_helper_certifies_node", None)
                    route_support_allowed = bool(
                        render_policy == "advisory_route_support_only"
                        and helper_node_id_for_name
                        and (
                            helper_node_id_for_name == getattr(node, "node_id", "")
                            or helper_node_id_for_name == helper_node_id
                            or helper_node_id_for_name == resolved_helper_node_id
                            or helper_node_id_for_name
                            == bridge_support_helper_node_id
                            or (
                                callable(certifies)
                                and certifies(helper_node, node)
                            )
                        )
                    )
                    negative_evidence_allowed = bool(
                        render_policy == "advisory_negative_evidence"
                        and callable(certifies)
                        and certifies(helper_node, node)
                    )
                    root_equivalent_route_helper_allowed = bool(
                        render_policy == "advisory_root_equivalent"
                        and helper_node_id_for_name
                        and helper_node_id_for_name == getattr(node, "node_id", "")
                    )
                    if not (
                        route_support_allowed
                        or negative_evidence_allowed
                        or root_equivalent_route_helper_allowed
                    ):
                        continue
                names.append(clean)
        return names

    @staticmethod
    def _session_goal_statement(session: Any) -> str:
        problem = getattr(session, "problem", None)
        dossier = getattr(session, "dossier", None)
        return str(
            getattr(dossier, "root_statement", "")
            or getattr(problem, "statement_type", "")
            or ""
        ).strip()

    @classmethod
    def _route_contract_status(
        cls,
        graph: Any,
        route_id: str,
        *,
        target_statement: str = "",
        mutate: bool = True,
    ) -> dict[str, Any]:
        status_getter = getattr(graph, "route_assembly_contract_status", None)
        if not callable(status_getter):
            return {
                "ready": False,
                "verdict": "route_assembly_contract_api_missing",
                "dependency_node_ids": cls._route_dependencies(graph, route_id),
            }
        try:
            try:
                raw_status = status_getter(
                    route_id,
                    target_statement=str(target_statement or ""),
                    mutate=mutate,
                )
            except TypeError:
                if not mutate:
                    raise
                raw_status = status_getter(
                    route_id,
                    target_statement=str(target_statement or ""),
                )
            status = dict(raw_status or {})
        except Exception as exc:
            return {
                "ready": False,
                "verdict": "route_assembly_contract_status_exception",
                "exception_type": type(exc).__name__,
                "dependency_node_ids": cls._route_dependencies(graph, route_id),
            }
        if "dependency_node_ids" not in status:
            status["dependency_node_ids"] = cls._route_dependencies(graph, route_id)
        return status

    @staticmethod
    def _route_helper_blocks(
        dossier: Any,
        helper_names: List[str],
        *,
        allow_hidden_helper_names: Optional[Sequence[str]] = None,
        refresh_quality: bool = True,
    ) -> List[str]:
        verified_helpers = getattr(dossier, "verified_helpers", {}) or {}
        allowed_hidden = {
            str(name or "").strip()
            for name in list(allow_hidden_helper_names or [])
            if str(name or "").strip()
        }
        closure_getter = getattr(dossier, "root_replay_helper_closure", None)
        if callable(closure_getter):
            closure_seed_names = list(helper_names)
            if not allowed_hidden:
                visible_seed_names: List[str] = []
                visibility_checker = getattr(
                    dossier,
                    "_verified_helper_context_visible",
                    None,
                )
                for name in closure_seed_names:
                    clean = str(name or "").strip()
                    helper = (
                        verified_helpers.get(clean)
                        if isinstance(verified_helpers, dict)
                        else None
                    )
                    if helper is None:
                        continue
                    visible = (
                        bool(visibility_checker(helper))
                        if callable(visibility_checker)
                        else not bool(
                            str(getattr(helper, "render_policy", "") or "").strip()
                        )
                    )
                    render_policy = str(
                        getattr(helper, "render_policy", "") or ""
                    ).strip()
                    if visible or render_policy == "advisory_root_equivalent":
                        visible_seed_names.append(clean)
                closure_seed_names = visible_seed_names
                if not closure_seed_names:
                    return []
            try:
                try:
                    raw_blocks = closure_getter(
                        replay_helpers=(),
                        support_helper_names=closure_seed_names,
                        refresh_quality=refresh_quality,
                    )
                except TypeError:
                    if not refresh_quality:
                        return []
                    raw_blocks = closure_getter(
                        replay_helpers=(),
                        support_helper_names=closure_seed_names,
                    )
                blocks = list(raw_blocks or [])
            except Exception:
                return []
            seen_closure_names = {
                str(getattr(dossier, "resolve_verified_helper_name", lambda x: x)(
                    str(name or "").strip()
                ) or "").strip()
                for block in blocks
                for name in [helper_decl_name(block)]
                if str(name or "").strip()
            }
            hidden_closure_seen: set[str] = set()

            def append_allowed_hidden_closure(raw_name: str) -> None:
                clean = str(raw_name or "").strip()
                if not clean or clean in seen_closure_names or clean in hidden_closure_seen:
                    return
                helper = (
                    verified_helpers.get(clean)
                    if isinstance(verified_helpers, dict)
                    else None
                )
                if helper is None:
                    return
                render_policy = str(getattr(helper, "render_policy", "") or "").strip()
                visibility_policy = str(
                    getattr(helper, "visibility_policy", "") or ""
                ).strip()
                provenance_tags = {
                    str(tag or "").strip()
                    for tag in list(getattr(helper, "provenance_tags", []) or [])
                    if str(tag or "").strip()
                }
                visibility_checker = getattr(
                    dossier, "_verified_helper_context_visible", None
                )
                context_visible = (
                    bool(visibility_checker(helper))
                    if callable(visibility_checker)
                    else not bool(render_policy)
                )
                route_local = bool(
                    context_visible
                    or clean in allowed_hidden
                    or render_policy == "advisory_route_support_only"
                    or visibility_policy == "advisory_route_support_only"
                    or "route_support_only_helper" in provenance_tags
                )
                if not route_local:
                    return
                hidden_closure_seen.add(clean)
                support_names = []
                try:
                    canonical = getattr(dossier, "_canonical_support_names", None)
                    referenced = getattr(
                        dossier, "_referenced_verified_helper_names", None
                    )
                    raw_supports = list(getattr(helper, "support_names", []) or [])
                    if callable(referenced):
                        raw_supports += list(
                            referenced(getattr(helper, "source", ""), skip=clean)
                            or []
                        )
                    support_names = (
                        list(canonical(raw_supports))
                        if callable(canonical)
                        else [
                            str(item or "").strip()
                            for item in raw_supports
                            if str(item or "").strip()
                        ]
                    )
                except Exception:
                    support_names = []
                for support in support_names:
                    append_allowed_hidden_closure(str(support or "").strip())
                source = str(getattr(helper, "source", "") or "").strip()
                if source:
                    blocks.append(source)
                    seen_closure_names.add(clean)

            for name in helper_names:
                clean = str(name or "").strip()
                if clean in allowed_hidden:
                    append_allowed_hidden_closure(clean)
            return _unique_helper_blocks_by_decl(blocks)
        blocks: List[str] = []
        seen: set[str] = set()
        for name in helper_names:
            clean = str(name or "").strip()
            if not clean or clean in seen:
                continue
            helper = (
                verified_helpers.get(clean)
                if isinstance(verified_helpers, dict)
                else None
            )
            render_policy = str(getattr(helper, "render_policy", "") or "").strip()
            if render_policy and clean not in allowed_hidden:
                continue
            source = str(getattr(helper, "source", "") or "").strip()
            if not source:
                continue
            seen.add(clean)
            blocks.append(source)
        return _unique_helper_blocks_by_decl(blocks)

    @staticmethod
    def _replay_helper_names(helper_blocks: Sequence[str]) -> Tuple[str, ...]:
        names: List[str] = []
        for block in list(helper_blocks or ()):
            name = str(helper_decl_name(str(block or "")) or "").strip()
            if name and name not in names:
                names.append(name)
        return tuple(names)

    @staticmethod
    def _route_has_replayable_bridge(contract_status: Dict[str, Any]) -> bool:
        contract_metadata = dict(contract_status.get("contract_metadata") or {})
        return bool(
            contract_status.get("deterministic_ready")
            or contract_status.get("assembly_bridge_node_ids")
            or contract_status.get("selected_branch_frame_ids")
            or (
                contract_metadata.get("source") == "formalization_bridge_support"
                and contract_metadata.get("bridge_helper_node_id")
            )
        )

    @staticmethod
    def _route_requires_authored_formalization_glue(
        contract_status: Dict[str, Any],
    ) -> bool:
        """Whether route-local support still needs an authored parent bridge.

        A ``formalization_bridge_support`` helper is deliberately recorded as
        non-closing evidence.  Treating that evidence as an executable bridge
        immediately spends the generic root-tactic budget on a route whose
        contract explicitly says parent assembly remains.  Deterministic
        bridge routes are excluded and keep their cheap assembly lane.
        """

        contract_metadata = dict(contract_status.get("contract_metadata") or {})
        return bool(
            not contract_status.get("deterministic_ready")
            and contract_metadata.get("source") == "formalization_bridge_support"
            and contract_metadata.get("bridge_helper_node_id")
        )

    @staticmethod
    def _route_has_new_rejection_evidence(graph: Any, route: Any) -> bool:
        checker = getattr(graph, "node_has_new_rejection_evidence", None)
        if callable(checker):
            try:
                return bool(checker(route))
            except Exception:
                return False
        evidence_getter = getattr(graph, "evidence_hash_for_node", None)
        if not callable(evidence_getter):
            return False
        try:
            evidence_hash = str(evidence_getter(getattr(route, "node_id", "")) or "")
        except Exception:
            return False
        if not evidence_hash:
            return False
        metadata = dict(getattr(route, "metadata", {}) or {})
        node_record = metadata.get("proof_state_node")
        old_hash = str(
            metadata.get("last_rejection_evidence_hash")
            or (
                node_record.get("rejection_evidence_hash")
                if isinstance(node_record, dict)
                else ""
            )
            or ""
        ).strip()
        return evidence_hash != old_hash

    @classmethod
    def _route_ready(
        cls,
        graph: Any,
        route_id: str,
        *,
        target_statement: str = "",
        mutate: bool = True,
    ) -> Tuple[bool, List[str]]:
        route = getattr(graph, "nodes", {}).get(route_id)
        if route is None or getattr(route, "kind", "") != "strategy_route":
            return False, []
        metadata = getattr(route, "metadata", {}) or {}
        route_status = str(getattr(route, "status", "") or "")
        if route_status == "failed":
            return False, []
        if metadata.get("route_retired") or metadata.get("route_dependency_contradicted"):
            return False, []
        if route_status == "rejected" and not cls._route_has_new_rejection_evidence(
            graph,
            route,
        ):
            return False, []
        if metadata.get("assembled_route_proof_hash"):
            return False, []
        contract_status = cls._route_contract_status(
            graph,
            route_id,
            target_statement=target_statement,
            mutate=mutate,
        )
        deps = [
            str(dep or "").strip()
            for dep in list(contract_status.get("dependency_node_ids") or [])
            if str(dep or "").strip()
        ]
        if not bool(contract_status.get("ready")):
            return False, deps
        if not deps:
            return False, []
        return True, deps

    def is_applicable(self, session: Any) -> bool:
        if self.max_routes <= 0 or getattr(session, "dossier", None) is None:
            return False
        graph = getattr(session.dossier, "proof_graph", None)
        if graph is None:
            return False
        item = self._selected_item(session)
        route_id = self._route_id_from_item(item)
        ready, deps = self._route_ready(
            graph,
            route_id,
            target_statement=self._session_goal_statement(session),
        )
        if not ready:
            return False
        helper_names = self._route_helper_names(graph, deps, session.dossier)
        contract_status = self._route_contract_status(
            graph,
            route_id,
            target_statement=self._session_goal_statement(session),
        )
        executable_root_tactic_available = bool(
            helper_names
            and self.root_tactic_timeout_s > 0.0
            and self.root_tactic_max_candidates > 0
            and getattr(session, "lean", None) is not None
        )
        if (
            helper_names
            and self._route_requires_authored_formalization_glue(contract_status)
            and self._authoring_fallback_available(session)
        ):
            return True
        if (
            not bool(contract_status.get("deterministic_ready"))
            and not executable_root_tactic_available
        ):
            return True
        branch_plan = self._branch_cases_assembly_plan(
            contract_status=contract_status,
            dossier=session.dossier,
            route_helper_names=helper_names,
        )
        if branch_plan and getattr(session, "lean", None) is not None:
            return True
        if not helper_names:
            return True
        # A deterministic route with replayable helpers is still actionable
        # when the cheap tactic lane is disabled or unavailable: ``run`` will
        # hand it to the route authoring lane, or materialize a typed rescue.
        if not executable_root_tactic_available:
            return True
        return bool(
            self.root_tactic_timeout_s > 0.0
            and self.root_tactic_max_candidates > 0
            and getattr(session, "lean", None) is not None
        )

    @staticmethod
    def _last_root_tactic_record(session: Any) -> dict[str, Any]:
        def from_attempt(attempt: Any) -> dict[str, Any]:
            metadata = getattr(attempt, "metadata", None)
            if isinstance(metadata, dict):
                record = dict(metadata)
            elif isinstance(attempt, dict):
                record = dict(attempt)
            else:
                record = {}
            if not record:
                return {}
            record.setdefault("verdict", getattr(attempt, "verdict", ""))
            record.setdefault("phase", getattr(attempt, "phase", ""))
            return record

        candidates: List[dict[str, Any]] = []
        recorder = getattr(session, "recorder", None)
        records = getattr(recorder, "records", None)
        if isinstance(records, list):
            for record in reversed(records):
                if isinstance(record, dict):
                    candidates.append(dict(record))
        dossier = getattr(session, "dossier", None)
        attempts = getattr(dossier, "attempts", None)
        if isinstance(attempts, list):
            for attempt in reversed(attempts):
                record = from_attempt(attempt)
                if record:
                    candidates.append(record)
        graph_attempts = getattr(getattr(dossier, "proof_graph", None), "attempts", None)
        if isinstance(graph_attempts, list):
            for attempt in reversed(graph_attempts):
                record = from_attempt(attempt)
                if record:
                    candidates.append(record)
        for record in candidates:
            if str(record.get("phase") or "") == "graph_route_assembly_root_tactic":
                return record
        for record in candidates:
            if "tactic_exit_reason" in record:
                return record
        return candidates[0] if candidates else {}

    @classmethod
    def _last_root_tactic_transient_failure(cls, session: Any) -> bool:
        record = cls._last_root_tactic_record(session)
        return bool(
            record.get("root_tactic_context_preserved")
            and str(record.get("verdict") or "") == "tactic_transient_failure"
        )

    @classmethod
    def _last_root_tactic_deferrable_timeout(cls, session: Any) -> bool:
        record = cls._last_root_tactic_record(session)
        if not record:
            return False
        try:
            candidate_count = int(record.get("tactic_candidate_count", 0) or 0)
        except (TypeError, ValueError):
            candidate_count = 0
        attempts = list(record.get("tactic_attempts") or [])
        try:
            attempt_count = int(
                record.get("tactic_attempt_count", len(attempts)) or 0
            )
        except (TypeError, ValueError):
            attempt_count = len(attempts)
        exit_reason = str(record.get("tactic_exit_reason") or "").strip().lower()
        return bool(
            "timeout" in exit_reason
            and candidate_count > 0
            and attempt_count < candidate_count
        )

    @staticmethod
    def _clear_route_root_tactic_continuation(route: Any) -> None:
        metadata = getattr(route, "metadata", None)
        if not isinstance(metadata, dict):
            return
        for key in (
            "route_root_tactic_continuation_hash",
            "route_root_tactic_suppressed_proofs",
            "route_root_tactic_suppressed_proof_records",
            "route_root_tactic_suppressed_count",
            "route_root_tactic_last_attempt_count",
            "route_root_tactic_last_candidate_count",
            "route_root_tactic_timeout_continuation_hash",
        ):
            metadata.pop(key, None)

    @classmethod
    def _route_root_tactic_suppressed_proofs(
        cls,
        route: Any,
        proof_hash: str,
    ) -> List[str]:
        metadata = getattr(route, "metadata", None)
        if not isinstance(metadata, dict):
            return []
        current_hash = str(proof_hash or "").strip()
        if (
            str(metadata.get("route_root_tactic_continuation_hash") or "").strip()
            != current_hash
        ):
            cls._clear_route_root_tactic_continuation(route)
            return []
        proofs: List[str] = []
        seen: set[str] = set()
        raw = metadata.get("route_root_tactic_suppressed_proofs") or []
        if isinstance(raw, str):
            raw = [raw]
        for item in list(raw or ()):
            proof = str(item or "").strip()
            if not proof or proof in seen:
                continue
            seen.add(proof)
            proofs.append(proof)
        if len(proofs) != len(list(raw or ())):
            metadata["route_root_tactic_suppressed_proofs"] = list(proofs)
            metadata["route_root_tactic_suppressed_count"] = len(proofs)
        return proofs

    @classmethod
    def _route_root_tactic_suppressed_proof_records(
        cls,
        route: Any,
        proof_hash: str,
    ) -> List[dict[str, str]]:
        metadata = getattr(route, "metadata", None)
        if not isinstance(metadata, dict):
            return []
        current_hash = str(proof_hash or "").strip()
        if (
            str(metadata.get("route_root_tactic_continuation_hash") or "").strip()
            != current_hash
        ):
            cls._clear_route_root_tactic_continuation(route)
            return []
        raw = metadata.get("route_root_tactic_suppressed_proof_records") or []
        records: List[dict[str, str]] = []
        seen: set[tuple[str, str]] = set()
        for item in list(raw or ()):
            if not isinstance(item, dict):
                continue
            proof = str(item.get("proof") or "").strip()
            target = str(item.get("target_statement") or "").strip()
            if not proof:
                continue
            key = (target, proof)
            if key in seen:
                continue
            seen.add(key)
            records.append({"proof": proof, "target_statement": target})
        if records:
            metadata["route_root_tactic_suppressed_proof_records"] = list(records)
            metadata["route_root_tactic_suppressed_proofs"] = list(
                dict.fromkeys(record["proof"] for record in records)
            )
            metadata["route_root_tactic_suppressed_count"] = len(records)
            return records
        return [
            {"proof": proof, "target_statement": ""}
            for proof in cls._route_root_tactic_suppressed_proofs(route, proof_hash)
        ]

    @classmethod
    def _record_route_root_tactic_attempted_proofs(
        cls,
        route: Any,
        *,
        proof_hash: str,
        record: dict[str, Any],
    ) -> dict[str, int]:
        metadata = getattr(route, "metadata", None)
        if not isinstance(metadata, dict):
            return {"added": 0, "total": 0, "attempted": 0}
        attempted: List[str] = []
        attempted_records: List[dict[str, str]] = []
        raw_records = record.get("tactic_attempted_proof_records") or []
        if isinstance(raw_records, dict):
            raw_records = [raw_records]
        for item in list(raw_records or ()):
            if not isinstance(item, dict):
                continue
            proof = str(item.get("proof") or "").strip()
            target = str(item.get("target_statement") or "").strip()
            if not proof:
                continue
            attempted_records.append({"proof": proof, "target_statement": target})
            attempted.append(proof)
        raw_attempted = record.get("tactic_attempted_proofs") or []
        if isinstance(raw_attempted, str):
            raw_attempted = [raw_attempted]
        if not attempted_records:
            for proof in list(raw_attempted or ()):
                text = str(proof or "").strip()
                if text:
                    attempted.append(text)
                    attempted_records.append(
                        {"proof": text, "target_statement": ""}
                    )
        if not attempted:
            for attempt in list(record.get("tactic_attempts") or []):
                if not isinstance(attempt, dict):
                    continue
                text = str(attempt.get("proof") or "").strip()
                if text:
                    attempted.append(text)
                    attempted_records.append(
                        {
                            "proof": text,
                            "target_statement": str(
                                attempt.get("target_statement") or ""
                            ).strip(),
                        }
                    )
        if not attempted:
            return {
                "added": 0,
                "total": len(
                    cls._route_root_tactic_suppressed_proof_records(route, proof_hash)
                ),
                "attempted": 0,
            }
        existing_records = cls._route_root_tactic_suppressed_proof_records(
            route,
            proof_hash,
        )
        seen = {
            (
                str(item.get("target_statement") or "").strip(),
                str(item.get("proof") or "").strip(),
            )
            for item in existing_records
            if str(item.get("proof") or "").strip()
        }
        added = 0
        for item in attempted_records:
            proof = str(item.get("proof") or "").strip()
            target = str(item.get("target_statement") or "").strip()
            if not proof:
                continue
            key = (target, proof)
            if key in seen:
                continue
            seen.add(key)
            existing_records.append({"proof": proof, "target_statement": target})
            added += 1
        metadata["route_root_tactic_continuation_hash"] = str(proof_hash or "").strip()
        metadata["route_root_tactic_suppressed_proof_records"] = list(existing_records)
        metadata["route_root_tactic_suppressed_proofs"] = list(
            dict.fromkeys(item["proof"] for item in existing_records)
        )
        metadata["route_root_tactic_suppressed_count"] = len(existing_records)
        try:
            metadata["route_root_tactic_last_attempt_count"] = int(
                record.get("tactic_attempt_count", len(attempted)) or 0
            )
        except (TypeError, ValueError):
            metadata["route_root_tactic_last_attempt_count"] = len(attempted)
        try:
            metadata["route_root_tactic_last_candidate_count"] = int(
                record.get("tactic_candidate_count", 0) or 0
            )
        except (TypeError, ValueError):
            metadata["route_root_tactic_last_candidate_count"] = 0
        return {
            "added": added,
            "total": int(metadata.get("route_root_tactic_suppressed_count", 0) or 0),
            "attempted": len(attempted),
        }

    @staticmethod
    def _authoring_fallback_available(session: Any) -> bool:
        """Whether the selected route can fall through to a targeted LLM turn."""

        available = getattr(session, "action_available", None)
        action_getter = getattr(session, "registered_action", None)
        conversation_action_ids = (
            "conversation_turn_prove",
            "conversation_turn_refine",
        )
        conversation_available = False
        conversation_client = None
        for action_id in conversation_action_ids:
            if not (callable(available) and bool(available(action_id))):
                continue
            conversation_action = (
                action_getter(action_id) if callable(action_getter) else None
            )
            candidate_client = getattr(conversation_action, "client", None)
            if candidate_client is None:
                candidate_client = (
                    getattr(session, "prover_client", None)
                    if action_id == "conversation_turn_prove"
                    else getattr(session, "refiner_client", None)
                )
            if candidate_client is None:
                continue
            conversation_available = True
            conversation_client = candidate_client
            break
        return bool(
            conversation_available
            and getattr(session, "conv", None) is not None
            and getattr(session, "lean", None) is not None
            and conversation_client is not None
        )

    @staticmethod
    def _route_dependency_signature(
        graph: Any,
        deps: List[str],
        *,
        route_id: str = "",
    ) -> List[dict[str, Any]]:
        signature_getter = getattr(graph, "route_dependency_signature", None)
        if callable(signature_getter) and str(route_id or "").strip():
            try:
                return list(signature_getter(str(route_id or "").strip()) or [])
            except Exception:
                pass
        nodes = getattr(graph, "nodes", {}) or {}
        signature: List[dict[str, Any]] = []
        for dep_id in deps:
            node = nodes.get(dep_id)
            metadata = dict(getattr(node, "metadata", {}) or {}) if node else {}
            signature.append(
                {
                    "node_id": str(dep_id or ""),
                    "kind": str(getattr(node, "kind", "") or "") if node else "",
                    "status": str(getattr(node, "status", "") or "") if node else "",
                    "source_hash": str(getattr(node, "source_hash", "") or "")
                    if node
                    else "",
                    "proof_hash": str(getattr(node, "proof_hash", "") or "")
                    if node
                    else "",
                    "verified_helper_source_hash": str(
                        metadata.get("verified_helper_source_hash") or ""
                    ),
                    "verified_by_helper_name": str(
                        metadata.get("verified_by_helper_name") or ""
                    ),
                    "verified_by_helper_node_id": str(
                        metadata.get("verified_by_helper_node_id") or ""
                    ),
                    "proposal_revision": str(metadata.get("proposal_revision") or ""),
                }
            )
        return signature

    @classmethod
    def _route_dependency_signature_hash(
        cls,
        graph: Any,
        deps: List[str],
        *,
        route_id: str = "",
    ) -> str:
        hash_getter = getattr(graph, "route_dependency_signature_hash", None)
        if callable(hash_getter) and str(route_id or "").strip():
            try:
                signature_hash = str(hash_getter(str(route_id or "").strip()) or "").strip()
            except Exception:
                signature_hash = ""
            if signature_hash:
                return signature_hash
        from ensemble_prover.proof_graph import graph_text_hash

        return graph_text_hash(
            json.dumps(
                cls._route_dependency_signature(graph, deps, route_id=route_id),
                sort_keys=True,
            )
        )

    @staticmethod
    def _increment_metric(session: Any, key: str, amount: int = 1) -> None:
        increment = getattr(getattr(session, "dossier", None), "increment_tool_metric", None)
        if callable(increment):
            try:
                increment(str(key), int(amount or 0))
            except Exception:
                pass

    @staticmethod
    def _helper_visible(dossier: Any, name: str) -> bool:
        helper_name = str(name or "").strip()
        if not helper_name:
            return False
        verified_helpers = getattr(dossier, "verified_helpers", {}) or {}
        helper = verified_helpers.get(helper_name) if isinstance(verified_helpers, dict) else None
        if helper is None:
            return False
        render_policy = str(getattr(helper, "render_policy", "") or "")
        return bool(render_policy in {"", "advisory_requires_unproved_premise"})

    @classmethod
    def _branch_cases_assembly_plan(
        cls,
        *,
        contract_status: Dict[str, Any],
        dossier: Any,
        route_helper_names: Sequence[str],
    ) -> Optional[Dict[str, Any]]:
        selected_ids = [
            str(item or "").strip()
            for item in list(contract_status.get("selected_branch_frame_ids") or [])
            if str(item or "").strip()
        ]
        if not selected_ids:
            return None
        frames_by_id = {
            str(frame.get("frame_id") or ""): dict(frame)
            for frame in list(contract_status.get("branch_frames") or [])
            if isinstance(frame, dict) and str(frame.get("frame_id") or "").strip()
        }
        frames = [frames_by_id.get(frame_id) for frame_id in selected_ids]
        if not frames or any(frame is None for frame in frames):
            return None
        selected_frames = [dict(frame or {}) for frame in frames]
        case_names = {
            str(frame.get("case_helper_name") or "").strip()
            for frame in selected_frames
        }
        case_names.discard("")
        if len(case_names) != 1:
            return None
        case_helper_name = next(iter(case_names))
        case_statement = str(selected_frames[0].get("case_statement") or "").strip()
        first_metadata = dict(selected_frames[0].get("metadata") or {})
        case_full_statement = str(
            selected_frames[0].get("case_full_statement")
            or first_metadata.get("case_full_statement")
            or case_statement
        ).strip()
        branch_frames = sorted(
            selected_frames,
            key=lambda item: int(item.get("branch_index") or 0),
        )
        branch_steps: List[Dict[str, Any]] = []
        reducer_names: List[str] = []
        support_names: List[str] = []
        for frame in branch_frames:
            metadata = dict(frame.get("metadata") or {})
            closed_by_false = bool(metadata.get("branch_closed_by_false_elim"))
            reducer_name = str(frame.get("reducer_helper_name") or "").strip()
            if not closed_by_false and not reducer_name:
                return None
            if reducer_name:
                reducer_names.append(reducer_name)
            for binding in list(metadata.get("reducer_premise_bindings") or []):
                if not isinstance(binding, dict):
                    continue
                if str(binding.get("kind") or "") != "support":
                    continue
                support_name = str(binding.get("support_helper_name") or "").strip()
                if support_name:
                    support_names.append(support_name)
            branch_steps.append(
                {
                    "frame_id": str(frame.get("frame_id") or "").strip(),
                    "reducer_helper_name": reducer_name,
                    "reducer_statement": str(
                        frame.get("reducer_statement") or ""
                    ).strip(),
                    "closed_by_false_elim": closed_by_false,
                    "reducer_premise_bindings": list(
                        metadata.get("reducer_premise_bindings") or []
                    ),
                    "branch_path": [
                        int(part)
                        for part in list(metadata.get("case_branch_path") or [])
                        if str(part).strip() in {"0", "1"}
                    ],
                }
            )
        if any(
            not step["closed_by_false_elim"] and not step["reducer_helper_name"]
            for step in branch_steps
        ):
            return None
        required_names = list(
            dict.fromkeys([case_helper_name, *reducer_names, *support_names])
        )
        if any(not cls._helper_visible(dossier, name) for name in required_names):
            return None
        all_helper_names = list(
            dict.fromkeys(
                [
                    str(name or "").strip()
                    for name in list(route_helper_names or []) + required_names
                    if str(name or "").strip()
                ]
            )
        )
        if not all_helper_names:
            return None
        return {
            "case_helper_name": case_helper_name,
            "case_statement": case_statement,
            "case_full_statement": case_full_statement,
            "branch_frames": branch_frames,
            "branch_steps": branch_steps,
            "reducer_helper_names": reducer_names,
            "helper_names": all_helper_names,
        }

    @staticmethod
    def _lean_apply(name: str, args: Sequence[str], trailing: Sequence[str] = ()) -> str:
        parts = [
            str(part or "").strip()
            for part in [name, *list(args or ()), *list(trailing or ())]
            if str(part or "").strip()
        ]
        return " ".join(parts)

    @staticmethod
    def _right_nested_branch_paths(count: int) -> List[List[int]]:
        if count <= 0:
            return []
        if count == 1:
            return [[]]
        return [
            ([1] * index + [0]) if index < count - 1 else ([1] * index)
            for index in range(count)
        ]

    @classmethod
    def _branch_step_tree(
        cls,
        branch_steps: Sequence[Dict[str, Any]],
    ) -> Dict[str, Any]:
        steps = [dict(step or {}) for step in list(branch_steps or [])]
        if not steps:
            return {}
        paths = [
            [
                int(part)
                for part in list(step.get("branch_path") or [])
                if str(part).strip() in {"0", "1"}
            ]
            for step in steps
        ]
        if any(not path for path in paths) or len({tuple(path) for path in paths}) != len(
            paths
        ):
            fallback_paths = cls._right_nested_branch_paths(len(steps))
            for step, path in zip(steps, fallback_paths):
                step["branch_path"] = path
        tree: Dict[str, Any] = {}
        for step in steps:
            path = [
                int(part)
                for part in list(step.get("branch_path") or [])
                if str(part).strip() in {"0", "1"}
            ]
            if not path:
                return {"step": step}
            cursor = tree
            for direction in path[:-1]:
                key = "left" if direction == 0 else "right"
                cursor = cursor.setdefault(key, {})
            leaf_key = "left" if path[-1] == 0 else "right"
            if cursor.get(leaf_key):
                return {}
            cursor[leaf_key] = {"step": step}
        return tree

    @staticmethod
    def _branch_hypothesis_name(path: Sequence[int], side: int) -> str:
        label = "".join("l" if int(part) == 0 else "r" for part in path) or "root"
        suffix = "left" if int(side) == 0 else "right"
        return f"h_branch_{label}_{suffix}"

    @classmethod
    def _render_rcases_tree(
        cls,
        *,
        case_expr: str,
        branch_tree: Dict[str, Any],
        args: Sequence[str],
        path: Sequence[int] = (),
        indent: str = "  ",
    ) -> List[str]:
        tree = dict(branch_tree or {})
        if not tree:
            return []
        if "step" in tree:
            step = dict(tree.get("step") or {})
            hypothesis = str(case_expr or "").strip()
            if bool(step.get("closed_by_false_elim")):
                return [f"{indent}exact False.elim {hypothesis}"]
            reducer_name = str(step.get("reducer_helper_name") or "").strip()
            if not reducer_name:
                return []
            reducer_statement = str(step.get("reducer_statement") or "").strip()
            reducer_arg_count = cls._forall_intro_application_arity(
                reducer_statement,
                exclude_proof_binders=True,
            )
            if reducer_statement and reducer_arg_count > len(args):
                return []
            premise_bindings = [
                dict(item or {})
                for item in list(step.get("reducer_premise_bindings") or [])
                if isinstance(item, dict)
            ]
            if not premise_bindings:
                premise_bindings = [{"kind": "branch"}]

            def render_binding(binding: Dict[str, Any]) -> str:
                kind = str(binding.get("kind") or "").strip()
                if kind == "branch":
                    return hypothesis
                if kind != "support":
                    return ""
                root_arg_index = str(binding.get("support_root_arg_index") or "").strip()
                if root_arg_index:
                    try:
                        index = int(root_arg_index)
                    except ValueError:
                        return ""
                    if index <= 0 or index > len(args):
                        return ""
                    return args[index - 1]
                support_name = str(binding.get("support_helper_name") or "").strip()
                if not support_name:
                    return ""
                support_statement = str(
                    binding.get("support_full_statement")
                    or binding.get("support_statement")
                    or binding.get("statement")
                    or ""
                ).strip()
                support_arg_count = cls._forall_intro_arity(support_statement)
                if support_statement and support_arg_count > len(args):
                    return ""
                support_args = (
                    list(args[:support_arg_count]) if support_statement else []
                )
                support_expr = cls._lean_apply(support_name, support_args)
                if " " in support_expr:
                    support_expr = f"({support_expr})"
                return support_expr

            reducer_args: List[str] = []
            data_arg_index = 0
            binding_index = 0
            for entry in cls._forall_binder_application_entries(
                reducer_statement,
            ):
                arity = int(entry.get("arity") or 0)
                if arity <= 0:
                    continue
                if entry.get("proof"):
                    for _ in range(arity):
                        if binding_index >= len(premise_bindings):
                            return []
                        rendered = render_binding(premise_bindings[binding_index])
                        if not rendered:
                            return []
                        reducer_args.append(rendered)
                        binding_index += 1
                    continue
                if data_arg_index + arity > len(args):
                    return []
                reducer_args.extend(args[data_arg_index : data_arg_index + arity])
                data_arg_index += arity
            for binding in premise_bindings[binding_index:]:
                rendered = render_binding(binding)
                if not rendered:
                    return []
                reducer_args.append(rendered)
            return [f"{indent}exact {cls._lean_apply(reducer_name, reducer_args)}"]
        left_tree = dict(tree.get("left") or {})
        right_tree = dict(tree.get("right") or {})
        if not left_tree or not right_tree:
            return []
        path_tuple = tuple(int(part) for part in path)
        left_hyp = cls._branch_hypothesis_name(path_tuple, 0)
        right_hyp = cls._branch_hypothesis_name(path_tuple, 1)
        left_lines = cls._render_rcases_tree(
            case_expr=left_hyp,
            branch_tree=left_tree,
            args=args,
            path=(*path_tuple, 0),
            indent=f"{indent}  ",
        )
        right_lines = cls._render_rcases_tree(
            case_expr=right_hyp,
            branch_tree=right_tree,
            args=args,
            path=(*path_tuple, 1),
            indent=f"{indent}  ",
        )
        if not left_lines or not right_lines:
            return []
        lines = [f"{indent}rcases {case_expr} with {left_hyp} | {right_hyp}"]
        lines.append(f"{indent}·")
        lines.extend(left_lines)
        lines.append(f"{indent}·")
        lines.extend(right_lines)
        return lines

    @classmethod
    def _forall_intro_application_arity(
        cls,
        statement: str,
        *,
        exclude_proof_binders: bool = False,
    ) -> int:
        return graph_statement_explicit_arity(
            statement,
            exclude_proof_binders=exclude_proof_binders,
        )

    @classmethod
    def _forall_binder_application_entries(
        cls,
        statement: str,
    ) -> List[Dict[str, Any]]:
        return [
            {"arity": arity, "proof": is_proof}
            for arity, is_proof in graph_statement_forall_application_entries(
                statement
            )
        ]

    @classmethod
    def _forall_intro_arity(cls, statement: str) -> int:
        return cls._forall_intro_application_arity(statement)

    @classmethod
    def _branch_cases_intro_arities(
        cls,
        *,
        goal_statement: str,
        max_probe_arity: int,
    ) -> List[int]:
        goal_arity = cls._forall_intro_arity(goal_statement)
        arities = list(range(max(0, int(max_probe_arity or 0)) + 1))
        if goal_arity > max_probe_arity:
            arities.append(goal_arity)
        return list(dict.fromkeys(arities))

    @classmethod
    def _branch_cases_proof_candidates(
        cls,
        *,
        plan: Dict[str, Any],
        goal_statement: str = "",
        max_intro_args: int = 8,
    ) -> List[str]:
        case_helper_name = str(plan.get("case_helper_name") or "").strip()
        case_statement = str(plan.get("case_statement") or "").strip()
        case_full_statement = str(
            plan.get("case_full_statement") or case_statement
        ).strip()
        branch_steps = [
            dict(step or {})
            for step in list(plan.get("branch_steps") or [])
            if isinstance(step, dict)
        ]
        if not case_helper_name or len(branch_steps) < 2:
            return []
        branch_tree = cls._branch_step_tree(branch_steps)
        if not branch_tree:
            return []
        candidates: List[str] = []
        for arity in cls._branch_cases_intro_arities(
            goal_statement=goal_statement,
            max_probe_arity=max_intro_args,
        ):
            args = [f"x{idx}" for idx in range(1, arity + 1)]
            case_arg_count = cls._forall_intro_arity(case_full_statement)
            if case_full_statement and case_arg_count > len(args):
                continue
            case_args = (
                list(args[:case_arg_count]) if case_full_statement else list(args)
            )
            case_expr = cls._lean_apply(case_helper_name, case_args)
            lines = ["by", "  classical"]
            lines.extend(f"  intro {arg}" for arg in args)
            case_lines = cls._render_rcases_tree(
                case_expr=case_expr,
                branch_tree=branch_tree,
                args=args,
                indent="  ",
            )
            if not case_lines:
                continue
            lines.extend(case_lines)
            proof = "\n".join(lines).strip()
            if proof not in candidates:
                candidates.append(proof)
        return candidates

    async def _try_branch_cases_assembly(
        self,
        *,
        graph: Any,
        route_id: str,
        deps: List[str],
        session: Any,
        contract_status: Dict[str, Any],
        route_helper_names: List[str],
        started: float,
    ) -> Optional[MiniOutcome]:
        if getattr(session, "lean", None) is None:
            return None
        plan = self._branch_cases_assembly_plan(
            contract_status=contract_status,
            dossier=session.dossier,
            route_helper_names=route_helper_names,
        )
        if not plan:
            return None
        helper_names = list(plan.get("helper_names") or route_helper_names)
        helper_blocks = self._route_helper_blocks(
            session.dossier,
            helper_names,
            allow_hidden_helper_names=route_helper_names,
        )
        if not helper_blocks:
            return None
        goal_statement = self._session_goal_statement(session)
        proof_candidates = self._branch_cases_proof_candidates(
            plan=plan,
            goal_statement=goal_statement,
        )
        if not proof_candidates:
            return None
        initial_selected_frame_ids = [
            str(frame_id or "").strip()
            for frame_id in list(contract_status.get("selected_branch_frame_ids") or [])
            if str(frame_id or "").strip()
        ]
        initial_signature_hash = self._route_dependency_signature_hash(
            graph,
            deps,
            route_id=route_id,
        )
        self._increment_metric(
            session,
            "mini_session_graph_route_cases_synthesized",
            1,
        )
        preamble = (
            session.acceptance_preamble()
            if hasattr(session, "acceptance_preamble")
            else str(getattr(getattr(session, "conv", None), "preamble", "") or "")
        )
        attempts: List[Dict[str, Any]] = []
        for proof in proof_candidates:
            try:
                result = await session.lean.check(
                    goal_statement,
                    proof,
                    helper_blocks,
                    preamble_override=preamble,
                    timeout_s=max(1.0, min(10.0, self.root_tactic_timeout_s or 10.0)),
                    check_kind="full",
                )
            except Exception as exc:
                attempts.append(
                    {
                        "ok": False,
                        "exception_type": type(exc).__name__,
                        "exception_message": str(exc),
                    }
                )
                continue
            ok = bool(getattr(result, "ok", False))
            attempts.append(
                {
                    "ok": ok,
                    "output": str(getattr(result, "output", "") or "")[:500],
                }
            )
            if not ok:
                continue
            from ensemble_prover.proof_graph import graph_text_hash

            latest_contract_status = self._route_contract_status(
                graph,
                route_id,
                target_statement=goal_statement,
            )
            latest_deps = [
                str(dep or "").strip()
                for dep in list(latest_contract_status.get("dependency_node_ids") or [])
                if str(dep or "").strip()
            ]
            latest_signature_hash = self._route_dependency_signature_hash(
                graph,
                latest_deps,
                route_id=route_id,
            )
            latest_route_helper_names = self._route_helper_names(
                graph,
                latest_deps,
                session.dossier,
            )
            latest_plan = self._branch_cases_assembly_plan(
                contract_status=latest_contract_status,
                dossier=session.dossier,
                route_helper_names=latest_route_helper_names,
            )
            latest_helper_names = (
                list(latest_plan.get("helper_names") or [])
                if latest_plan
                else []
            )
            latest_selected_frame_ids = [
                str(frame_id or "").strip()
                for frame_id in list(
                    latest_contract_status.get("selected_branch_frame_ids") or []
                )
                if str(frame_id or "").strip()
            ]
            stale_reasons: List[str] = []
            if not bool(latest_contract_status.get("deterministic_ready")):
                stale_reasons.append("contract_not_deterministic_ready")
            if latest_selected_frame_ids != initial_selected_frame_ids:
                stale_reasons.append("branch_frames_changed")
            if latest_signature_hash != initial_signature_hash:
                stale_reasons.append("dependency_signature_changed")
            if latest_helper_names != helper_names:
                stale_reasons.append("helper_names_changed")
            if stale_reasons:
                if route_id in getattr(graph, "nodes", {}):
                    graph.record_attempt(
                        route_id,
                        phase=self.id,
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        proof=json.dumps(
                            {
                                "route_id": route_id,
                                "candidate_count": len(proof_candidates),
                            },
                            sort_keys=True,
                        ),
                        verdict="route_cases_assembly_contract_stale",
                        error_type="route_cases_assembly_contract_stale",
                        metadata={
                            "dependency_node_ids": list(deps),
                            "latest_dependency_node_ids": list(latest_deps),
                            "helper_names": list(helper_names),
                            "latest_helper_names": list(latest_helper_names),
                            "selected_branch_frame_ids": list(
                                initial_selected_frame_ids
                            ),
                            "latest_selected_branch_frame_ids": list(
                                latest_selected_frame_ids
                            ),
                            "dependency_signature_hash": initial_signature_hash,
                            "latest_dependency_signature_hash": latest_signature_hash,
                            "route_assembly_contract_status": dict(contract_status),
                            "latest_route_assembly_contract_status": dict(
                                latest_contract_status
                            ),
                            "stale_reasons": list(stale_reasons),
                            "attempts": attempts[:5],
                            "selected_work_item": dict(
                                getattr(session, "selected_work_item_record", {}) or {}
                            ),
                        },
                    )
                self._increment_metric(
                    session,
                    "mini_session_graph_route_cases_failed",
                    1,
                )
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "verdict": "route_cases_assembly_contract_stale",
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "latest_dependency_node_ids": list(latest_deps),
                        "helper_names": list(helper_names),
                        "latest_helper_names": list(latest_helper_names),
                        "stale_reasons": list(stale_reasons),
                        "preserve_frontier_work": True,
                        "graph_route_assembled": False,
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
            latest_helper_blocks = self._route_helper_blocks(
                session.dossier,
                latest_helper_names,
                allow_hidden_helper_names=latest_helper_names,
            )
            if not latest_helper_blocks:
                return None
            proof_hash = graph_text_hash(
                json.dumps(
                    {
                        "route_id": route_id,
                        "dependency_node_ids": list(latest_deps),
                        "dependency_signature_hash": latest_signature_hash,
                        "selected_branch_frame_ids": list(latest_selected_frame_ids),
                        "proof": proof,
                    },
                    sort_keys=True,
                )
            )
            route = graph.nodes[route_id]
            route.metadata["assembled_dependency_node_ids"] = list(latest_deps)
            route.metadata["assembled_dependency_signature_hash"] = latest_signature_hash
            route.metadata["assembled_by_action"] = self.id
            route.metadata["assembled_route_proof_hash"] = proof_hash
            route.metadata["assembled_branch_frame_ids"] = list(latest_selected_frame_ids)
            route.metadata["route_cases_assembly_helper_names"] = list(
                latest_helper_names
            )
            latest_replay_helper_names = self._replay_helper_names(
                latest_helper_blocks
            )
            graph.record_attempt(
                route_id,
                phase=self.id,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                proof=json.dumps({"proof": proof, "route_id": route_id}, sort_keys=True),
                verdict="route_cases_assembly_solved",
                metadata={
                    "dependency_node_ids": list(latest_deps),
                    "dependency_signature_hash": latest_signature_hash,
                    "helper_names": list(latest_helper_names),
                    "replay_helper_names": list(latest_replay_helper_names),
                    "selected_branch_frame_ids": list(latest_selected_frame_ids),
                    "route_assembly_contract_status": dict(latest_contract_status),
                    "selected_work_item": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                },
            )
            self._increment_metric(session, "mini_session_graph_route_cases_solved", 1)
            return MiniOutcome(
                action_id=self.id,
                solved=True,
                proof=proof,
                progress=True,
                cost_seconds=time.monotonic() - started,
                root_candidate=RootFinalizationCandidate(
                    proof=proof,
                    replay_helpers=tuple(latest_helper_blocks),
                    helper_names=latest_replay_helper_names,
                    phase=self.id,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    source_action_id=self.id,
                    route_id=route_id,
                    dependency_node_ids=tuple(latest_deps),
                    dependency_helper_names=tuple(latest_helper_names),
                    target_statement=goal_statement,
                    require_route_contract=True,
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof,
                        phase=self.id,
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        target_statement=goal_statement,
                        replay_helpers=tuple(latest_helper_blocks),
                        helper_names=latest_replay_helper_names,
                        source="graph_route_assembly_cases",
                    ),
                ),
                metadata={
                    "verdict": "route_cases_assembly_solved",
                    "route_id": route_id,
                    "dependency_node_ids": list(latest_deps),
                    "dependency_signature_hash": latest_signature_hash,
                    "helper_names": list(latest_helper_names),
                    "selected_branch_frame_ids": list(latest_selected_frame_ids),
                    "strong_progress": True,
                    "graph_route_assembled": True,
                    "selected_work_item": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                },
            )
        graph.record_attempt(
            route_id,
            phase=self.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            proof=json.dumps(
                {
                    "route_id": route_id,
                    "candidate_count": len(proof_candidates),
                },
                sort_keys=True,
            ),
            verdict="route_cases_assembly_failed",
            error_type="route_cases_assembly_failed",
            metadata={
                "dependency_node_ids": list(deps),
                "helper_names": list(helper_names),
                "selected_branch_frame_ids": list(
                    contract_status.get("selected_branch_frame_ids") or []
                ),
                "attempts": attempts[:5],
            },
        )
        self._increment_metric(session, "mini_session_graph_route_cases_failed", 1)
        return None

    @classmethod
    def _no_replayable_helpers_outcome(
        cls,
        *,
        graph: Any,
        route_id: str,
        deps: List[str],
        session: Any,
        started: float,
    ) -> MiniOutcome:
        route = graph.nodes[route_id]
        dependency_signature = cls._route_dependency_signature(
            graph,
            deps,
            route_id=route_id,
        )
        hash_getter = getattr(graph, "route_dependency_signature_hash", None)
        if callable(hash_getter):
            try:
                signature_hash = str(hash_getter(route_id) or "").strip()
            except Exception:
                signature_hash = ""
        else:
            signature_hash = ""
        if not signature_hash:
            from ensemble_prover.proof_graph import graph_text_hash

            signature_hash = graph_text_hash(
                json.dumps(dependency_signature, sort_keys=True)
            )
        route.metadata["route_no_replayable_helper_signature_hash"] = signature_hash
        route.metadata["route_no_replayable_helper_dependency_node_ids"] = list(deps)
        graph.record_attempt(
            route_id,
            phase=cls.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            proof=json.dumps(
                {
                    "route_id": route_id,
                    "dependency_node_ids": list(deps),
                    "dependency_signature": dependency_signature,
                },
                sort_keys=True,
            ),
            verdict="route_ready_no_replayable_helpers",
            error_type="route_no_replayable_helpers",
            metadata={
                "dependency_node_ids": list(deps),
                "dependency_signature_hash": signature_hash,
                "selected_work_item": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
            },
        )
        increment = getattr(getattr(session, "dossier", None), "increment_tool_metric", None)
        if callable(increment):
            try:
                increment("mini_session_graph_route_no_replayable_helpers", 1)
            except Exception:
                pass
        return MiniOutcome(
            action_id=cls.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "verdict": "route_ready_no_replayable_helpers",
                "route_id": route_id,
                "dependency_node_ids": list(deps),
                "dependency_signature_hash": signature_hash,
                "strong_progress": False,
                "graph_route_assembled": False,
                "preserve_frontier_work": False,
                "graph_work_consumed_verdict": "route_ready_no_replayable_helpers",
                "graph_work_consumed_error_type": "route_no_replayable_helpers",
                "selected_work_item": dict(
                    getattr(session, "selected_work_item_record", {}) or {}
                ),
            },
        )

    def _request_authoring_without_tactic(
        self,
        *,
        graph: Any,
        route: Any,
        route_id: str,
        deps: list[str],
        helper_names: list[str],
        contract_status: dict[str, Any],
        session: Any,
        started: float,
    ) -> MiniOutcome:
        from ensemble_prover.proof_graph import graph_text_hash

        signature = self._route_dependency_signature(graph, deps, route_id=route_id)
        signature_getter = getattr(graph, "route_dependency_signature_hash", None)
        try:
            signature_hash = str(signature_getter(route_id) or "").strip()
        except Exception:
            signature_hash = ""
        if not signature_hash:
            signature_hash = graph_text_hash(json.dumps(signature, sort_keys=True))
        proof_hash = graph_text_hash(
            json.dumps(
                {
                    "route_id": route_id,
                    "dependency_node_ids": list(deps),
                    "dependency_signature": signature,
                    "mode": "authoring_without_root_tactic",
                },
                sort_keys=True,
            )
        )
        route.metadata["route_root_tactic_authoring_ready_hash"] = proof_hash
        route.metadata["route_root_tactic_authoring_ready_signature_hash"] = (
            signature_hash
        )
        route.metadata["route_root_tactic_authoring_helper_names"] = list(helper_names)
        route.metadata["route_root_tactic_helper_names"] = list(helper_names)
        verdict = "route_authoring_requested_without_root_tactic"
        graph.record_attempt(
            route_id,
            phase=self.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            proof=json.dumps({"route_id": route_id, "dependency_node_ids": deps}, sort_keys=True),
            verdict=verdict,
            metadata={
                "dependency_node_ids": list(deps),
                "helper_names": list(helper_names),
                "route_assembly_contract_status": dict(contract_status),
                "route_root_tactic_authoring_ready_hash": proof_hash,
                "route_root_tactic_authoring_ready_signature_hash": signature_hash,
            },
        )
        increment = getattr(getattr(session, "dossier", None), "increment_tool_metric", None)
        if callable(increment):
            increment("mini_session_graph_route_authoring_requested", 1)
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=False,
            cost_seconds=time.monotonic() - started,
            metadata={
                "verdict": verdict,
                "route_id": route_id,
                "dependency_node_ids": list(deps),
                "helper_names": list(helper_names),
                "preserve_frontier_work": False,
                "graph_work_consumed_verdict": verdict,
                "graph_work_consumed_error_type": verdict,
            },
        )

    def _materialize_failed_route_rescue(
        self,
        *,
        graph: Any,
        route_id: str,
        deps: list[str],
        helper_names: list[str],
        contract_status: dict[str, Any],
        session: Any,
        started: float,
        failure_verdict: str,
    ) -> MiniOutcome:
        from ensemble_prover.proof_graph import graph_text_hash

        signature = self._route_dependency_signature(graph, deps, route_id=route_id)
        signature_getter = getattr(graph, "route_dependency_signature_hash", None)
        try:
            signature_hash = str(signature_getter(route_id) or "").strip()
        except Exception:
            signature_hash = ""
        if not signature_hash:
            signature_hash = graph_text_hash(json.dumps(signature, sort_keys=True))
        route = getattr(graph, "nodes", {}).get(route_id)
        prior_rescue_id = str(
            (getattr(route, "metadata", {}) or {}).get(
                "route_missing_assembly_bridge_rescue_obligation_id"
            )
            or ""
        )
        prior_rescue = getattr(graph, "nodes", {}).get(prior_rescue_id)
        prior_generation = int(
            (getattr(prior_rescue, "metadata", {}) or {}).get(
                "route_missing_assembly_bridge_rescue_generation",
                -1,
            )
            or -1
        )
        prior_status = str(getattr(prior_rescue, "status", "") or "")
        rescue = None
        ensure_rescue = getattr(graph, "ensure_route_missing_assembly_bridge_rescue", None)
        if callable(ensure_rescue):
            rescue = ensure_rescue(
                route_id,
                contract_status,
                signature_hash=signature_hash,
                phase=self.id,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                allow_deterministic_ready=True,
            )
        rescue_id = str(getattr(rescue, "node_id", "") or "")
        rescue_status = str(getattr(rescue, "status", "") or "")
        rescue_generation = int(
            (getattr(rescue, "metadata", {}) or {}).get(
                "route_missing_assembly_bridge_rescue_generation",
                -1,
            )
            or -1
        )
        rescue_novel = bool(
            rescue_id
            and (
                rescue_id != prior_rescue_id
                or rescue_generation != prior_generation
                or (
                    prior_status in {"blocked", "failed", "obsolete", "rejected"}
                    and rescue_status == "open"
                )
            )
        )
        verdict = (
            "route_root_tactic_failed_rescue_materialized"
            if rescue_novel
            else "route_root_tactic_failed_rescue_already_current"
        )
        graph.record_attempt(
            route_id,
            phase=self.id,
            turn_index=int(getattr(session, "iteration", 0) or 0),
            proof=json.dumps({"route_id": route_id, "dependency_node_ids": deps}, sort_keys=True),
            verdict=verdict,
            error_type=failure_verdict,
            metadata={
                "dependency_node_ids": list(deps),
                "helper_names": list(helper_names),
                "route_assembly_contract_status": dict(contract_status),
                "route_missing_assembly_bridge_rescue_materialized": bool(rescue_id),
                "route_missing_assembly_bridge_rescue_obligation_id": rescue_id,
            },
        )
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            progress=rescue_novel,
            cost_seconds=time.monotonic() - started,
            metadata={
                "verdict": verdict,
                "route_id": route_id,
                "dependency_node_ids": list(deps),
                "helper_names": list(helper_names),
                "route_missing_assembly_bridge_rescue_materialized": bool(rescue_id),
                "route_missing_assembly_bridge_rescue_obligation_id": rescue_id,
                "preserve_frontier_work": False,
                "graph_work_consumed_verdict": verdict,
                "graph_work_consumed_error_type": failure_verdict,
            },
        )

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.proof_graph import graph_text_hash

        started = time.monotonic()
        graph = getattr(getattr(session, "dossier", None), "proof_graph", None)
        item = self._selected_item(session)
        route_id = self._route_id_from_item(item)
        if graph is None or not route_id:
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={"verdict": "missing_route"},
            )
        ready, deps = self._route_ready(
            graph,
            route_id,
            target_statement=self._session_goal_statement(session),
        )
        if not ready:
            contract_status = self._route_contract_status(
                graph,
                route_id,
                target_statement=self._session_goal_statement(session),
            )
            increment = getattr(
                getattr(session, "dossier", None),
                "increment_tool_metric",
                None,
            )
            if callable(increment):
                try:
                    increment("mini_session_graph_route_contract_blocked", 1)
                except Exception:
                    pass
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": "route_not_ready",
                    "route_id": route_id,
                    "route_contract_verdict": str(
                        contract_status.get("verdict") or ""
                    ),
                    "dependency_node_ids": list(
                        contract_status.get("dependency_node_ids") or []
                    ),
                },
            )
        proof_payload = {
            "route_id": route_id,
            "dependency_node_ids": deps,
        }
        route = graph.nodes[route_id]
        helper_names = self._route_helper_names(graph, deps, session.dossier)
        contract_status = self._route_contract_status(
            graph,
            route_id,
            target_statement=self._session_goal_statement(session),
        )
        executable_root_tactic_available = bool(
            helper_names
            and self.root_tactic_timeout_s > 0.0
            and self.root_tactic_max_candidates > 0
            and getattr(session, "lean", None) is not None
        )
        if (
            helper_names
            and self._route_requires_authored_formalization_glue(contract_status)
            and self._authoring_fallback_available(session)
        ):
            return self._request_authoring_without_tactic(
                graph=graph,
                route=route,
                route_id=route_id,
                deps=list(deps),
                helper_names=list(helper_names),
                contract_status=dict(contract_status),
                session=session,
                started=started,
            )
        if (
            not bool(contract_status.get("deterministic_ready"))
            and not executable_root_tactic_available
        ):
            if helper_names and self._authoring_fallback_available(session):
                return self._request_authoring_without_tactic(
                    graph=graph,
                    route=route,
                    route_id=route_id,
                    deps=list(deps),
                    helper_names=list(helper_names),
                    contract_status=dict(contract_status),
                    session=session,
                    started=started,
                )
            dependency_signature = self._route_dependency_signature(
                graph,
                deps,
                route_id=route_id,
            )
            signature_hash_getter = getattr(graph, "route_dependency_signature_hash", None)
            if callable(signature_hash_getter):
                try:
                    route_dependency_signature_hash = str(
                        signature_hash_getter(route_id) or ""
                    ).strip()
                except Exception:
                    route_dependency_signature_hash = ""
            else:
                route_dependency_signature_hash = ""
            if not route_dependency_signature_hash:
                route_dependency_signature_hash = graph_text_hash(
                    json.dumps(dependency_signature, sort_keys=True)
                )
            proof_hash = graph_text_hash(
                json.dumps(
                    {
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "dependency_signature": dependency_signature,
                        "route_contract_verdict": str(
                            contract_status.get("verdict") or ""
                        ),
                        "route_assembly_mode": "authoring_missing_bridge",
                    },
                    sort_keys=True,
                )
            )
            authoring_suppressed = bool(
                route_dependency_signature_hash
                and self._authoring_fallback_available(session)
            )
            verdict = "route_missing_assembly_bridge"
            route.metadata["route_missing_assembly_bridge_signature_hash"] = (
                route_dependency_signature_hash
            )
            route.metadata.pop("route_root_tactic_authoring_ready_hash", None)
            route.metadata.pop(
                "route_root_tactic_authoring_ready_signature_hash",
                None,
            )
            route.metadata.pop("route_root_tactic_authoring_helper_names", None)
            route.metadata.pop("route_root_tactic_helper_names", None)
            if authoring_suppressed:
                route.metadata[
                    "route_root_tactic_authoring_suppressed_reason"
                ] = "missing_replayable_assembly_bridge"
            rescue_obligation_id = ""
            rescue_replan_id = ""
            ensure_rescue = getattr(
                graph,
                "ensure_route_missing_assembly_bridge_rescue",
                None,
            )
            if callable(ensure_rescue):
                try:
                    rescue = ensure_rescue(
                        route_id,
                        contract_status,
                        signature_hash=route_dependency_signature_hash,
                        phase=self.id,
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                    )
                except Exception as exc:
                    route.metadata.pop(
                        "route_missing_assembly_bridge_signature_hash",
                        None,
                    )
                    route.metadata[
                        "route_missing_assembly_bridge_rescue_error"
                    ] = f"{type(exc).__name__}: {exc}"
                    rescue = None
                if rescue is not None:
                    rescue_obligation_id = str(getattr(rescue, "node_id", "") or "")
                    rescue_replan_id = str(
                        (getattr(route, "metadata", {}) or {}).get(
                            "route_missing_assembly_bridge_rescue_replan_id"
                        )
                        or ""
                    )
            graph.record_attempt(
                route_id,
                phase=self.id,
                turn_index=int(getattr(session, "iteration", 0) or 0),
                proof=json.dumps(proof_payload, sort_keys=True),
                verdict=verdict,
                error_type="route_missing_assembly_bridge",
                metadata={
                    "dependency_node_ids": list(deps),
                    "helper_names": list(helper_names),
                    "route_assembly_contract_status": dict(contract_status),
                    "route_root_tactic_authoring_ready_hash": "",
                    "route_root_tactic_authoring_ready_signature_hash": "",
                    "route_root_tactic_authoring_suppressed": authoring_suppressed,
                    "route_root_tactic_authoring_suppressed_reason": (
                        "missing_replayable_assembly_bridge"
                        if authoring_suppressed
                        else ""
                    ),
                    "route_missing_assembly_bridge_rescue_materialized": bool(
                        rescue_obligation_id
                    ),
                    "route_missing_assembly_bridge_rescue_obligation_id": (
                        rescue_obligation_id
                    ),
                    "route_missing_assembly_bridge_rescue_replan_id": (
                        rescue_replan_id
                    ),
                    "selected_work_item": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                },
            )
            increment = getattr(
                getattr(session, "dossier", None),
                "increment_tool_metric",
                None,
            )
            if callable(increment):
                try:
                    increment(
                        "mini_session_graph_route_missing_assembly_bridge",
                        1,
                    )
                    if authoring_suppressed:
                        increment(
                            "mini_session_graph_route_authoring_missing_bridge_suppressed",
                            1,
                        )
                except Exception:
                    pass
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                progress=False,
                cost_seconds=time.monotonic() - started,
                metadata={
                    "verdict": verdict,
                    "route_id": route_id,
                    "dependency_node_ids": list(deps),
                    "helper_names": list(helper_names),
                    "route_contract_verdict": str(
                        contract_status.get("verdict") or ""
                    ),
                    "route_assembly_contract_status": dict(contract_status),
                    "route_root_tactic_authoring_suppressed": authoring_suppressed,
                    "route_root_tactic_authoring_suppressed_reason": (
                        "missing_replayable_assembly_bridge"
                        if authoring_suppressed
                        else ""
                    ),
                    "route_missing_assembly_bridge_rescue_materialized": bool(
                        rescue_obligation_id
                    ),
                    "route_missing_assembly_bridge_rescue_obligation_id": (
                        rescue_obligation_id
                    ),
                    "route_missing_assembly_bridge_rescue_replan_id": (
                        rescue_replan_id
                    ),
                    "strong_progress": False,
                    "graph_route_assembled": False,
                    "preserve_frontier_work": False,
                    "graph_work_consumed_verdict": verdict,
                    "graph_work_consumed_error_type": "route_missing_assembly_bridge",
                    "selected_work_item": dict(
                        getattr(session, "selected_work_item_record", {}) or {}
                    ),
                },
            )
        if not helper_names:
            return self._no_replayable_helpers_outcome(
                graph=graph,
                route_id=route_id,
                deps=deps,
                session=session,
                started=started,
            )
        if bool(contract_status.get("deterministic_ready")):
            cases_outcome = await self._try_branch_cases_assembly(
                graph=graph,
                route_id=route_id,
                deps=deps,
                session=session,
                contract_status=dict(contract_status),
                route_helper_names=list(helper_names),
                started=started,
            )
            if cases_outcome is not None:
                return cases_outcome
        if helper_names and not executable_root_tactic_available:
            if self._authoring_fallback_available(session):
                return self._request_authoring_without_tactic(
                    graph=graph,
                    route=route,
                    route_id=route_id,
                    deps=list(deps),
                    helper_names=list(helper_names),
                    contract_status=dict(contract_status),
                    session=session,
                    started=started,
                )
            return self._materialize_failed_route_rescue(
                graph=graph,
                route_id=route_id,
                deps=list(deps),
                helper_names=list(helper_names),
                contract_status=dict(contract_status),
                session=session,
                started=started,
                failure_verdict="route_root_tactic_unavailable",
            )
        if (
            helper_names
            and self.root_tactic_timeout_s > 0.0
            and self.root_tactic_max_candidates > 0
            and getattr(session, "lean", None) is not None
        ):
            from ensemble_prover.mini_prover import _try_root_tactic_close
            from ensemble_prover.proof_state_executor import _root_tactic_context_key

            goal_statement = self._session_goal_statement(session)
            preamble = (
                session.acceptance_preamble()
                if hasattr(session, "acceptance_preamble")
                else str(getattr(getattr(session, "conv", None), "preamble", "") or "")
            )
            helper_blocks = self._route_helper_blocks(
                session.dossier,
                helper_names,
                allow_hidden_helper_names=helper_names,
            )
            root_tactic_context_key = _root_tactic_context_key(
                goal_statement=goal_statement,
                preamble=preamble,
                helpers=helper_blocks,
                timeout_s=self.root_tactic_timeout_s,
                max_candidates=self.root_tactic_max_candidates,
            )
            proof_hash = graph_text_hash(
                json.dumps(
                    {
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "dependency_signature": self._route_dependency_signature(
                            graph,
                            deps,
                            route_id=route_id,
                        ),
                        "root_tactic_context_key": root_tactic_context_key,
                    },
                    sort_keys=True,
                )
            )
            route_dependency_signature_hash = ""
            signature_hash_getter = getattr(graph, "route_dependency_signature_hash", None)
            if callable(signature_hash_getter):
                try:
                    route_dependency_signature_hash = str(
                        signature_hash_getter(route_id) or ""
                    ).strip()
                except Exception:
                    route_dependency_signature_hash = ""
            retry_after_defer = bool(
                route.metadata.get("route_root_tactic_deferred_hash") == proof_hash
                and route.metadata.get("route_root_tactic_continued_hash")
                != proof_hash
            )
            suppressed_proofs = self._route_root_tactic_suppressed_proofs(
                route,
                proof_hash,
            )
            suppressed_proof_records = self._route_root_tactic_suppressed_proof_records(
                route,
                proof_hash,
            )
            excluded_source_prefixes = excluded_tactic_source_prefixes_for_context(
                session,
                goal_statement=goal_statement,
                helper_blocks=helper_blocks,
            )
            try:
                ok, proof = await _try_root_tactic_close(
                    phase="graph_route_assembly_root_tactic",
                    theorem_name=str(getattr(session.dossier, "theorem_name", "") or ""),
                    goal_statement=goal_statement,
                    preamble=preamble,
                    lean=session.lean,
                    dossier=session.dossier,
                    recorder=getattr(session, "recorder", None),
                    trace_prefix=str(getattr(session, "trace_prefix", "") or ""),
                    timeout_s=self.root_tactic_timeout_s,
                    max_candidates=self.root_tactic_max_candidates,
                    helper_blocks=helper_blocks,
                    finalize_root=False,
                    excluded_source_prefixes=excluded_source_prefixes,
                    suppressed_proofs=(
                        suppressed_proofs if not suppressed_proof_records else ()
                    ),
                    suppressed_proof_records=suppressed_proof_records,
                    tactic_source_suppression_records=tactic_source_suppression_records(
                        session
                    ),
                    tactic_source_suppression_helper_blocks=helper_blocks,
                )
            except Exception as exc:
                route.metadata["route_root_tactic_helper_names"] = list(helper_names)
                if not retry_after_defer:
                    route.metadata["route_root_tactic_deferred_hash"] = proof_hash
                    verdict = "route_root_tactic_exception_deferred"
                    preserve_frontier = True
                else:
                    route.metadata["route_root_tactic_continued_hash"] = proof_hash
                    route.metadata["route_root_tactic_failed_hash"] = proof_hash
                    if route_dependency_signature_hash:
                        route.metadata["route_root_tactic_failed_signature_hash"] = (
                            route_dependency_signature_hash
                        )
                    verdict = "route_root_tactic_exception"
                    preserve_frontier = False
                graph.record_attempt(
                    route_id,
                    phase=self.id,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    proof=json.dumps(proof_payload, sort_keys=True),
                    verdict=verdict,
                    metadata={
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "exception_type": type(exc).__name__,
                        "exception_message": str(exc),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
                if preserve_frontier:
                    return MiniOutcome(
                        action_id=self.id,
                        solved=False,
                        proof=None,
                        progress=False,
                        cost_seconds=time.monotonic() - started,
                        metadata={
                            "verdict": verdict,
                            "route_id": route_id,
                            "dependency_node_ids": list(deps),
                            "helper_names": list(helper_names),
                            "preserve_frontier_work": True,
                            "graph_work_consumed_verdict": verdict,
                            "graph_work_consumed_error_type": verdict,
                            "exception_type": type(exc).__name__,
                            "exception_message": str(exc),
                            "selected_work_item": dict(
                                getattr(session, "selected_work_item_record", {}) or {}
                            ),
                        },
                    )
                # The retry was exhausted. Continue through the ordinary
                # author-or-rescue fallback below instead of consuming the
                # route as a terminal infrastructure failure.
                ok, proof = False, ""
            if ok and proof:
                self._clear_route_root_tactic_continuation(route)
                route_contract_status: dict[str, Any] = {}
                status_getter = getattr(graph, "route_assembly_contract_status", None)
                if callable(status_getter):
                    try:
                        route_contract_status = dict(
                            status_getter(
                                route_id,
                                target_statement=goal_statement,
                            )
                            or {}
                        )
                    except Exception:
                        route_contract_status = {}
                if not bool(route_contract_status.get("ready")):
                    graph.record_attempt(
                        route_id,
                        phase=self.id,
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        proof=json.dumps(proof_payload, sort_keys=True),
                        verdict="route_root_tactic_finalization_contract_not_ready",
                        metadata={
                            "dependency_node_ids": list(deps),
                            "helper_names": list(helper_names),
                            "route_assembly_contract_status": route_contract_status,
                            "selected_work_item": dict(
                                getattr(session, "selected_work_item_record", {}) or {}
                            ),
                        },
                    )
                    return MiniOutcome(
                        action_id=self.id,
                        solved=False,
                        proof=None,
                        progress=False,
                        cost_seconds=time.monotonic() - started,
                        metadata={
                            "verdict": "route_root_tactic_finalization_contract_not_ready",
                            "route_id": route_id,
                            "dependency_node_ids": list(deps),
                            "helper_names": list(helper_names),
                            "route_contract_verdict": str(
                                route_contract_status.get("verdict") or ""
                            ),
                            "preserve_frontier_work": True,
                            "selected_work_item": dict(
                                getattr(session, "selected_work_item_record", {}) or {}
                            ),
                        },
                    )
                route.metadata["assembled_dependency_node_ids"] = list(deps)
                route.metadata["assembled_by_action"] = self.id
                route.metadata["assembled_route_proof_hash"] = proof_hash
                if route_dependency_signature_hash:
                    route.metadata["assembled_dependency_signature_hash"] = (
                        route_dependency_signature_hash
                    )
                route.metadata["route_root_tactic_helper_names"] = list(helper_names)
                replay_helper_names = self._replay_helper_names(helper_blocks)
                graph.record_attempt(
                    route_id,
                    phase=self.id,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    proof=json.dumps(proof_payload, sort_keys=True),
                    verdict="route_root_tactic_solved",
                    metadata={
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "replay_helper_names": list(replay_helper_names),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
                return MiniOutcome(
                    action_id=self.id,
                    solved=True,
                    proof=proof,
                    progress=True,
                    cost_seconds=time.monotonic() - started,
                    root_candidate=RootFinalizationCandidate(
                        proof=proof,
                        replay_helpers=tuple(helper_blocks),
                        helper_names=replay_helper_names,
                        phase=self.id,
                        turn_index=int(getattr(session, "iteration", 0) or 0),
                        source_action_id=self.id,
                        route_id=route_id,
                        dependency_node_ids=tuple(deps),
                        dependency_helper_names=tuple(helper_names),
                        target_statement=goal_statement,
                        require_route_contract=True,
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=proof,
                            phase=self.id,
                            turn_index=int(getattr(session, "iteration", 0) or 0),
                            target_statement=goal_statement,
                            replay_helpers=tuple(helper_blocks),
                            helper_names=replay_helper_names,
                            source="graph_route_assembly",
                        ),
                    ),
                    metadata={
                        "verdict": "route_root_tactic_solved",
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "strong_progress": True,
                        "graph_route_assembled": True,
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
            last_root_tactic_record = self._last_root_tactic_record(session)
            transient_failure = self._last_root_tactic_transient_failure(session)
            deferrable_timeout = self._last_root_tactic_deferrable_timeout(session)
            continuation_stats = self._record_route_root_tactic_attempted_proofs(
                route,
                proof_hash=proof_hash,
                record=last_root_tactic_record,
            )
            if deferrable_timeout and continuation_stats.get("added", 0) > 0:
                route.metadata["route_root_tactic_timeout_continuation_hash"] = proof_hash
                route.metadata["route_root_tactic_helper_names"] = list(helper_names)
                graph.record_attempt(
                    route_id,
                    phase=self.id,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    proof=json.dumps(proof_payload, sort_keys=True),
                    verdict="route_root_tactic_timeout_deferred",
                    metadata={
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "transient_failure": bool(transient_failure),
                        "deferrable_timeout": True,
                        "route_root_tactic_suppressed_count": int(
                            continuation_stats.get("total", 0) or 0
                        ),
                        "route_root_tactic_suppressed_added": int(
                            continuation_stats.get("added", 0) or 0
                        ),
                        "tactic_candidate_count": int(
                            last_root_tactic_record.get("tactic_candidate_count", 0)
                            or 0
                        ),
                        "tactic_attempt_count": int(
                            last_root_tactic_record.get(
                                "tactic_attempt_count",
                                len(last_root_tactic_record.get("tactic_attempts") or []),
                            )
                            or 0
                        ),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
                increment = getattr(
                    getattr(session, "dossier", None),
                    "increment_tool_metric",
                    None,
                )
                if callable(increment):
                    try:
                        increment("mini_session_graph_route_root_tactic_continued", 1)
                    except Exception:
                        pass
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    progress=True,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "verdict": "route_root_tactic_timeout_deferred",
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "preserve_frontier_work": True,
                        "transient_failure": bool(transient_failure),
                        "deferrable_timeout": True,
                        "route_root_tactic_suppressed_count": int(
                            continuation_stats.get("total", 0) or 0
                        ),
                        "route_root_tactic_suppressed_added": int(
                            continuation_stats.get("added", 0) or 0
                        ),
                        "graph_work_consumed_verdict": (
                            "route_root_tactic_timeout_deferred"
                        ),
                        "graph_work_consumed_error_type": (
                            "route_root_tactic_timeout_deferred"
                        ),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
            if transient_failure and deferrable_timeout:
                route.metadata["route_root_tactic_deferral_suppressed_hash"] = proof_hash
            authoring_available = bool(
                route_dependency_signature_hash
                and self._authoring_fallback_available(session)
            )
            if authoring_available:
                # The authoring lane now owns this signature.  A tactic-failed
                # suppression marker would make the just-created authoring work
                # unreachable in ``route_ready_for_assembly``.
                route.metadata.pop("route_root_tactic_failed_hash", None)
                route.metadata.pop("route_root_tactic_failed_signature_hash", None)
                route.metadata["route_root_tactic_authoring_ready_hash"] = proof_hash
                route.metadata["route_root_tactic_authoring_ready_signature_hash"] = (
                    route_dependency_signature_hash
                )
                route.metadata["route_root_tactic_authoring_helper_names"] = list(
                    helper_names
                )
                route.metadata["route_root_tactic_helper_names"] = list(helper_names)
                graph.record_attempt(
                    route_id,
                    phase=self.id,
                    turn_index=int(getattr(session, "iteration", 0) or 0),
                    proof=json.dumps(proof_payload, sort_keys=True),
                    verdict="route_root_tactic_failed_authoring_requested",
                    metadata={
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "transient_failure": bool(transient_failure),
                        "deferrable_timeout": bool(deferrable_timeout),
                        "route_root_tactic_authoring_ready_hash": proof_hash,
                        "route_root_tactic_authoring_ready_signature_hash": (
                            route_dependency_signature_hash
                        ),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
                increment = getattr(
                    getattr(session, "dossier", None),
                    "increment_tool_metric",
                    None,
                )
                if callable(increment):
                    try:
                        increment("mini_session_graph_route_authoring_requested", 1)
                    except Exception:
                        pass
                return MiniOutcome(
                    action_id=self.id,
                    solved=False,
                    proof=None,
                    progress=False,
                    cost_seconds=time.monotonic() - started,
                    metadata={
                        "verdict": "route_root_tactic_failed_authoring_requested",
                        "route_id": route_id,
                        "dependency_node_ids": list(deps),
                        "helper_names": list(helper_names),
                        "preserve_frontier_work": False,
                        "transient_failure": bool(transient_failure),
                        "deferrable_timeout": bool(deferrable_timeout),
                        "graph_work_consumed_verdict": (
                            "route_root_tactic_failed_authoring_requested"
                        ),
                        "graph_work_consumed_error_type": (
                            "route_root_tactic_failed_authoring_requested"
                        ),
                        "selected_work_item": dict(
                            getattr(session, "selected_work_item_record", {}) or {}
                        ),
                    },
                )
            return self._materialize_failed_route_rescue(
                graph=graph,
                route_id=route_id,
                deps=list(deps),
                helper_names=list(helper_names),
                contract_status=dict(contract_status),
                session=session,
                started=started,
                failure_verdict="route_root_tactic_failed",
            )
        return self._no_replayable_helpers_outcome(
            graph=graph,
            route_id=route_id,
            deps=deps,
            session=session,
            started=started,
        )
