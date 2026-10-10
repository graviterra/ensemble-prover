"""Explicit root planning after a bounded sequence of failed proof tools."""

from __future__ import annotations

import copy
import hashlib
import json
import re
from collections.abc import Mapping
from typing import Any

from ...mini_falsification.model import content_hash
from ...proof_dossier import canonical_dossier_statement_key
from ...research_claims.model import json_text
from ...research_claims.native_guidance import is_proof_candidate
from ...state_data import clone_json_value
from ..action import MiniOutcome
from ..planner_jobs import PlannerJobLaunch
from .recursive_controller import RecursiveControllerAction

_HELPER_EVIDENCE = re.compile(r"helper:[0-9a-f]{64}\Z")
_ARCHIVE_POINTER_FIELDS = {
    "artifact_id",
    "path",
    "coverage",
    "read_with",
    "characters",
    "control_outcomes",
}


def _validated_archive_pointer(value: Any, field: str) -> str:
    """Return the field-archive digest of a context-window pointer.

    The digest is the stored artifact id of ``json_text({field: value})``.
    Pointer metadata does not identify the field. A pointer that does not
    name this field is not that field's content.
    """

    if not isinstance(value, dict) or not set(value).issubset(_ARCHIVE_POINTER_FIELDS):
        return ""
    artifact = value.get("artifact_id")
    if (
        value.get("coverage") != "not_in_this_window"
        or value.get("read_with") != "read_artifact"
        or value.get("path") != [field]
        or not isinstance(artifact, str)
        or re.fullmatch(r"[0-9a-f]{64}", artifact) is None
    ):
        return ""
    if "characters" in value and type(value["characters"]) is not int:
        return ""
    if "control_outcomes" in value and not isinstance(value["control_outcomes"], list):
        return ""
    return artifact


def _optional_research_reservations(record: Mapping[str, Any], key: str) -> list[dict[str, Any]] | None:
    """Return parsed reservations, or None when a legacy snapshot omits them."""

    if key not in record:
        return None
    value = record.get(key)
    if not isinstance(value, list) or len(value) > 256:
        raise ValueError(f"invalid {key}")
    parsed: list[dict[str, Any]] = []
    for item in value:
        evidence = item.get("evidence") if isinstance(item, dict) else None
        advice_key = item.get("advice_key") if isinstance(item, dict) else None
        if (
            not isinstance(advice_key, str)
            or re.fullmatch(r"[0-9a-f]{64}", advice_key) is None
            or not isinstance(evidence, list)
            or len(evidence) > 4096
            or any(
                not isinstance(text, str) or _HELPER_EVIDENCE.fullmatch(text) is None
                for text in evidence
            )
        ):
            raise ValueError(f"invalid {key}")
        parsed.append({"advice_key": advice_key, "evidence": list(evidence)})
    return parsed


class GraphRootReplanAction(RecursiveControllerAction):
    """Use the graph pass pool while keeping the flat proof turn suspended."""

    id = "graph_root_replan"
    _STALL_TOOL_ATTEMPTS = 3
    FAILED_DISPATCH_ROLLBACK_STATE_FIELDS = (
        RecursiveControllerAction.FAILED_DISPATCH_ROLLBACK_STATE_FIELDS
        | frozenset({"_active_replan_identity"})
    )
    _SETTINGS = (
        "config", "run_conversation_fn", "max_tool_calls_per_turn",
        "lean_check_tool_enabled", "try_lean_tool_enabled",
        "compute_examples_tool_enabled", "apply_decl_to_goal_tool_enabled",
        "raw_feedback", "repair_retrieval_enabled", "repair_retrieval_top_k",
        "proof_state_child_tactics_enabled", "proof_state_child_tactic_timeout_s",
        "proof_state_child_tactic_max_candidates", "root_tactic_timeout_s",
        "root_tactic_max_candidates", "proof_state_child_goal_limit",
        "proof_state_decl_application_limit", "proof_state_batch_parallelism",
    )

    def __init__(self, *, source_action: Any) -> None:
        super().__init__(
            action_id=self.id,
            priority=21,
            phase_label="[root replanning after proof-tool stall]",
            budget_attr="graph_recursive_decompose_remaining",
            **{name: getattr(source_action, name) for name in self._SETTINGS},
        )
        self._pending_replan_request: dict[str, Any] = {}
        self._served_replan_requests: list[str] = []
        self._served_research_reservations: list[dict[str, Any]] = []
        self._ancestor_research_reservations: list[dict[str, Any]] = []
        self._active_replan_identity = ""

    @staticmethod
    def _context_identity(session: Any) -> str:
        return content_hash((
            str(session.problem.statement_type or ""),
            str(session.acceptance_preamble() or ""),
            tuple(session._durable_formal_progress_evidence()),
        ))

    @staticmethod
    def _validated_research_guidance(guidance: Any) -> dict[str, Any]:
        value = clone_json_value(guidance, label="native research planner guidance")
        if (not isinstance(value, dict) or value.get("kernel_verified") is not False
                or not isinstance(value.get("artifact_id"), str)
                or re.fullmatch(r"[0-9a-f]{64}", value["artifact_id"]) is None
                or len(json.dumps(value, ensure_ascii=False, allow_nan=False)) > 14000):
            raise ValueError("invalid or unbounded native research planner guidance")
        return value

    @staticmethod
    def _research_advice_parts(advice: Mapping[str, Any]) -> tuple[Any, Any, Any]:
        """Return target, context, and action without the delivery artifact id."""

        nested = advice.get("advice")
        source = nested if isinstance(nested, dict) else advice
        action = source.get("action") if isinstance(source, dict) else None
        if not isinstance(action, dict) and isinstance(advice.get("action"), dict):
            action = advice.get("action")
        target = source.get("target_statement") if isinstance(source, dict) else None
        context = source.get("target_context_binding") if isinstance(source, dict) else None
        if target is None:
            target = advice.get("target_statement")
        if context is None:
            context = advice.get("target_context_binding")
        return target, context, action if isinstance(action, dict) else None

    def _canonical_field_identity(self, field: str, value: Any) -> str:
        """Identify one advice field independent of context-window presentation.

        An inline value and its archive pointer both hash
        ``json_text({field: value})``. A missing or unvalidated field has no
        identity. Callers refuse that advice instead of tracking a digest
        they cannot recompute.
        """

        pointer = _validated_archive_pointer(value, field)
        if pointer:
            return pointer
        if isinstance(value, dict) and value.get("coverage") == "not_in_this_window":
            return ""
        try:
            encoded = json_text({field: value}).encode()
        except (TypeError, ValueError):
            return ""
        return hashlib.sha256(encoded).hexdigest()

    def _advice_key(self, environment: str, advice: Mapping[str, Any]) -> str:
        """Identify advice without its delivery artifact or local graph ids.

        The paid request identity still names the artifact. This key only
        decides whether a later delivery is the same plan. It is computed
        from the complete target, context, and action, including when a
        context window has replaced one of those fields with an archive
        pointer.
        """

        target, context, action = self._research_advice_parts(advice)
        if action is None or not environment:
            return ""
        action_id = self._canonical_field_identity("action", action)
        target_id = self._canonical_field_identity("target_statement", target)
        context_id = self._canonical_field_identity("target_context_binding", context)
        if not action_id or not target_id or not context_id:
            return ""
        return content_hash((
            "native_research_advice",
            environment,
            target_id,
            context_id,
            action_id,
        ))

    def _inherited_checked_evidence(self, session: Any) -> tuple[str, ...]:
        """Return helper evidence a child dossier actually inherits.

        Proved proof-state nodes and rebuilt graph ids are local. A missing,
        smaller, or reordered copy of the inherited helper set is not new
        checked progress. A helper that was not in the reserved set is.
        """

        from ..progress_identity import helper_progress_keys

        keys = helper_progress_keys(getattr(session, "dossier", None))
        return tuple(sorted({
            f"helper:{value}"
            for value in keys.values()
            if isinstance(value, str) and value
        }))

    def _note_unstarted_research_context(self, session: Any) -> None:
        """Record the latest helper context for a request that has not started.

        Dispatch keeps that snapshot. Helpers added earlier are part of the
        planner input; helpers added after dispatch stay outside it.
        """

        request = self._pending_replan_request
        advice = request.get("native_research")
        if not isinstance(advice, dict):
            return
        if self._active_replan_identity == request.get("request_identity"):
            return
        environment = str(request.get("root_environment_identity") or "")
        advice_key = self._advice_key(environment, advice)
        if advice_key:
            request["research_advice_key"] = advice_key
        request["research_evidence"] = list(self._inherited_checked_evidence(session))

    def _reservation_item_covers(
        self,
        item: Mapping[str, Any],
        advice_key: str,
        observed: set[str],
    ) -> bool:
        if item.get("advice_key") != advice_key:
            return False
        reserved = {
            text
            for text in item.get("evidence") or ()
            if isinstance(text, str)
        }
        return observed <= reserved

    def _reservation_covers(
        self,
        advice_key: str,
        evidence: tuple[str, ...],
        session: Any = None,
    ) -> bool:
        if not advice_key:
            return False
        observed = set(evidence)
        for item in (
            *self._served_research_reservations,
            *self._ancestor_research_reservations,
        ):
            if self._reservation_item_covers(item, advice_key, observed):
                return True
        # The serialized ancestor list is bounded. Live in-flight advice is
        # not: every active ancestor still blocks its own advice.
        current = getattr(session, "parent", None)
        seen: set[int] = set()
        while current is not None and id(current) not in seen:
            seen.add(id(current))
            getter = getattr(current, "registered_action", None)
            action = getter("graph_root_replan") if callable(getter) else None
            if action is not None:
                pending = getattr(action, "_pending_replan_request", {}) or {}
                in_flight = (
                    getattr(action, "_active_replan_identity", "")
                    == pending.get("request_identity")
                )
                derived = (
                    self._ancestor_reservation_from_pending(action, current)
                    if in_flight
                    else None
                )
                if derived is not None and self._reservation_item_covers(
                    derived, advice_key, observed
                ):
                    return True
            current = getattr(current, "parent", None)
        return False

    def research_delivery_binding(
        self,
        session: Any,
        guidance: Mapping[str, Any],
    ) -> tuple[str, str, tuple[str, ...]]:
        """Identify a delivery by semantic advice and helper evidence.

        The artifact id is not the identity. A changed checker environment
        changes this binding even when the research action text is unchanged.
        """

        problem = getattr(session, "problem", None)
        root = str(getattr(problem, "statement_type", "") or "").strip()
        preamble_fn = getattr(session, "acceptance_preamble", None)
        preamble = preamble_fn() if callable(preamble_fn) else ""
        environment = content_hash((root, preamble))
        advice_key = self._advice_key(environment, guidance)
        evidence = self._inherited_checked_evidence(session)
        if advice_key:
            return ("advice", advice_key, evidence)
        return ("artifact", str(guidance.get("artifact_id") or ""), evidence)

    def _ancestor_reservation_from_pending(
        self,
        action: Any,
        session: Any,
    ) -> dict[str, Any] | None:
        pending = getattr(action, "_pending_replan_request", {}) or {}
        advice = pending.get("native_research")
        if not isinstance(advice, dict):
            return None
        environment = str(pending.get("root_environment_identity") or "")
        advice_key = str(pending.get("research_advice_key") or "")
        if not advice_key:
            advice_key = self._advice_key(environment, advice)
        if not advice_key:
            return None
        active = (
            getattr(action, "_active_replan_identity", "")
            == pending.get("request_identity")
        )
        stored = pending.get("research_evidence")
        if active and isinstance(stored, list):
            evidence = tuple(text for text in stored if isinstance(text, str))
        else:
            evidence = self._inherited_checked_evidence(session)
        return {"advice_key": advice_key, "evidence": list(evidence)}

    def inherit_research_replan_ancestry(self, session: Any) -> None:
        """Reserve advice an ancestor has consumed or still has in flight.

        Child sessions are built before the ancestor can record the replan as
        served. The reservation is the advice plus the helper context the
        child inherits. A local proof-state fact that the child does not
        receive does not authorize another plan. In-flight advice is kept
        ahead of older served history when the retained list is bounded.
        """

        active: list[dict[str, Any]] = []
        history: list[dict[str, Any]] = []
        seen_active: set[tuple[str, tuple[str, ...]]] = set()
        seen_history: set[tuple[str, tuple[str, ...]]] = set()

        def add(
            bucket: list[dict[str, Any]],
            seen: set[tuple[str, tuple[str, ...]]],
            item: Mapping[str, Any],
        ) -> None:
            advice_key = str(item.get("advice_key") or "")
            evidence = tuple(
                text for text in item.get("evidence") or () if isinstance(text, str)
            )
            if not advice_key:
                return
            identity = (advice_key, evidence)
            if identity in seen:
                return
            seen.add(identity)
            bucket.append({"advice_key": advice_key, "evidence": list(evidence)})

        current = getattr(session, "parent", None)
        while current is not None:
            getter = getattr(current, "registered_action", None)
            action = getter("graph_root_replan") if callable(getter) else None
            if action is not None:
                pending = getattr(action, "_pending_replan_request", {}) or {}
                derived = self._ancestor_reservation_from_pending(action, current)
                if (
                    derived is not None
                    and getattr(action, "_active_replan_identity", "")
                    == pending.get("request_identity")
                ):
                    add(active, seen_active, derived)
                elif derived is not None:
                    add(history, seen_history, derived)
                for item in (
                    *getattr(action, "_served_research_reservations", ()),
                    *getattr(action, "_ancestor_research_reservations", ()),
                ):
                    if isinstance(item, Mapping):
                        add(history, seen_history, item)
            current = getattr(current, "parent", None)
        # Keep the nearest in-flight advice even when older served history
        # fills the checkpoint bound. History fills only the remaining slots.
        kept: list[dict[str, Any]] = []
        seen: set[tuple[str, tuple[str, ...]]] = set()
        for source in (active, history):
            for item in source:
                identity = (
                    str(item.get("advice_key") or ""),
                    tuple(item.get("evidence") or ()),
                )
                if identity in seen:
                    continue
                seen.add(identity)
                kept.append(item)
                if len(kept) >= 256:
                    break
            if len(kept) >= 256:
                break
        self._ancestor_research_reservations = kept

    def request_research_replan(self, session: Any, guidance: dict[str, Any]) -> bool:
        """Queue advisory material for the original root using existing passes.

        A committed/pending planner retains its exact request. Its owner can
        retry delivery after publication; research never replaces paid work.
        """
        advice = self._validated_research_guidance(guidance)
        # A plain refusal is deferred. Only acceptance, or an exact advice
        # and helper context that is already reserved, is consumed.
        self._last_research_replan_disposition = "deferred"
        _, _, action = self._research_advice_parts(advice)
        archived_action = _validated_archive_pointer(action, "action")
        candidate = is_proof_candidate(action) or bool(
            archived_action
            and advice.get("proof_candidate_action_id") == archived_action
        )
        if not candidate:
            self._last_research_replan_disposition = "context_only"
            return False
        budget = session.budgets.get(self.id)
        if (session.root_finalized or session.terminal_failure_reason
                or session._run_governor_exhausted()
                or self._pending_replan_request or self._active_replan_identity
                or self._pending_planner_job_launch is not None
                or self._recursive_driver_state.get("phase") == "planner_job_pending"
                or self.id in getattr(session, "recursive_inflight_reservations", {})
                or (budget is not None and budget.exhausted())
                or int(getattr(session, self.budget_attr, 0) or 0) == 0
                or self.run_conversation_fn is None
                or not getattr(session.conv, "allow_helper_decomposition", True)):
            return False
        root = str(session.problem.statement_type or "").strip()
        if not root or session.dossier is None:
            return False
        environment = content_hash((root, session.acceptance_preamble()))
        identity = content_hash(("native_research", environment, advice["artifact_id"]))
        advice_key = self._advice_key(environment, advice)
        # Advice that cannot be identified must not become an untracked retry.
        if not advice_key:
            return False
        evidence = self._inherited_checked_evidence(session)
        if self._reservation_covers(advice_key, evidence, session):
            self._last_research_replan_disposition = "covered"
            return False
        # A served artifact stays consumed until a reservation shows that the
        # helper context grew. Missing legacy reservations cannot be inverted
        # from the artifact hash, so the paid identity still refuses a retry.
        if identity in self._served_replan_requests and not any(
            item.get("advice_key") == advice_key
            for item in self._served_research_reservations
        ):
            self._last_research_replan_disposition = "covered"
            return False
        self._pending_replan_request = {
            "node_id": str(session.dossier.proof_graph.root_node_id),
            "work_type": "root_replan", "source": "root_replan",
            "target_statement": root, "exact_target_statement": root,
            "context_identity": self._context_identity(session),
            "root_environment_identity": environment,
            "request_identity": identity, "owner_action_id": "native_research",
            "stalled_tool_attempts": 0, "diagnostic_kind": "research_alternative",
            "native_research": advice,
            **({"research_advice_key": advice_key} if advice_key else {}),
            "research_evidence": list(evidence),
        }
        session._record_event({
            "phase": "session_root_replanning", "iteration": session.iteration,
            "verdict": "research_root_replan_requested", "kernel_verified": False,
            "research_artifact_id": advice["artifact_id"], "request_identity": identity,
        })
        self._last_research_replan_disposition = "accepted"
        return True

    def _session_progress_signature(self, session: Any) -> str:
        signature = super()._session_progress_signature(session)
        advice = self._pending_replan_request.get("native_research")
        if advice:
            # New advisory work changes the planner's input, not the formal
            # progress ledger. No other action's fixed point is reopened.
            return content_hash((signature, "native_research", advice["artifact_id"]))
        return signature

    def _planner_problem_text(self, session: Any) -> str:
        original = super()._planner_problem_text(session)
        advice = self.selected_replan_work(session).get("native_research")
        if not advice:
            return original
        return original + (
            "\n\nUntrusted research advice for the ORIGINAL root:\n"
            "Check the disputed inference and source hypotheses; construct a concrete "
            "alternative plan. This is not a theorem, assumption, or proof certificate. "
            "Archived fields are uninspected. Proof conversations can use "
            "read_native_research_artifact for complete arguments; identify any "
            "source check still required before relying on the advice.\n"
            + json.dumps(advice, ensure_ascii=False, allow_nan=False)
        )

    def observe_proof_outcome(
        self, session: Any, outcome: MiniOutcome, *, formal_progress: bool,
        sustained_helper_progress: bool = False,
    ) -> None:
        if (
            self._pending_replan_request
            and not self._active_replan_identity
            and not self.selected_replan_work(session)
        ):
            self._pending_replan_request = {}
        if (
            (formal_progress and not sustained_helper_progress)
            or outcome.solved or outcome.exception is not None
        ):
            return
        if not outcome.action_id.startswith("conversation_turn"):
            return
        record = dict(session.selected_work_item_record or {})
        if record and session.selected_work_item_action_id != outcome.action_id:
            return
        if record and record.get("work_type") not in {"root_repair", "assemble_route"}:
            return
        root = str(session.problem.statement_type or "").strip()
        target = str(
            record.get("exact_target_statement") or record.get("target_statement")
            or getattr(session.conv, "goal_statement", "") or ""
        ).strip()
        if not root or canonical_dossier_statement_key(target) != canonical_dossier_statement_key(root):
            return
        metadata = outcome.metadata
        if (
            session._persistent_infrastructure_defer(metadata)
            or metadata.get("paid_tool_infrastructure_disposition")
            or int(metadata.get("provider_calls_completed", 0) or 0) <= 0
            or (
                not sustained_helper_progress
                and int(metadata.get("semantic_diagnostic_best_phase", -1)) < 0
            )
        ):
            return
        attempts = int(metadata.get("proof_tool_attempts", 0) or 0)
        stalled = int(metadata.get("consecutive_no_formal_progress", 0) or 0)
        if not sustained_helper_progress and (
            stalled < self._STALL_TOOL_ATTEMPTS or attempts < self._STALL_TOOL_ATTEMPTS
        ):
            return
        context = self._context_identity(session)
        identity = content_hash(
            (
                context, "sustained_helper_progress",
                session.helper_only_progress_identity,
                int(session.helper_only_provider_quanta),
            )
            if sustained_helper_progress else (
                context, outcome.action_id,
                int(metadata.get("conv_turn_index_absolute", 0) or 0),
                attempts // self._STALL_TOOL_ATTEMPTS,
            )
        )
        if identity in self._served_replan_requests or self._pending_replan_request:
            return
        self._pending_replan_request = {
            "node_id": str(session.dossier.proof_graph.root_node_id),
            "work_type": "root_replan",
            "source": "root_replan",
            "target_statement": root,
            "exact_target_statement": root,
            "context_identity": context,
            "root_environment_identity": content_hash((root, session.acceptance_preamble())),
            "request_identity": identity,
            "owner_action_id": outcome.action_id,
            "stalled_tool_attempts": stalled,
            "diagnostic_kind": str(metadata.get("semantic_diagnostic_best_error_kind") or ""),
            "sustained_helper_progress": sustained_helper_progress,
            "helper_only_progress_identity": (
                session.helper_only_progress_identity if sustained_helper_progress else ""
            ),
        }
        session._record_event({
            "phase": "session_root_replanning",
            "iteration": session.iteration,
            "verdict": "root_replan_requested",
            "selected_work_item": copy.deepcopy(self._pending_replan_request),
        })

    def selected_replan_work(self, session: Any) -> dict[str, Any]:
        request = self._pending_replan_request
        if not request:
            return {}
        if request.get("target_statement") != str(session.problem.statement_type or "").strip():
            return {}
        if request.get("root_environment_identity") != content_hash((
            str(session.problem.statement_type or "").strip(), session.acceptance_preamble(),
        )):
            return {}
        active = self._active_replan_identity == request.get("request_identity")
        if not active and request.get("native_research"):
            # Applicability is read-only. The returned selection shows the
            # helper context dispatch would freeze; the stored request changes
            # only when run() starts the planner.
            selected = copy.deepcopy(request)
            advice = selected.get("native_research")
            if isinstance(advice, dict):
                environment = str(selected.get("root_environment_identity") or "")
                advice_key = self._advice_key(environment, advice)
                if advice_key:
                    selected["research_advice_key"] = advice_key
                selected["research_evidence"] = list(
                    self._inherited_checked_evidence(session)
                )
            selected["context_identity"] = self._context_identity(session)
            return selected
        if not active and request.get("sustained_helper_progress"):
            # This is a request to replan the unchanged obligation *after*
            # earned work drains. Additional checked helpers enrich that
            # planning context; only parent progress or a changed root can
            # discharge the sustained-progress intervention itself.
            if (
                request.get("helper_only_progress_identity")
                != session._helper_only_root_identity()
                or int(session.max_helper_only_provider_quanta or 0) <= 0
                or int(session.helper_only_provider_quanta or 0)
                < int(session.max_helper_only_provider_quanta)
            ):
                return {}
            selected = copy.deepcopy(request)
            selected["context_identity"] = self._context_identity(session)
            return selected
        if not active and request.get("context_identity") != self._context_identity(session):
            return {}
        return copy.deepcopy(request)

    def is_applicable(self, session: Any) -> bool:
        request = self.selected_replan_work(session)
        active = bool(self._active_replan_identity) and (
            self._active_replan_identity == request.get("request_identity")
        )
        return bool(
            request
            and not (
                request.get("sustained_helper_progress")
                # Once active, an owned ready result must publish even if
                # more child debt arrived while its provider was running.
                and not active
                and session._helper_only_progress_has_funded_continuation()
            )
            and getattr(session.conv, "allow_helper_decomposition", True)
            and (
                self._active_replan_identity
                or not session.repair_policy_narrowing_required
            )
            and super().is_applicable(session)
        )

    async def run(self, session: Any) -> MiniOutcome:
        if not self.is_applicable(session):
            return MiniOutcome(action_id=self.id, solved=False, proof=None, metadata={
                "verdict": "root_replan_not_serviceable", "scheduler_neutral": True,
                "preserve_action_budget": True, "iteration_neutral": True,
                "root_replan_invalidated": bool(
                    self._pending_replan_request and not self.selected_replan_work(session)
                ),
            })
        if self._pending_replan_request.get("native_research"):
            self._note_unstarted_research_context(session)
        self._active_replan_identity = str(self._pending_replan_request["request_identity"])
        return await super().run(session)

    def has_owned_active_continuation(self, session: Any) -> bool:
        """Keep paid planner work live without trusting an orphaned marker."""

        if not self._active_replan_identity or not self.selected_replan_work(session):
            return False
        budget = session.budgets.get(self.id)
        dispatch_funded = budget is None or not budget.exhausted()
        driver = self._recursive_driver_state
        identity = driver.get("planner_job_identity")
        broker_status = "missing"
        owned_launch = False
        if driver.get("phase") == "planner_job_pending" and isinstance(identity, Mapping):
            job_id = str(identity.get("job_id") or "").strip()
            fingerprint = str(identity.get("request_fingerprint") or "").strip()
            if job_id and fingerprint:
                launch = self._pending_planner_job_launch
                owned_launch = isinstance(launch, PlannerJobLaunch) and (
                    launch.identity.job_id == job_id
                    and launch.identity.request_fingerprint == fingerprint
                )
                broker = session.planner_job_broker(create=False)
                if broker is not None:
                    broker_status = broker.status(job_id, fingerprint)
        # The scheduler publishes owned ready broker receipts independently
        # of the ordinary action budget, but run() must still accept the work.
        if (dispatch_funded or broker_status == "ready") and session._safe_is_applicable(
            self, context="sustained_helper_progress_active",
        ):
            return True
        if owned_launch or broker_status == "pending":
            return True
        wait = self._planner_equivalent_wait
        return bool(
            wait
            and wait["frontier_signature"] == self._session_progress_signature(session)
            and self._can_wait_for_equivalent_planner(
                session, wait["job_id"], wait["request_fingerprint"],
            )
        )

    def on_outcome_applied(self, session: Any, outcome: MiniOutcome) -> None:
        invalidated = bool(outcome.metadata.get("root_replan_invalidated"))
        if outcome.metadata.get("verdict") == "root_replan_not_serviceable" and not invalidated:
            # A pending provider or temporarily empty pool retains its already
            # authorized request and reservation. A changed root retires them.
            return
        super().on_outcome_applied(session, outcome)
        if not invalidated and (
            outcome.metadata.get("planner_job_pending")
            or outcome.metadata.get("recursive_pass_quantum_yield")
            or outcome.metadata.get("llm_retryable")
            or outcome.metadata.get("preserve_action_budget")
        ):
            return
        identity = str(self._pending_replan_request.get("request_identity") or "")
        advice_key = str(self._pending_replan_request.get("research_advice_key") or "")
        evidence = self._pending_replan_request.get("research_evidence")
        advice = self._pending_replan_request.get("native_research")
        if isinstance(advice, dict):
            # A legacy active request can still carry the advice body after
            # the newer key and evidence fields were absent at dispatch.
            # Derive the key from that body. Unknown dispatch evidence is the
            # helper set present at completion, not a reconstruction of an
            # opaque served artifact id.
            if not advice_key:
                environment = str(
                    self._pending_replan_request.get("root_environment_identity") or ""
                )
                advice_key = self._advice_key(environment, advice)
            if not isinstance(evidence, list):
                evidence = list(self._inherited_checked_evidence(session))
        if (
            identity and not invalidated and outcome.exception is None
            and int(outcome.metadata.get("passes_used", 0) or 0) > 0
            and session._helper_only_progress_intervention_due()
        ):
            session._reset_helper_only_progress_window()
        if identity:
            self._served_replan_requests = [*self._served_replan_requests, identity][-256:]
        if advice_key and isinstance(evidence, list):
            self._served_research_reservations = [
                *self._served_research_reservations,
                {
                    "advice_key": advice_key,
                    "evidence": [text for text in evidence if isinstance(text, str)],
                },
            ][-256:]
        self._pending_replan_request = {}
        self._active_replan_identity = ""

    def scheduler_runtime_state(self) -> dict[str, Any]:
        return {
            **super().scheduler_runtime_state(),
            "root_replan_request": copy.deepcopy(self._pending_replan_request),
            "served_root_replans": list(self._served_replan_requests),
            "served_research_reservations": copy.deepcopy(
                self._served_research_reservations
            ),
            "ancestor_research_reservations": copy.deepcopy(
                self._ancestor_research_reservations
            ),
            "active_root_replan": self._active_replan_identity,
        }

    def apply_scheduler_runtime_state(self, state: Any) -> None:
        record = dict(state or {})
        pending = record.get("root_replan_request", {})
        served = record.get("served_root_replans", [])
        active = record.get("active_root_replan", "")
        served_reservations = _optional_research_reservations(
            record, "served_research_reservations"
        )
        ancestor_reservations = _optional_research_reservations(
            record, "ancestor_research_reservations"
        )
        if not isinstance(pending, dict) or not isinstance(served, list) or len(served) > 256:
            raise ValueError("invalid root replanning runtime state")
        if any(not isinstance(item, str) or len(item) != 64 for item in served):
            raise ValueError("invalid root replanning request history")
        if not isinstance(active, str) or (active and active != pending.get("request_identity")):
            raise ValueError("invalid active root replanning request")
        if "research_advice_key" in pending:
            advice_key = pending.get("research_advice_key")
            if (
                not isinstance(advice_key, str)
                or re.fullmatch(r"[0-9a-f]{64}", advice_key) is None
            ):
                raise ValueError("invalid research replan advice")
        if "research_evidence" in pending:
            evidence = pending.get("research_evidence")
            if (
                not isinstance(evidence, list)
                or len(evidence) > 4096
                or any(
                    not isinstance(text, str) or _HELPER_EVIDENCE.fullmatch(text) is None
                    for text in evidence
                )
            ):
                raise ValueError("invalid research replan evidence")
        if "native_research" in pending:
            advice = self._validated_research_guidance(pending["native_research"])
            environment = pending.get("root_environment_identity")
            if (not isinstance(environment, str)
                    or re.fullmatch(r"[0-9a-f]{64}", environment) is None
                    or pending.get("request_identity") != content_hash((
                        "native_research", environment, advice["artifact_id"],
                    ))):
                raise ValueError("native research replanning identity changed")
            if "research_advice_key" in pending:
                expected = self._advice_key(str(environment), advice)
                if not expected or pending.get("research_advice_key") != expected:
                    raise ValueError("invalid research replan advice")
        # Legacy requests omit this optional pair. New intervention intent
        # must not silently change meaning through truthiness or coercion.
        if "sustained_helper_progress" in pending or "helper_only_progress_identity" in pending:
            sustained = pending.get("sustained_helper_progress")
            helper_identity = pending.get("helper_only_progress_identity")
            if type(sustained) is not bool or not isinstance(helper_identity, str):
                raise ValueError("invalid sustained helper replanning request")
            if (sustained and re.fullmatch(r"[0-9a-f]{64}", helper_identity) is None) or (
                not sustained and helper_identity
            ):
                raise ValueError("invalid sustained helper replanning identity")
        super().apply_scheduler_runtime_state(record)
        self._pending_replan_request = copy.deepcopy(pending)
        self._served_replan_requests = list(served)
        # A legacy child checkpoint omits ancestor reservations. Keep the guard
        # inherited while this session was built; an explicit list replaces it.
        if served_reservations is not None:
            self._served_research_reservations = served_reservations
        if ancestor_reservations is not None:
            self._ancestor_research_reservations = ancestor_reservations
        self._active_replan_identity = active
