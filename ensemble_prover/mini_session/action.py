"""Typed action, outcome, repair-ticket, and budget contracts for sessions.

An ``Action`` reports applicability, declares its session-state writes, and
returns a ``MiniOutcome``. Actions may mutate the dossier, proof state,
conversation, recorder state, or caches as declared; ``MiniSession.apply``
centralizes budgets, iteration and stagnation counters, normalized telemetry,
and cross-action invariants. Write declarations are auditable contracts rather
than a runtime sandbox.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import math
from typing import (
    Any,
    ClassVar,
    Dict,
    FrozenSet,
    Optional,
    Protocol,
    Tuple,
    runtime_checkable,
)

from ensemble_prover.root_finalization import RootFinalizationCandidate
from ensemble_prover.proof_lineage import ProofLineageEnvelope
from ensemble_prover.dispatch_exception_projection import (
    dispatch_exception_projection,
    dispatch_exception_projection_is_canonical,
)
from ensemble_prover.deadline_guard import DispatchScopeDetached


def action_dispatch_replaced(
    session: Any,
    expected_dispatch_id: str,
) -> bool:
    """Whether a live action's exact dispatch generation was replaced."""

    expected = str(expected_dispatch_id or "").strip()
    if not expected:
        return False
    current = str(
        getattr(session, "_inflight_action_dispatch_id", "") or ""
    ).strip()
    return current != expected


def require_current_action_dispatch(
    session: Any,
    expected_dispatch_id: str,
) -> None:
    """Reject publication by an action whose dispatch generation was replaced."""

    if action_dispatch_replaced(session, expected_dispatch_id):
        raise DispatchScopeDetached(
            "action dispatch generation changed before result publication"
        )


def _has_llm_provider_failure_provenance(exc: BaseException) -> bool:
    """Return whether an exception is concretely attributable to an LLM boundary.

    Text alone is deliberately insufficient: ordinary theorem/session code can
    mention phrases such as ``insufficient balance`` without being a provider
    billing error.  Recognized SDK/HTTP exceptions, status-bearing responses,
    and explicit LLM boundary markers remain authoritative, including through
    an exception chain.
    """

    seen: set[int] = set()
    current: Optional[BaseException] = exc
    for _depth in range(8):
        if current is None or id(current) in seen:
            break
        seen.add(id(current))
        projection = dispatch_exception_projection(current)
        trusted_projection = bool(
            projection is not None
            and dispatch_exception_projection_is_canonical(projection)
        )
        module = str(
            (
                projection.original_module
                if trusted_projection
                else type(current).__module__
            )
            or ""
        ).lower()
        if module.startswith(("httpx", "httpcore", "openai")):
            return True
        if any(
            bool(getattr(current, marker, False))
            for marker in (
                "llm_provider_failure",
                "llm_required_prompt_context_overflow",
                "llm_detached_provider_request",
                "is_provider_capability_chain_exhausted",
                "is_provider_capability_conflict",
            )
        ):
            return True
        response = getattr(current, "response", None)
        status = getattr(response, "status_code", None)
        if status is None:
            status = getattr(current, "status_code", None)
        try:
            if int(status or 0) >= 100:
                return True
        except (TypeError, ValueError):
            pass
        projected_name = (
            projection.original_name
            if trusted_projection
            else type(current).__name__
        )
        if projected_name == "CostBudgetExceeded" and module == (
            "ensemble_prover.llm_usage"
        ):
            return True
        current = getattr(current, "__cause__", None) or getattr(
            current, "__context__", None
        )
    return False


@dataclass
class RepairTicket:
    """Durable scheduler-owned request to repair one rejected Lean proof."""

    ticket_id: str
    proof: str
    lean_output: str = ""
    feedback_text: str = ""
    feedback_source: str = ""
    error_type: str = ""
    failure_signature: str = ""
    target_id: str = "root"
    target_statement: str = ""
    route_id: str = ""
    obligation_id: str = ""
    work_type: str = ""
    proof_attempt_id: str = ""
    strategy_lineage_id: str = ""
    statement_identity: str = ""
    proof_candidate_id: str = ""
    lean_residual_id: str = ""
    helper_blocks: Tuple[str, ...] = ()
    helper_names: Tuple[str, ...] = ()
    source_action_id: str = ""
    turn_index: int = 0
    max_attempts: int = 1
    attempts_used: int = 0
    policy_attempts_used: int = 0
    max_policy_attempts: int = 1
    root_ticket_id: str = ""
    repair_depth: int = 0
    max_chain_depth: int = -1
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        lineage = ProofLineageEnvelope.from_metadata(self.metadata)
        selected_work = self.metadata.get("selected_work_item")
        if isinstance(selected_work, dict):
            lineage_sources = [selected_work]
            graph_record = selected_work.get("graph_record")
            if isinstance(graph_record, dict):
                lineage_sources.append(graph_record)
            for lineage_source in lineage_sources:
                selected_lineage = ProofLineageEnvelope.from_metadata(
                    lineage_source
                )
                lineage = lineage.updated(
                    **{
                        field_name: getattr(selected_lineage, field_name)
                        for field_name in selected_lineage.__dataclass_fields__
                        if getattr(selected_lineage, field_name)
                        and not getattr(lineage, field_name)
                    }
                )
        explicit = {
            "strategy_lineage_id": self.strategy_lineage_id,
            "route_id": self.route_id,
            "statement_identity": self.statement_identity,
            "proof_candidate_id": self.proof_candidate_id,
            "lean_residual_id": self.lean_residual_id,
            "repair_ticket_id": self.ticket_id,
        }
        lineage = lineage.updated(
            **{key: value for key, value in explicit.items() if str(value or "").strip()}
        )
        self.strategy_lineage_id = lineage.strategy_lineage_id
        self.route_id = lineage.route_id
        self.statement_identity = lineage.statement_identity
        self.proof_candidate_id = lineage.proof_candidate_id
        self.lean_residual_id = lineage.lean_residual_id
        self.metadata.update(lineage.merged_metadata(self.metadata))

    @property
    def exhausted(self) -> bool:
        if bool(self.metadata.get("repair_ticket_explicitly_exhausted")):
            return True
        return int(self.attempts_used or 0) >= max(1, int(self.max_attempts or 1))


# ---------------------------------------------------------------------------
# Outcome — pure data, returned by every Action.run().
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MiniOutcome:
    """Typed result of one ``Action.run()`` invocation.

    Actions return this; ``MiniSession.apply(outcome)`` does the cross-cutting
    bookkeeping (budgets, iteration counter, recorder normalization,
    stagnation detection, terminal-state checks).
    """

    action_id: str
    solved: bool
    proof: Optional[str]
    helpers_added: Tuple[str, ...] = ()
    progress: bool = False
    cost_seconds: float = 0.0
    metadata: Dict[str, Any] = field(default_factory=dict)
    exception: Optional[BaseException] = None
    repair_ticket: Optional[RepairTicket] = None
    root_candidate: Optional[RootFinalizationCandidate] = None

    def elapsed_is_productive(self) -> bool:
        """Whether this dispatch's wall time paid off for spin accounting.

        ``ActionBudget``'s aggregate seconds ceiling exists to bound spin:
        time spent on dispatches that produced no progress.  Actions report
        that through ``solved``/``progress``.  ``FormalStateSearchAction``
        deliberately reports ``progress=False`` for a bounded exploration
        quantum while its outcome metadata records whether the quantum reset
        its per-context no-improvement window in ``formal_rank_improved``;
        that action-emitted receipt is the narrow formal-search productivity
        signal.  Provider prose, replayed free text, and exception receipts
        never qualify.
        """

        if self.exception is not None:
            return False
        if self.solved or self.progress:
            return True
        return (self.metadata or {}).get("formal_rank_improved") is True

    @classmethod
    def from_exception(
        cls,
        action: "Action",
        exc: BaseException,
        *,
        cost_seconds: float = 0.0,
    ) -> "MiniOutcome":
        # Exception classification is diagnostic policy, never part of action
        # settlement.  A malformed/custom exception must not escape this
        # adapter and strand loop-wide dispatch instrumentation before its
        # ``finally`` block can restore the event loop.
        try:
            exception_type = str(
                type.__getattribute__(type(exc), "__name__") or "BaseException"
            )
        except BaseException:
            exception_type = "BaseException"
        try:
            exception_message = str(exc)
        except BaseException:
            exception_message = "<exception message unavailable>"
        try:
            selected_context_invalidated = bool(
                getattr(exc, "mini_selected_proof_idea_context_error", False)
            )
        except BaseException:
            selected_context_invalidated = False
        if selected_context_invalidated:
            metadata = {
                "exception_type": exception_type,
                "exception_message": exception_message,
                "terminal_failure": False,
                "terminal_failure_scope": "scoped",
                "scoped_failure_reason": (
                    "selected_proof_idea_context_invalidated"
                ),
                "selected_work_projection_invalidated": True,
                "selected_work_projection_zero_provider": True,
                "preserve_action_budget": True,
                "refund_local_repair_quota": True,
                "iteration_neutral": True,
                "scheduler_neutral": True,
                "stagnation_neutral": True,
                "hard_pivot_neutral": True,
            }
        else:
            # An action boundary must not erase an already-classifiable global
            # provider failure behind the generic controller exception label.
            # In particular, formal-state search can surface a pre-generation
            # 402 after its durable dispatch receipt; preserving the canonical
            # reason makes the terminal summary actionable while accounting
            # continues to charge that rejected request zero.
            from ensemble_prover.llm_error_policy import classify_llm_exception

            classification_error = ""
            provider_failure_provenance = False
            try:
                llm_classification = classify_llm_exception(exc)
                provider_failure_provenance = (
                    _has_llm_provider_failure_provenance(exc)
                )
                terminal_llm_reason = (
                    str(llm_classification.failure_reason or "").strip()
                    if bool(llm_classification.terminal)
                    and provider_failure_provenance
                    else ""
                )
            except BaseException as classification_exc:
                # The original action exception remains authoritative.  The
                # classifier is best-effort metadata and cannot be allowed to
                # replace it or prevent operation-scope teardown.
                llm_classification = None
                terminal_llm_reason = ""
                try:
                    classification_error = str(
                        type.__getattribute__(
                            type(classification_exc),
                            "__name__",
                        )
                        or "BaseException"
                    )
                except BaseException:
                    classification_error = "BaseException"
            if terminal_llm_reason:
                metadata = {
                    "exception_type": exception_type,
                    "exception_message": exception_message,
                    "terminal_failure": True,
                    "terminal_failure_reason": terminal_llm_reason,
                    "terminal_failure_kind": str(
                        llm_classification.kind or ""
                    ).strip(),
                }
            else:
                # A repair/action implementation exception is an
                # infrastructure failure, not a mathematical verdict.  Keep
                # the exact lane and accounting available for durable timed
                # retry; configured run/cost governors or operator
                # cancellation remain the only authorities that may end it.
                metadata = {
                    "exception_type": exception_type,
                    "exception_message": exception_message,
                    "terminal_failure": False,
                    "terminal_failure_scope": "scoped",
                    "scoped_failure_reason": (
                        "mini_action_infrastructure_exception"
                    ),
                    "llm_failure_scope": "scoped",
                    "llm_failure_kind": (
                        str(llm_classification.kind or "").strip()
                        if llm_classification is not None
                        and bool(llm_classification.retryable)
                        and provider_failure_provenance
                        else "mini_action_infrastructure_exception"
                    ),
                    "llm_retryable": True,
                    "zero_provider_failure": not provider_failure_provenance,
                    "retryable_infrastructure": True,
                    "retryable_infrastructure_reason": (
                        "mini_action_infrastructure_exception"
                    ),
                    "preserve_frontier_work": True,
                    "defer_selected_frontier_action": True,
                    "preserve_action_budget": True,
                    "iteration_neutral": True,
                    "scheduler_neutral": True,
                    "stagnation_neutral": True,
                    "hard_pivot_neutral": True,
                }
            if classification_error:
                metadata["exception_classification_error"] = classification_error
            if terminal_llm_reason:
                assert llm_classification is not None
                metadata.update(
                    {
                        "llm_failure_scope": "global",
                        "llm_failure_kind": str(
                            llm_classification.kind or ""
                        ).strip(),
                        "llm_status_code": int(
                            llm_classification.status_code or 0
                        ),
                    }
                )
        return cls(
            action_id=action.id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=False,
            cost_seconds=cost_seconds,
            metadata=metadata,
            exception=exc,
        )


# ---------------------------------------------------------------------------
# Budget — dispatch accounting with an explicit semantic scope.
# ---------------------------------------------------------------------------


@dataclass
class ActionBudget:
    """Dispatch budget/accounting record, checked between invocations.

    Individual wall-clock operations are bounded by each action's own timeout;
    ``max_total_seconds`` prevents another dispatch once recorded action time
    reaches the cumulative cap.  It is not an interrupt mechanism for an
    already-running action.

    ``scope="session"`` is the traditional cumulative cap keyed by action id.
    A semantic scope such as ``"theory_need"``, ``"formal_context"``, or
    ``"proof_work"`` means
    that the action enforces
    its bounded work against that semantic identity; the session-level record
    remains aggregate telemetry and must not suppress an unrelated identity.

    ``max_aggregate_invocations`` / ``max_aggregate_seconds`` are the explicit
    runaway ceiling across *all* identities, and apply whatever the scope is.
    The seconds ceiling charges ``unproductive_seconds`` -- time spent on
    dispatches that reported no progress -- rather than total time, so it
    bounds spin without ever cutting search that is still paying off.
    They are opt-in (negative / zero means unset) precisely because crossing
    identities is what the semantic scopes otherwise forbid: a caller that
    sets one is declaring that total spend, not per-identity spend, is the
    bound it wants.  Without such a ceiling a semantic-scope budget can never
    exhaust across distinct work identities.
    """

    max_invocations: int
    max_total_seconds: float
    invocations: int = 0
    total_seconds: float = 0.0
    last_failure_reason: str = ""
    scope: str = "session"
    max_aggregate_invocations: int = -1
    max_aggregate_seconds: float = 0.0
    unproductive_seconds: float = 0.0
    research_invocation_seal: Optional[Dict[str, Any]] = None
    research_invocation_debits: list[str] = field(default_factory=list)
    # Resource receipts outlive semantic portfolio continuations. Their keys
    # bind a scheduler dispatch and its accounting operation, not a theorem.
    execution_receipts: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    execution_service_seconds: float = 0.0
    execution_elapsed_seconds: float = 0.0
    historical_execution_cost_incomplete: bool = False

    def __setattr__(self, name: str, value: Any) -> None:
        if name == "max_aggregate_invocations":
            # An explicit policy assignment supersedes a research-owned seal,
            # even when the new ceiling happens to have the same value.
            object.__setattr__(self, "research_invocation_seal", None)
        object.__setattr__(self, name, value)

    def __post_init__(self) -> None:
        if type(self.historical_execution_cost_incomplete) is not bool:
            raise ValueError("invalid historical execution cost marker")
        if not isinstance(self.execution_receipts, dict):
            raise ValueError("invalid execution receipt ledger")
        for key, receipt in self.execution_receipts.items():
            if not isinstance(key, str) or not isinstance(receipt, dict):
                raise ValueError("invalid execution receipt")
            if (type(receipt.get("schema_version")) is not int
                    or receipt["schema_version"] != 1) or key != self.execution_key(
                receipt.get("dispatch_id", ""), receipt.get("operation_id", "")
            ):
                raise ValueError("invalid execution receipt identity")
            for metric in ("elapsed_seconds", "nested_seconds", "service_seconds"):
                value = receipt.get(metric)
                if (isinstance(value, bool) or not isinstance(value, (float, int))
                        or not math.isfinite(value) or value < 0):
                    raise ValueError("invalid execution receipt duration")
            if abs(receipt["elapsed_seconds"] - receipt["nested_seconds"]
                   - receipt["service_seconds"]) > 1e-6:
                raise ValueError("invalid exclusive execution duration")
            if type(receipt.get("semantic_attempt_completed")) is not bool:
                raise ValueError("invalid execution semantic completion")
            if type(receipt.get("productive")) is not bool:
                raise ValueError("invalid execution productivity receipt")
            if not isinstance(receipt.get("details"), dict):
                raise ValueError("invalid execution receipt details")
            if not isinstance(receipt.get("ownership"), dict):
                raise ValueError("invalid execution ownership")
        if (not math.isfinite(self.execution_service_seconds)
                or self.execution_service_seconds < 0
                or abs(self.execution_service_seconds - sum(
                    float(receipt["service_seconds"]) for receipt in self.execution_receipts.values()
                )) > 1e-5):
            raise ValueError("execution service total does not match receipts")
        if (not math.isfinite(self.execution_elapsed_seconds)
                or self.execution_elapsed_seconds < 0
                or abs(self.execution_elapsed_seconds - sum(
                    float(receipt["elapsed_seconds"]) for receipt in self.execution_receipts.values()
                )) > 1e-5):
            raise ValueError("execution elapsed total does not match receipts")
        if (self.execution_elapsed_seconds > self.total_seconds + 1e-5
                or sum(int(r["semantic_attempt_completed"])
                       for r in self.execution_receipts.values()) > self.invocations):
            raise ValueError("execution receipts exceed action budget accounting")
        debits = self.research_invocation_debits
        if (not isinstance(debits, list)
                or any(not isinstance(token, str) or not token for token in debits)
                or len(set(debits)) != len(debits)):
            raise ValueError("invalid research invocation debit ownership")
        seal = self.research_invocation_seal
        if seal is not None:
            if (not isinstance(seal, dict)
                    or set(seal) != {"previous_cap", "cap", "grants"}
                    or type(seal["previous_cap"]) is not int
                    or seal["previous_cap"] < -1
                    or type(seal["cap"]) is not int or seal["cap"] < 0
                    or seal["cap"] != self.max_aggregate_invocations
                    or (seal["previous_cap"] != -1 and seal["previous_cap"] < seal["cap"])
                    or not isinstance(seal["grants"], dict) or not seal["grants"]
                    or any(not isinstance(key, str) or not key or not isinstance(value, dict)
                           or set(value) != {"cap", "retained"}
                           or type(value["cap"]) is not int or value["cap"] < 0
                           or type(value["retained"]) is not bool
                           for key, value in seal["grants"].items())):
                raise ValueError("invalid research invocation seal")
            limits = [value["cap"] for value in seal["grants"].values()]
            if seal["previous_cap"] >= 0:
                limits.append(seal["previous_cap"])
            if seal["cap"] != min(limits):
                raise ValueError("invalid research invocation seal limits")
        if self.scope not in {
            "session",
            "theory_need",
            "formal_context",
            "proof_work",
        }:
            raise ValueError(f"unsupported action budget scope: {self.scope!r}")

        # Runtime-only version history is deliberately outside the dataclass
        # fields: standalone checkpoints retain the ordinary receipt map.
        from .execution_receipt_history import ExecutionReceiptHistory

        self._execution_history = ExecutionReceiptHistory(self.execution_receipts)
        self._execution_version = 0
        self._execution_completed_count = sum(
            int(r["semantic_attempt_completed"]) for r in self.execution_receipts.values()
        )
        self._execution_pending_count = sum(
            r["details"].get("detached_tail_pending") is True
            for r in self.execution_receipts.values()
        )
        self._execution_projection_only = False
        self._execution_projection_cursor: Dict[str, Any] = {}

    def execution_cursor(self) -> Dict[str, Any]:
        """Capture exact local receipt ownership without copying its history."""
        if self._execution_projection_only:
            return dict(self._execution_projection_cursor)
        return {
            "schema_version": 1,
            "history_id": self._execution_history.identity,
            "version": self._execution_version,
            "receipt_count": len(self.execution_receipts),
            "completed_count": self._execution_completed_count,
            "pending_count": self._execution_pending_count,
        }

    def _require_execution_ownership(self) -> None:
        if self._execution_projection_only:
            raise ValueError("scheduler accounting projection cannot resume execution")

    def settle_execution_tail(self, key: str) -> None:
        """Version a pending-tail update so older cutpoints remain immutable."""
        self._require_execution_ownership()
        receipt = self.execution_receipts.get(key)
        if receipt is not None and receipt["details"].get("detached_tail_pending") is True:
            receipt["details"]["detached_tail_pending"] = False
            self._execution_pending_count -= 1
            self._execution_version = self._execution_history.append(
                self._execution_version, key, "detached_tail_pending", False,
            )

    def exhausted(self) -> bool:
        if (
            self.scope == "session"
            and self.max_invocations >= 0
            and self.invocations >= self.max_invocations
        ):
            return True
        if (
            self.scope in {"session", "proof_work"}
            and self.max_total_seconds > 0
            and self.total_seconds >= self.max_total_seconds
        ):
            return True
        # Scope-independent runaway ceiling; see the class docstring.
        if (
            self.max_aggregate_invocations >= 0
            and self.invocations >= self.max_aggregate_invocations
        ):
            return True
        if (
            self.max_aggregate_seconds > 0
            and self.unproductive_seconds >= self.max_aggregate_seconds
        ):
            return True
        return False

    def consume(self, cost_seconds: float, *, productive: bool = False) -> None:
        self.consume_elapsed(cost_seconds, productive=productive)
        self.invocations += 1

    def consume_elapsed(self, cost_seconds: float, *, productive: bool = False) -> None:
        """Debit executed resource time without finishing a semantic attempt."""
        seconds = float(cost_seconds or 0.0)
        if not math.isfinite(seconds) or seconds < 0:
            raise ValueError("action elapsed time must be finite and nonnegative")
        self.total_seconds += seconds
        if not productive:
            self.unproductive_seconds += seconds

    @staticmethod
    def execution_key(dispatch_id: str, operation_id: str) -> str:
        if not isinstance(dispatch_id, str) or not dispatch_id:
            raise ValueError("execution receipt requires dispatch identity")
        if not isinstance(operation_id, str) or not operation_id:
            raise ValueError("execution receipt requires operation identity")
        return f"{len(dispatch_id)}:{dispatch_id}{operation_id}"

    def record_execution(
        self, *, dispatch_id: str, operation_id: str, elapsed_seconds: float,
        nested_seconds: float = 0.0, productive: bool = False,
        disposition: str = "settled", details: Optional[Dict[str, Any]] = None,
        ownership: Optional[Dict[str, str]] = None,
    ) -> Tuple[Dict[str, Any], bool]:
        """Commit one resource debit; replay never charges the same owner twice.

        Admission and fairness retain inclusive duration; exclusive service
        has a separate total for resource rollups across nested operations.
        """
        self._require_execution_ownership()
        key = self.execution_key(dispatch_id, operation_id)
        existing = self.execution_receipts.get(key)
        if existing is not None:
            return existing, False
        elapsed = float(elapsed_seconds)
        nested = float(nested_seconds)
        if (not math.isfinite(elapsed) or not math.isfinite(nested)
                or elapsed < 0 or nested < 0):
            raise ValueError("invalid execution elapsed duration")
        nested = min(elapsed, nested)
        receipt: Dict[str, Any] = {
            "schema_version": 1, "dispatch_id": dispatch_id,
            "operation_id": operation_id, "elapsed_seconds": elapsed,
            "nested_seconds": nested, "service_seconds": elapsed - nested,
            "productive": bool(productive),
            "semantic_attempt_completed": False, "disposition": disposition,
            "details": dict(details or {}),
            "ownership": dict(ownership or {}),
        }
        self.consume_elapsed(elapsed, productive=productive)
        self.execution_service_seconds += receipt["service_seconds"]
        self.execution_elapsed_seconds += elapsed
        self.execution_receipts[key] = receipt
        self._execution_pending_count += receipt["details"].get("detached_tail_pending") is True
        self._execution_version = self._execution_history.append(
            self._execution_version, key, "receipt", receipt,
        )
        return receipt, True

    def complete_execution_attempt(self, receipt: Dict[str, Any]) -> bool:
        """Count portfolio completion independently from its executed slices."""
        self._require_execution_ownership()
        key = self.execution_key(receipt["dispatch_id"], receipt["operation_id"])
        if self.execution_receipts.get(key) is not receipt:
            raise ValueError("execution receipt is not owned by this budget")
        if receipt["semantic_attempt_completed"]:
            return False
        receipt["semantic_attempt_completed"] = True
        self.invocations += 1
        self._execution_completed_count += 1
        self._execution_version = self._execution_history.append(
            self._execution_version, key, "semantic_attempt_completed", True,
        )
        return True

    def mark_exhausted(self, reason: str) -> None:
        # Bumps invocation count past the cap so ``exhausted()`` returns True.
        caps = [
            cap
            for cap in (self.max_invocations, self.max_aggregate_invocations)
            if cap >= 0
        ]
        if caps:
            self.invocations = max(self.invocations, max(caps)) + 1
        if self.max_aggregate_seconds > 0:
            self.unproductive_seconds = max(
                self.unproductive_seconds, self.max_aggregate_seconds
            )
        self.last_failure_reason = str(reason or "")


# ---------------------------------------------------------------------------
# Action Protocol — every action class implements this surface.
# ---------------------------------------------------------------------------


@runtime_checkable
class Action(Protocol):
    """Protocol: a stateless or self-contained action the session can dispatch.

    Each action class declares:

    - ``id``: stable identifier used as budget key and recorder ``action_id``.
    - ``priority``: integer; lower scanned earlier in the static priority
      fallback (frontier-first selection consults ``work_frontier()`` first;
      see ``MiniSession.select_next_action``).
    - ``cost_estimate_s``: rough wall-clock estimate; used as a tie-breaker
      in priority scanning.
    - ``WRITES``: ``ClassVar[FrozenSet[str]]`` listing session-owned objects
      this action mutates (e.g. ``frozenset({"dossier", "proof_state"})``
      for ``LemmaDagDecomposeAction``). Documentary + tested-against, not
      runtime-enforced.
    - Actions whose bounded unit is narrower than the session may declare an
      optional ``BUDGET_SCOPE`` class variable. The default is ``"session"``;
      ``"theory_need"``, ``"formal_context"``, and ``"proof_work"`` delegate
      exhaustion to the action's durable per-identity guards while retaining
      aggregate session telemetry.
    - Actions with execution-only configuration may declare
      ``REPLAY_OPERATIONAL_SPEC_PATHS``. Each dotted path names one exact leaf
      excluded from deterministic replay identity.
    - Actions may declare ``FAILED_DISPATCH_ROLLBACK_STATE_FIELDS`` for torn
      transient attributes that must rewind when dispatch generation is
      recycled. Runtime continuation fields are preserved unless explicitly
      named because recycle does not call ``on_outcome_applied``.

    Methods:

    - ``is_applicable(session)``: synchronous predicate. Return False if the
      action has no work to do (frontier empty, preconditions absent, etc.).
    - ``run(session)``: async; do the work, return a ``MiniOutcome``.
    """

    id: str
    priority: int
    cost_estimate_s: float
    WRITES: ClassVar[FrozenSet[str]]

    def is_applicable(self, session: Any) -> bool: ...

    async def run(self, session: Any) -> MiniOutcome: ...
