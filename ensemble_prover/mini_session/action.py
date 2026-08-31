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
    max_chain_depth: int = 3
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
    exhaust at all -- ``formal_state_search`` ran unbounded for exactly this
    reason (5 dispatches, 611s, zero progress, on putnam_1977_a2 2026-08-19).
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

    def __post_init__(self) -> None:
        if self.scope not in {
            "session",
            "theory_need",
            "formal_context",
            "proof_work",
        }:
            raise ValueError(f"unsupported action budget scope: {self.scope!r}")

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
        self.invocations += 1
        self.total_seconds += float(cost_seconds or 0.0)
        if not productive:
            self.unproductive_seconds += float(cost_seconds or 0.0)

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
