"""Run a bounded child ``MiniSession`` for one open helper goal.

The child session receives a fresh conversation and incremented recursion
depth, so give-up and depth gates apply inside the helper proof. Its slim action
set includes conversation, repair/salvage, and proof-state-aware deterministic
work but omits root-level actions irrelevant to a single helper.
"""

from __future__ import annotations

import asyncio
import copy
import contextvars
import inspect
import time
from typing import Any, Callable, Dict, Mapping, Optional, Sequence, Tuple

from ..deadline_guard import _cancel_and_abandon
from ..helper_salvage import (
    dependency_ordered_verified_helper_items,
    helper_uses_superseded_support,
    helper_provenance_is_trust_monotone,
    helper_source_hash_was_superseded,
    preflight_dependency_ordered_verified_helper_items,
)
from ..mini_runtime_defaults import DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
from ..mini_branching import (
    merge_relevant_child_proof_ideas,
    selected_child_proof_idea_packet,
    seed_relevant_proof_ideas_for_child,
)
from .action import ActionBudget
from .session import MiniSession, _observe_and_detach_operation_tail


_RECURSIVE_CLEANUP_OUTCOME_ATTR = "_mini_recursive_cleanup_outcome"


def _nonnegative_counter(value: Any) -> int:
    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError, OverflowError):
        return 0


def _child_provider_exposure(
    child_session: Any,
    *,
    include_inflight: bool = False,
) -> tuple[int, int]:
    """Read applied totals plus any newer durable last-action evidence."""

    metadata = dict(
        getattr(child_session, "last_action_outcome_metadata", {}) or {}
    )
    completed = max(
        _nonnegative_counter(
            getattr(child_session, "provider_calls_completed_total", 0)
        ),
        _nonnegative_counter(metadata.get("provider_calls_completed")),
    )
    durable_dispatched = max(
        _nonnegative_counter(
            getattr(child_session, "provider_dispatches_started_total", 0)
        ),
        _nonnegative_counter(metadata.get("provider_dispatches_started")),
    )
    inflight_dispatched = (
        _nonnegative_counter(
            getattr(
                getattr(
                    child_session,
                    "_inflight_provider_exposure_tracker",
                    None,
                ),
                "provider_dispatches_started",
                0,
            )
        )
        if include_inflight
        else 0
    )
    dispatched = durable_dispatched + inflight_dispatched
    return completed, dispatched


class _RevocableRecursiveHelperCapability:
    """Lease-gated view of one shared parent side-effect capability.

    The wrapper is installed before the child task starts, so methods captured
    before cancellation still close over the mutable lease instead of the raw
    parent object.  Reads remain available only while the lease is active;
    writes and provider calls fail closed once the detached tail is fenced.
    """

    __slots__ = ("__capability_label", "__lease", "__target")

    def __init__(self, target: Any, lease: Any, *, label: str) -> None:
        object.__setattr__(
            self,
            "_RevocableRecursiveHelperCapability__target",
            target,
        )
        object.__setattr__(
            self,
            "_RevocableRecursiveHelperCapability__lease",
            lease,
        )
        object.__setattr__(
            self,
            "_RevocableRecursiveHelperCapability__capability_label",
            str(label or "shared"),
        )

    def _require_active(self, operation: str) -> None:
        from ..runtime_context import RuntimeCapabilityRevokedError

        lease = object.__getattribute__(
            self,
            "_RevocableRecursiveHelperCapability__lease",
        )
        if not bool(getattr(lease, "abandoned", False)):
            return
        label = object.__getattribute__(
            self,
            "_RevocableRecursiveHelperCapability__capability_label",
        )
        raise RuntimeCapabilityRevokedError(
            f"recursive helper {label} capability was revoked before "
            f"{str(operation or 'operation')}"
        )

    def __getattr__(self, name: str) -> Any:
        if name in {
            "_target",
            "_lease",
            "_capability_label",
            "_dispatch_capability_identity",
        }:
            raise AttributeError(name)
        self._require_active(f"attribute access {name}")
        target = object.__getattribute__(
            self,
            "_RevocableRecursiveHelperCapability__target",
        )
        value = getattr(target, name)
        if not callable(value):
            label = object.__getattribute__(
                self,
                "_RevocableRecursiveHelperCapability__capability_label",
            )
            if (
                label == "theory library"
                and name in {"needs", "store", "_store", "verifier", "retriever"}
                and value is not None
            ):
                return _RevocableRecursiveHelperCapability(
                    value,
                    object.__getattribute__(
                        self,
                        "_RevocableRecursiveHelperCapability__lease",
                    ),
                    label=f"theory library {name}",
                )
            return value

        def invoke(*args: Any, **kwargs: Any) -> Any:
            def guard_deferred_publication(resolved: Any) -> Any:
                label = object.__getattribute__(
                    self,
                    "_RevocableRecursiveHelperCapability__capability_label",
                )
                if (
                    label == "proof cache"
                    and name.startswith("begin_")
                    and resolved is not None
                ):
                    return _RevocableRecursiveHelperCapability(
                        resolved,
                        object.__getattribute__(
                            self,
                            "_RevocableRecursiveHelperCapability__lease",
                        ),
                        label="proof cache deferred publication",
                    )
                return resolved

            self._require_active(f"call {name}")
            result = value(*args, **kwargs)
            if not inspect.isawaitable(result):
                self._require_active(f"return from {name}")
                return guard_deferred_publication(result)

            async def await_guarded_result() -> Any:
                self._require_active(f"await {name}")
                resolved = await result
                self._require_active(f"return from {name}")
                return guard_deferred_publication(resolved)

            return await_guarded_result()

        return invoke

    def __setattr__(self, name: str, value: Any) -> None:
        self._require_active(f"attribute write {name}")
        setattr(
            object.__getattribute__(
                self,
                "_RevocableRecursiveHelperCapability__target",
            ),
            name,
            value,
        )

    def __bool__(self) -> bool:
        self._require_active("truth-value test")
        return bool(
            object.__getattribute__(
                self,
                "_RevocableRecursiveHelperCapability__target",
            )
        )

    def _dispatch_capability_identity_token(self) -> Any:
        """Expose the live wrapped capability for lock and generation identity.

        A tuple token is not weak-keyable, so lock registries would fall back
        to one per-loop lock and a retired generation's occupancy would be
        inherited by every fresh runner. Returning the wrapped object lets
        ``_dispatch_capability_identity`` unwrap nested generation rotation.
        """

        return object.__getattribute__(
            self,
            "_RevocableRecursiveHelperCapability__target",
        )


def _install_recursive_helper_capability_fence(
    child_session: Any,
    lease: Any,
) -> None:
    """Replace every shared side-effect surface before child execution."""

    proxies_by_identity: Dict[int, _RevocableRecursiveHelperCapability] = {}
    for attribute, label in (
        ("lean", "Lean verifier"),
        ("prover_client", "prover client"),
        ("refiner_client", "refiner client"),
        ("recorder", "recorder"),
        ("proof_cache", "proof cache"),
        ("cost_controller", "cost controller"),
    ):
        target = getattr(child_session, attribute, None)
        if target is None:
            continue
        proxy = proxies_by_identity.get(id(target))
        if proxy is None:
            proxy = _RevocableRecursiveHelperCapability(
                target,
                lease,
                label=label,
            )
            proxies_by_identity[id(target)] = proxy
        setattr(child_session, attribute, proxy)

    # No registered recursive-child action consumes ``session.parent``.
    # Sever this raw mutable reference before child code can capture it.
    child_session.parent = None

    theory_library = getattr(child_session, "theory_library", None)
    if theory_library is not None:
        child_session.theory_library = _RevocableRecursiveHelperCapability(
            theory_library,
            lease,
            label="theory library",
        )

    # Production theory construction is stateful: its builder captures a raw
    # provider client and cost controller independently of the MiniSession.
    # A method-only wrapper cannot stop an already-started build after it has
    # suppressed cancellation.  Give the child a shallow-local builder whose
    # captured shared capabilities carry this same revocation lease, then wrap
    # the builder itself so calls begun after revocation also fail closed.
    theory_builder = getattr(child_session, "theory_candidate_builder", None)
    fenced_theory_builder = None
    if theory_builder is not None:
        try:
            local_builder = copy.copy(theory_builder)
            rebound_capability = False
            for attribute, label in (
                ("client", "theory builder client"),
                ("cost_controller", "theory builder cost controller"),
            ):
                target = getattr(theory_builder, attribute, None)
                if target is None:
                    continue
                proxy = proxies_by_identity.get(id(target))
                if proxy is None:
                    proxy = _RevocableRecursiveHelperCapability(
                        target,
                        lease,
                        label=label,
                    )
                    proxies_by_identity[id(target)] = proxy
                setattr(local_builder, attribute, proxy)
                rebound_capability = True
            if rebound_capability:
                fenced_theory_builder = _RevocableRecursiveHelperCapability(
                    local_builder,
                    lease,
                    label="theory candidate builder",
                )
        except Exception:
            # Unknown builders whose captured side effects cannot be rebound
            # are unavailable in a detachable recursive child.  Root theory
            # work remains available through the original parent builder.
            fenced_theory_builder = None
        child_session.theory_candidate_builder = fenced_theory_builder

    # ConversationTurnAction captures its client at registration time rather
    # than resolving only through ``session.prover_client``. Replace those
    # references too; otherwise a pre-captured raw client bypasses the fence.
    for action in tuple(getattr(child_session, "actions", ()) or ()):
        if hasattr(action, "candidate_builder"):
            action.candidate_builder = fenced_theory_builder
        client = getattr(action, "client", None)
        if client is None:
            continue
        proxy = proxies_by_identity.get(id(client))
        if proxy is not None:
            action.client = proxy


def _recursive_cleanup_infrastructure_outcome(
    child_session: Any,
    *,
    reason: str,
) -> Dict[str, Any]:
    """Fence one non-quiescent child and publish a retryable yield shape.

    The child session is an isolated speculative state image.  Once its
    cancellation cleanup outlives the finite ownership allowance, none of
    that in-memory image is eligible for parent admission. Detaching the
    result-only tail keeps the controller responsive; the capability lease
    prevents any new shared side effect from that tail.
    """

    provider_calls_completed, provider_dispatches_started = (
        _child_provider_exposure(child_session, include_inflight=True)
    )
    zero_provider_failure = (
        provider_calls_completed == 0 and provider_dispatches_started == 0
    )
    outcome = {
        "verdict": "recursive_helper_cleanup_infrastructure_yield",
        "retryable_infrastructure": True,
        "retryable_infrastructure_reason": str(reason or ""),
        "llm_retryable": True,
        "llm_failure_kind": "recursive_helper_cleanup_timeout",
        "provider_calls_completed": provider_calls_completed,
        "provider_dispatches_started": provider_dispatches_started,
        "zero_provider_failure": zero_provider_failure,
        "terminal_failure": False,
        "preserve_frontier_work": True,
        # A child that never completed a provider request consumed no paid
        # mathematical attempt. Genuine provider work remains charged even
        # though its durable frame stays retryable and stagnation-neutral.
        "preserve_action_budget": zero_provider_failure,
        "iteration_neutral": zero_provider_failure,
        "scheduler_neutral": True,
        "stagnation_neutral": True,
        "hard_pivot_neutral": True,
        "shared_capabilities_revoked": True,
    }
    setattr(child_session, _RECURSIVE_CLEANUP_OUTCOME_ATTR, dict(outcome))

    try:
        child_session.parent = None
    except Exception:
        pass
    lease = getattr(child_session, "_mini_recursive_hard_timeout_lease", None)
    if lease is not None:
        try:
            lease.abandoned = True
            lease.late_result_discarded = True
        except Exception:
            pass
    return outcome



def _bounded_nested_elapsed_deadline_epoch_s(
    *,
    max_elapsed_s: float,
    ancestor_deadline_epoch_s: float = 0.0,
) -> float:
    """Return the earliest positive local/ancestor wall-clock deadline."""

    deadlines: list[float] = []
    elapsed_s = max(0.0, float(max_elapsed_s or 0.0))
    if elapsed_s > 0.0:
        deadlines.append(time.time() + elapsed_s)
    ancestor = max(0.0, float(ancestor_deadline_epoch_s or 0.0))
    if ancestor > 0.0:
        deadlines.append(ancestor)
    return min(deadlines) if deadlines else 0.0


async def _run_child_with_elapsed_budget(
    child_session: MiniSession,
    *,
    max_elapsed_s: float,
    deadline_epoch_s: float,
) -> Tuple[bool, Optional[str], bool]:
    """Run one nested child without resetting its durable wall-clock budget.

    The cooperative timeout gives ``MiniSession.run`` a finite cancellation
    allowance so its provider and mutation barriers can settle before the
    caller publishes ``child_complete``. Productive child runtime never arms
    a process-killing lease: a finite local allowance is an action scheduling
    boundary, not authority to destroy the complete proof search. A child
    that outlives cleanup is fenced from parent publication and detached as a
    result-only tail; the scheduler receives a retryable infrastructure yield.
    """

    elapsed_budget = max(0.0, float(max_elapsed_s or 0.0))
    durable_deadline = max(0.0, float(deadline_epoch_s or 0.0))
    if elapsed_budget > 0.0:
        local_deadline = time.time() + elapsed_budget
        durable_deadline = (
            min(durable_deadline, local_deadline)
            if durable_deadline > 0.0
            else local_deadline
        )
    remaining_s: Optional[float] = (
        durable_deadline - time.time()
        if durable_deadline > 0.0
        else None
    )
    if remaining_s is not None and remaining_s <= 0.0:
        # Distinguish a restored/stale lease that prevented *all* child work
        # from an in-flight child that genuinely consumed its allowance.  The
        # recursive controller may refund/reissue only the former.
        setattr(
            child_session,
            "_mini_recursive_elapsed_budget_expired_before_run",
            True,
        )
        child_conv = getattr(child_session, "conv", None)
        if child_conv is not None:
            setattr(
                child_conv,
                "_mini_recursive_elapsed_budget_expired_before_run",
                True,
            )
        return False, None, True

    cleanup_allowance_s = max(
        0.001,
        float(
            getattr(child_session, "recursive_helper_cleanup_timeout_s", 1.0)
            or 1.0
        ),
    )

    # Preserve request/cost/deadline context while removing only the owning
    # action's raw-child tracker.  This helper joins the child on every normal
    # path; on resistant cancellation it explicitly reclassifies the tail as
    # result-only, so the parent transaction never waits again or poisons the
    # whole Mini run.  An empty Context would incorrectly drop usage receipts.
    from .session import _OPERATION_CHILD_TASK_TRACKER
    from ..runtime_context import (
        HardTimeoutLease,
        _CURRENT_HARD_TIMEOUT_LEASE,
    )

    child_context = contextvars.copy_context()
    child_context.run(_OPERATION_CHILD_TASK_TRACKER.set, None)
    mutation_lease = HardTimeoutLease(
        timeout_s=(0.0 if remaining_s is None else max(0.0, remaining_s)),
        cancel_grace_s=cleanup_allowance_s,
    )
    _install_recursive_helper_capability_fence(child_session, mutation_lease)
    child_context.run(_CURRENT_HARD_TIMEOUT_LEASE.set, mutation_lease)
    setattr(child_session, "_mini_recursive_hard_timeout_lease", mutation_lease)
    task = child_context.run(asyncio.create_task, child_session.run())

    async def drain_cancelled_child(
        *,
        initial_cancellation: Optional[asyncio.CancelledError],
        timeout_reason: str,
    ) -> tuple[
        Optional[asyncio.CancelledError],
        Optional[BaseException],
        bool,
    ]:
        """Own cancellation through settlement or the finite fence point."""

        caller_cancellation = initial_cancellation
        cleanup_deadline = time.monotonic() + cleanup_allowance_s
        while not task.done():
            cleanup_remaining_s = cleanup_deadline - time.monotonic()
            if cleanup_remaining_s <= 0.0:
                break
            try:
                # ``asyncio.wait`` deliberately avoids forwarding later
                # caller cancellations into a child already performing its
                # owned provider settlement.
                await asyncio.wait({task}, timeout=cleanup_remaining_s)
            except asyncio.CancelledError as cancellation:
                caller_cancellation = caller_cancellation or cancellation
                continue

        cleanup_timed_out = not task.done()
        if cleanup_timed_out:
            # Revoke all child-held shared capabilities first. The same lease
            # lives in the child's copied Context and in every facade already
            # captured by its actions, so the tail cannot start another paid
            # call or shared publication.
            mutation_lease.abandoned = True
            mutation_lease.late_result_discarded = True
            _recursive_cleanup_infrastructure_outcome(
                child_session,
                reason=timeout_reason,
            )
            # asyncio cannot force-stop a cancellation-suppressing coroutine.
            # Keep observing/retrying cancellation off the caller path, mark
            # the tail result-only for global barriers, and discard any late
            # value. The child has no parent mutation bridge.
            _cancel_and_abandon(
                task,
                operation_label=timeout_reason,
                timeout_s=cleanup_allowance_s,
                deadline_expired=True,
                invalidate_bound_scope=False,
                operation_ownership="result_only",
            )
            _observe_and_detach_operation_tail(task)
            return caller_cancellation, None, True

        cleanup_failure: Optional[BaseException] = None
        try:
            task.result()
        except asyncio.CancelledError as child_cancellation:
            if bool(
                getattr(
                    child_cancellation,
                    "_mini_cancellation_cleanup_failed",
                    False,
                )
            ):
                cleanup_failure = child_cancellation
        except BaseException as child_error:
            cleanup_failure = child_error
        return caller_cancellation, cleanup_failure, False

    try:
        done, _pending = await asyncio.wait({task}, timeout=remaining_s)
    except asyncio.CancelledError as caller_cancellation:
        task.cancel()
        # An ancestor's elapsed budget commonly cancels a nested helper before
        # this helper's own deadline.  That is ordinary timeout composition,
        # not proof that the descendant is cancellation-resistant.  Drain the
        # child's provider barrier within the same cleanup allowance and keep
        # ownership until it settles.
        (
            caller_cancellation,
            cleanup_failure,
            cleanup_timed_out,
        ) = await drain_cancelled_child(
            initial_cancellation=caller_cancellation,
            timeout_reason=(
                "recursive_helper_external_cancellation_cleanup_timeout"
            ),
        )
        if cleanup_failure is not None:
            caller_cancellation.add_note(
                "recursive helper cancellation cleanup failed: "
                f"{type(cleanup_failure).__name__}: {cleanup_failure}"
            )
        raise caller_cancellation
    if task in done:
        ok, proof = task.result()
        return bool(ok), proof, False

    task.cancel()
    (
        caller_cancellation,
        cleanup_failure,
        cleanup_timed_out,
    ) = await drain_cancelled_child(
        initial_cancellation=None,
        timeout_reason="recursive_helper_timeout_cleanup_timeout",
    )
    if cleanup_failure is not None:
        if caller_cancellation is not None:
            caller_cancellation.add_note(
                "recursive helper timeout cleanup failed: "
                f"{type(cleanup_failure).__name__}: {cleanup_failure}"
            )
            raise caller_cancellation
        if isinstance(cleanup_failure, asyncio.CancelledError):
            # The helper consumed its elapsed allowance.
            return False, None, True
        # The child has finished, so this is a cleanup-adapter failure rather
        # than a live mathematical exception. Retain caller cancellation
        # precedence and convert this to the same retryable infrastructure
        # yield used for a resistant child tail.
        mutation_lease.abandoned = True
        mutation_lease.late_result_discarded = True
        cleanup_reason = (
            "recursive_helper_timeout_cleanup_failure:"
            f"{type(cleanup_failure).__name__}"
        )
        _recursive_cleanup_infrastructure_outcome(
            child_session,
            reason=cleanup_reason,
        )
        if caller_cancellation is not None:
            caller_cancellation.add_note(
                "recursive helper timeout cleanup failed: "
                f"{type(cleanup_failure).__name__}: {cleanup_failure}"
            )
            raise caller_cancellation
        return False, None, True
    if caller_cancellation is not None:
        raise caller_cancellation
    return False, None, True


def merge_child_theory_context(parent_session: Any, child_session: Any) -> bool:
    """Install a child's dependency-closed theory snapshot before proof replay."""

    bundle_ids = tuple(
        getattr(child_session, "theory_imported_bundle_ids", ()) or ()
    )
    install = getattr(parent_session, "install_theory_bundles", None)
    if not bundle_ids or not callable(install):
        return False
    return bool(install(bundle_ids))



def parent_proof_idea_context_for_child_prompt(
    *,
    parent_session: Any,
    parent_dossier: Any,
    parent_target_graph_node: Any,
) -> str:
    """Return conserved parent cognition for the child prompt.

    Stale or conflicting selected-work packets raise
    ``SelectedProofIdeaContextError`` so the child is not launched
    cognition-blind.
    """

    from .actions.conversation_turn import (
        SelectedProofIdeaContextError,
        _selected_proof_idea_context_for_prompt,
    )

    try:
        return str(
            _selected_proof_idea_context_for_prompt(
                parent_session,
                selected_child_proof_idea_packet(
                    parent_dossier,
                    dict(
                        getattr(parent_session, "selected_work_item_record", {})
                        or {}
                    ),
                    graph_node=parent_target_graph_node,
                    session=parent_session,
                ),
                audience="child",
            )
            or ""
        )
    except SelectedProofIdeaContextError:
        raise
    except (TypeError, ValueError, AttributeError) as exc:
        raise SelectedProofIdeaContextError(
            "selected child cognition binding is stale"
        ) from exc


async def prove_helper_in_subsession(
    *,
    parent_session: Any,
    helper_name: str,
    target_statement: str,
    max_turns: int = 5,
    refine_enabled: bool = False,
    trace_label: str = "",
    nested_node_id: str = "",
    nested_attempt_number: int = 0,
    max_elapsed_s: float = 0.0,
    action_deadline_epoch_s: float = 0.0,
    advisory_refutation_candidates: Sequence[Mapping[str, Any]] = (),
    publication_guard: Optional[Callable[[], None]] = None,
) -> Tuple[bool, Optional[str], Dict[str, Any]]:
    """Prove ONE helper in a child MiniSession.

    Returns ``(ok, proof_text, telemetry)``.

    Args:
        parent_session: the calling MiniSession; donates lean/clients/
            searcher/recorder/proof_cache and provides verified helpers
            seed.
        helper_name: name of the helper goal (used for theorem-decl
            wrapping).
        target_statement: the Lean type signature to prove.
        max_turns: max_prove_turns budget for the sub-conversation.
        refine_enabled: when True, also runs a refine pass (dormant by
            default per Phase 2 design).
        trace_label: prefix for trace lines (e.g. "[helper-recursion d1]").
        max_elapsed_s: total wall-clock allowance for this nested action.
        action_deadline_epoch_s: durable absolute deadline owned by the
            parent action. A restored child reuses it instead of receiving a
            fresh elapsed-time allowance.
        advisory_refutation_candidates: bounded Lean-checked counterexample
            hints that lack a full-negation certificate. They steer the child
            prompt but never carry falsification authority.

    Telemetry payload includes:
        - ``conv_turn_count``: how many ConversationTurnAction
          invocations fired in the child session.
        - ``giveup_cluster``: cluster id if the child session's
          post-failure cascade ever triggered a give-up redirect
          (None if no give-up fired).
        - ``giveup_match``: matched phrase, if any.
        - ``recursion_depth``: child session's depth (parent + 1).
        - ``max_recursion_depth``: cap inherited from parent.
        - ``child_helpers_added``: helper names in child dossier at end-of-run.
        - ``refine_skipped``: True if refine was requested but the
          parent had no refiner_client.
        - ``verdict``: one of "ran" | "empty_target" |
          "depth_cap_exceeded" | "parent_session_required".

    Adversarial review fixes (2026-05-09):
        - Defensive guards: parent_session/dossier/conv None.
        - Empty target_statement validated up front.
        - Depth-cap enforced inside (defense-in-depth, even though
          the action's is_applicable should never call here at cap).
        - answer-related state forced empty/disabled for child sessions.
        - Sanitize orphan tool_calls before refine pass.
        - Merge-back routes through dossier.record_verified_helper
          (which has the answer-unsafe filter), NOT direct
          clone_verified_helper assignment. Skips proposed_name to
          avoid colliding with parent's recheck path.
        - Surface giveup_cluster/giveup_match in telemetry.
        - Recorder events tagged with recursion_depth.
    """

    # Lazy imports to avoid circulars.
    from ensemble_prover.mini_prover import Conversation
    from ensemble_prover.proof_dossier import (
        ProofDossier,
        canonical_dossier_statement_key,
    )
    from ensemble_prover.proof_state import ProofSearchState, lean_referenced_helper_names
    from .actions.child_closure import ChildClosureAction
    from .actions.conversation_turn import ConversationTurnAction
    from .actions.graph_native_shortcut import GraphNativeShortcutAction
    from .actions.graph_route_assembly import GraphRouteAssemblyAction
    from .actions.formal_state_search import FormalStateSearchAction
    from .actions.helper_only_salvage import HelperOnlySalvageAction
    from .actions.inter_turn_assembly import InterTurnAssemblyAction
    from .actions.lemma_dag_decompose import LemmaDagDecomposeAction
    from .actions.premise_retrieval import PremiseRetrievalAction
    from .actions.proof_state_retrieval import ProofStateRetrievalAction
    from .actions.recursive_helper_prover import RecursiveHelperProverAction
    from .actions.tactic_close import RootTacticCloseAction

    # Defensive guards (LOW from review).
    if parent_session is None:
        return False, None, {
            "verdict": "parent_session_required",
            "recursion_depth": 0,
            "child_helpers_added": [],
            "giveup_cluster": None,
            "giveup_match": "",
        }

    parent_dossier = parent_session.dossier
    parent_conv = parent_session.conv
    parent_recursion_depth = int(getattr(parent_session, "recursion_depth", 0) or 0)
    # Aligned with action's _depth_under_cap and nudge convention:
    # ``max_recursion_depth=0`` means "uncapped". Read directly (no
    # ``or 3`` fallback) so 0 stays 0.
    raw_max = getattr(parent_session, "max_recursion_depth", 3)
    max_recursion_depth = int(raw_max if raw_max is not None else 3)
    new_depth = parent_recursion_depth + 1

    target_statement = str(target_statement or "").strip()
    helper_name = str(helper_name or "helper_unknown").strip() or "helper_unknown"

    advisory_lines: list[str] = []
    for raw_finding in tuple(advisory_refutation_candidates or ())[:3]:
        if not isinstance(raw_finding, Mapping):
            continue
        engine = str(raw_finding.get("engine") or "deterministic")[:80]
        reason = " ".join(
            str(raw_finding.get("reason") or "").split()
        )[:400]
        for raw_candidate in tuple(raw_finding.get("candidates") or ())[:3]:
            if not isinstance(raw_candidate, Mapping):
                continue
            witnesses = [
                " ".join(str(item or "").split())[:160]
                for item in tuple(raw_candidate.get("witness_terms") or ())[:8]
                if str(item or "").strip()
            ]
            concrete = " ".join(
                str(raw_candidate.get("concrete_statement") or "").split()
            )[:500]
            details = []
            if witnesses:
                details.append("witnesses: " + ", ".join(witnesses))
            if concrete:
                details.append("instantiated check: " + concrete)
            advisory_lines.append(
                f"- {engine}: {reason}"
                + ("; " + "; ".join(details) if details else "")
            )
    advisory_prompt = ""
    if advisory_lines:
        advisory_prompt = (
            " A Lean-checked counterexample candidate was found, but it is "
            "not yet authority to reject this sub-step:\n"
            + "\n".join(advisory_lines[:6])
            + "\nPrioritize completing a full Lean proof of the negation "
            "with `certify_counterexample`. If certification fails, continue "
            "trying to prove the original sub-step; the candidate alone does "
            "not close it."
        )

    def helper_dependency_closure(
        helpers: Any,
        initial_blocked: set[str],
    ) -> set[str]:
        helper_map = {
            str(name or "").strip(): helper
            for name, helper in (helpers or {}).items()
            if str(name or "").strip()
        }
        all_names = sorted(
            set(helper_map)
            | {str(name or "").strip() for name in initial_blocked}
        )
        blocked = {
            str(name or "").strip()
            for name in initial_blocked
            if str(name or "").strip()
        }
        progressed = True
        while progressed:
            progressed = False
            for name, helper in helper_map.items():
                if name in blocked:
                    continue
                support_names = {
                    str(item or "").strip()
                    for item in list(getattr(helper, "support_names", []) or [])
                    if str(item or "").strip()
                }
                support_names.update(
                    str(item or "").strip()
                    for item in dict(
                        getattr(helper, "support_source_hashes", {}) or {}
                    )
                    if str(item or "").strip()
                )
                refs = lean_referenced_helper_names(
                    str(getattr(helper, "source", "") or ""),
                    all_names,
                    skip=name,
                )
                if blocked.intersection(support_names) or blocked.intersection(refs):
                    blocked.add(name)
                    progressed = True
        return blocked

    # MED: empty target → invalid Lean signature → wasted budget.
    # Refuse here; caller's responsibility to provide a real target.
    if not target_statement:
        return False, None, {
            "verdict": "empty_target",
            "recursion_depth": parent_recursion_depth,
            "child_helpers_added": [],
            "giveup_cluster": None,
            "giveup_match": "",
        }

    # MED: depth cap enforced inside. The action's is_applicable also
    # checks, but defense-in-depth: this function is callable from
    # tests / future actions / direct callers that may bypass the
    # action's gate.
    if max_recursion_depth > 0 and new_depth > max_recursion_depth:
        return False, None, {
            "verdict": "depth_cap_exceeded",
            "recursion_depth": new_depth,
            "max_recursion_depth": max_recursion_depth,
            "child_helpers_added": [],
            "giveup_cluster": None,
            "giveup_match": "",
        }

    if parent_conv is None or parent_session.lean is None or parent_session.prover_client is None:
        return False, None, {
            "verdict": "parent_session_incomplete",
            "recursion_depth": new_depth,
            "child_helpers_added": [],
            "giveup_cluster": None,
            "giveup_match": "",
        }

    from .actions.conversation_turn import SelectedProofIdeaContextError

    parent_graph = getattr(parent_dossier, "proof_graph", None)
    parent_target_graph_node = None
    if parent_graph is not None and nested_node_id:
        parent_target_graph_node = getattr(parent_graph, "nodes", {}).get(
            str(nested_node_id)
        ) or getattr(parent_graph, "nodes", {}).get(
            f"proof_state:{str(nested_node_id)}"
        )
    try:
        selected_parent_proof_idea_context = parent_proof_idea_context_for_child_prompt(
            parent_session=parent_session,
            parent_dossier=parent_dossier,
            parent_target_graph_node=parent_target_graph_node,
        )
    except SelectedProofIdeaContextError as exc:
        return False, None, {
            "verdict": "selected_proof_idea_context_invalidated",
            "preserve_action_budget": True,
            "selected_work_projection_invalidated": True,
            "selected_work_projection_zero_provider": True,
            "scoped_failure_reason": "selected_proof_idea_context_invalidated",
            "projection_error_type": type(exc).__name__,
            "projection_error": str(exc)[:240],
            "recursion_depth": new_depth,
            "child_helpers_added": [],
            "giveup_cluster": None,
            "giveup_match": "",
            "provider_calls_completed": 0,
        }

    def _parent_action(action_id: str) -> Optional[Any]:
        getter = getattr(parent_session, "registered_action", None)
        if callable(getter):
            try:
                return getter(action_id)
            except Exception:
                return None
        return None

    parent_child_closure = _parent_action("child_closure")
    parent_formal_search = _parent_action("formal_state_search")
    parent_root_tactic = _parent_action("tactic_close")
    parent_premise_retrieval = _parent_action("premise_retrieval")
    parent_premise_record = dict(
        getattr(parent_session, "last_premise_retrieval_record", {}) or {}
    )
    parent_premise_retrieval_enabled = bool(
        parent_premise_retrieval is not None
        or (
            parent_premise_record.get("premise_retrieval_enabled") is True
            and parent_premise_record.get("premise_retrieval_searcher_available")
            is True
        )
    )
    parent_premise_top_k = max(
        1,
        int(
            getattr(parent_premise_retrieval, "top_k", 0)
            or parent_premise_record.get("premise_retrieval_top_k")
            or 8
        ),
    )
    parent_retrieval = _parent_action("proof_state_retrieval")
    parent_salvage = _parent_action("helper_only_salvage")
    parent_assembly = _parent_action("inter_turn_assembly")
    parent_route_assembly = _parent_action("graph_route_assembly")
    parent_recursive = _parent_action("recursive_helper_prover")
    parent_prove_action = _parent_action("conversation_turn_prove")
    parent_refine_action = _parent_action("conversation_turn_refine")
    parent_opaque_mode = bool(getattr(parent_conv, "opaque_mode", True))
    parent_allow_official_answer_visibility = bool(
        getattr(parent_conv, "allow_official_answer_visibility", False)
    )
    parent_official_answer_payload_present = getattr(
        parent_conv,
        "official_answer_payload_present",
        getattr(
            parent_dossier,
            "official_answer_payload_present",
            None,
        ),
    )
    from ensemble_prover.proof_dossier import (
        effective_solution_placeholder_suppression,
    )

    effective_placeholder_suppression = (
        effective_solution_placeholder_suppression(
            suppress_solution_placeholders=getattr(
                parent_conv,
                "suppress_solution_placeholders",
                getattr(
                    parent_dossier,
                    "suppress_solution_placeholders",
                    True,
                ),
            ),
            opaque_mode=parent_opaque_mode,
            allow_official_answer_visibility=(
                parent_allow_official_answer_visibility
            ),
            official_answer_payload_present=(
                parent_official_answer_payload_present
            ),
        )
    )
    answer_safety_kwargs = {
        "suppress_solution_placeholders": effective_placeholder_suppression,
        "opaque_mode": parent_opaque_mode,
        "allow_official_answer_visibility": parent_allow_official_answer_visibility,
        "official_answer_payload_present": parent_official_answer_payload_present,
    }
    inherited_child_tactics_action = (
        parent_prove_action or parent_refine_action or parent_recursive
    )
    child_tactics_enabled = bool(
        getattr(
            inherited_child_tactics_action,
            "proof_state_child_tactics_enabled",
            True,
        )
    )
    nested_decomposition_available = bool(
        parent_recursive is not None
        and child_tactics_enabled
        and (max_recursion_depth <= 0 or new_depth < max_recursion_depth)
    )
    # Child helper sessions are proof-only. They may expose failed local
    # Lean artifacts, but the parent/top-level graph scheduler owns mining
    # and scheduling new obligations from those failures.
    nested_decomposition_allowed = False

    # --- Build the child dossier seeded with parent's verified helpers ---
    # MED-3 fix (2026-05-09): seed via record_verified_helper so each
    # seeded helper goes through the answer-unsafe filter
    # (is_answer_unsafe_helper_source) and gets a graph node. Direct
    # clone_verified_helper assignment to the dict skipped the filter,
    # which (combined with the merge-back path below) could leak
    # _solution-named helpers into the child dossier.
    _parent_theorem_name = getattr(parent_dossier, "theorem_name", "?") or "?"
    _parent_root_statement = str(
        getattr(parent_dossier, "root_statement", "") or ""
    )
    # D2 guard (adversarial-review 2026-05-13): if the helper target IS
    # the parent root (degenerate extraction), drop the orientation
    # context to avoid contradicting instructions ("goal is the parent
    # root" + "do not prove the parent root").
    if (
        _parent_root_statement
        and target_statement.strip() == _parent_root_statement.strip()
    ):
        _parent_root_statement = ""
    child_dossier = ProofDossier(
        theorem_name=helper_name,
        root_statement=target_statement,
        cache_owner_theorem_name=str(
            getattr(parent_dossier, "cache_owner_theorem_name", "")
            or getattr(parent_dossier, "theorem_name", "")
            or ""
        ),
        proof_cache_publish_enabled=False,
        graph_execution_projection_mode=str(
            getattr(parent_dossier, "graph_execution_projection_mode", "off")
            or "off"
        ),
        graph_execution_project_environment_hash=str(
            getattr(
                parent_dossier,
                "graph_execution_project_environment_hash",
                "",
            )
            or ""
        ),
        # Inherit the parent's Lean environment lattice so seeded
        # parent-verified helpers remain interpretable after the child
        # session re-syncs its preamble hash.
        current_lean_environment_hash=str(
            getattr(parent_dossier, "current_lean_environment_hash", "") or ""
        ),
        lean_environment_ancestor_hashes=copy.deepcopy(
            getattr(parent_dossier, "lean_environment_ancestor_hashes", {}) or {}
        ),
        lean_environment_content_digests=copy.deepcopy(
            getattr(parent_dossier, "lean_environment_content_digests", {}) or {}
        ),
        problem_text=(
            "Sub-step proving task for parent theorem "
            f"{_parent_theorem_name}. The signature below is one sub-step "
            "of that proof; the variables and hypotheses bound in its "
            "signature are the parent's local context, frozen at the "
            "point this sub-step was extracted. The sub-step is part of "
            "the parent's proof, not a free invitation to rewrite the "
            "root theorem. First try to prove it relative to those "
            "bindings. If Lean or a concrete instance shows the extracted "
            "sub-step is false or overgeneralized, submit a Lean artifact "
            "showing the concrete counterexample, inconsistent premises, or "
            "failed local `have`/`suffices` attempt instead of decomposing it "
            "further. Counterexample evidence must assign the variables, "
            "satisfy every premise, and violate the conclusion; test simple "
            "candidate counterexamples with Lean or direct arithmetic before "
            "relying on them. Do not emit a standalone defect note. (If the sub-step "
            "is itself a negation like `¬ P x` or `a ≠ b`, proving it by "
            "deriving a contradiction from the positive form is still "
            "proving the sub-step, not refuting it.) Verified helpers "
            "already proven for the parent appear in the Lean preamble."
            + (
                f" Parent root statement (for orientation only, NOT to "
                f"be proved here): {_parent_root_statement}"
                if _parent_root_statement
                else ""
            )
            + advisory_prompt
        ),
        opaque_mode=parent_opaque_mode,
        allow_official_answer_visibility=parent_allow_official_answer_visibility,
        official_answer_payload_present=parent_official_answer_payload_present,
        suppress_solution_placeholders=effective_placeholder_suppression,
    )
    if parent_target_graph_node is None:
        parent_graph = getattr(parent_dossier, "proof_graph", None)
        if parent_graph is not None and nested_node_id:
            parent_target_graph_node = getattr(parent_graph, "nodes", {}).get(
                str(nested_node_id)
            ) or getattr(parent_graph, "nodes", {}).get(
                f"proof_state:{str(nested_node_id)}"
            )
    child_proof_idea_ids, child_proof_idea_branch_id = (
        seed_relevant_proof_ideas_for_child(
            child_dossier,
            parent_dossier,
            lineage_sources=(
                dict(
                    getattr(parent_session, "selected_work_item_record", {})
                    or {}
                ),
                dict(
                    getattr(parent_target_graph_node, "metadata", {}) or {}
                ),
            ),
            branch_source="recursive-helper-child",
            branch_key=(
                f"{helper_name}:{str(nested_node_id or target_statement)}:"
                f"{int(nested_attempt_number or 0)}"
            ),
        )
    )
    from ensemble_prover.proof_dossier import is_answer_unsafe_helper_source

    child_seeded_helpers: list[str] = []
    child_seeded_proposed_helpers: list[str] = []
    child_skipped_solution_helpers: list[str] = []
    child_skipped_target_dependent_helpers: list[str] = []
    if parent_dossier is not None:
        child_dossier.superseded_verified_helper_hashes = {
            str(name): [str(value) for value in list(values or [])]
            for name, values in (
                getattr(parent_dossier, "superseded_verified_helper_hashes", {})
                or {}
            ).items()
        }
        child_dossier.verified_helper_source_hash_history = {
            str(name): [str(value) for value in list(values or [])]
            for name, values in (
                getattr(parent_dossier, "verified_helper_source_hash_history", {})
                or {}
            ).items()
        }
        target_dependent_names = helper_dependency_closure(
            getattr(parent_dossier, "verified_helpers", {}) or {},
            {helper_name},
        )
        parent_helper_items = list(
            (parent_dossier.verified_helpers or {}).items()
        )
        for name, helper in dependency_ordered_verified_helper_items(
            parent_helper_items
        ):
            # Skip helpers whose name matches the child's theorem (would
            # cause Lean dup-decl rejection — adversarial review LOW-MED).
            if name == helper_name:
                continue
            if str(name or "").strip() in target_dependent_names:
                child_skipped_target_dependent_helpers.append(str(name or ""))
                continue
            source = str(getattr(helper, "source", "") or "")
            if not source:
                continue
            if is_answer_unsafe_helper_source(source, **answer_safety_kwargs):
                child_skipped_solution_helpers.append(str(name or ""))
                continue
            try:
                seeded = child_dossier.record_imported_verified_helper(
                    helper,
                    phase=str(
                        getattr(helper, "phase", "parent_seed")
                        or "parent_seed"
                    ),
                )
                if seeded is not None:
                    child_seeded_helpers.append(str(name or seeded.name))
            except Exception:
                # Best-effort: seed failure shouldn't abort. The child
                # may proceed with a smaller helper context.
                pass
        from ..proof_dossier import propagate_invalidated_statements

        propagate_invalidated_statements(
            child_dossier,
            parent_dossier,
            record_graph=False,
        )
        # Child helper sessions are proof-only. Verified parent helpers are
        # usable proof facts; unproved parent proposals are decomposition
        # hints and must not leak into a child whose job is to close exactly
        # one statement.

    # --- Build the child conversation rooted at the helper goal ---
    parent_preamble = str(getattr(parent_conv, "preamble", "") or "")
    raw_parent_lean_preamble = getattr(parent_conv, "lean_preamble", None)
    parent_lean_preamble = str(
        parent_preamble
        if raw_parent_lean_preamble is None
        else raw_parent_lean_preamble
    )
    # Helper sub-prover targets ONLY the helper statement. Force answer-related
    # state empty/disabled so stale parent records cannot affect verification.
    total_turn_budget = max(1, int(max_turns or 1))
    refine_turn_budget = (
        1
        if bool(refine_enabled)
        and parent_session.refiner_client is not None
        and total_turn_budget > 1
        else 0
    )
    prove_turn_budget = max(1, total_turn_budget - refine_turn_budget)

    lean_signature = (
        f"theorem {helper_name} : {target_statement} := by\n  -- prove this helper"
    )

    child_conv = Conversation(
        role="prove",
        goal_statement=target_statement,
        problem_text=child_dossier.problem_text,
        lean_signature=lean_signature,
        preamble=parent_preamble,
        lean_preamble=parent_lean_preamble,
        turn_budget=prove_turn_budget,
        opaque_mode=parent_opaque_mode,
        allow_official_answer_visibility=parent_allow_official_answer_visibility,
        official_answer_payload_present=parent_official_answer_payload_present,
        suppress_solution_placeholders=effective_placeholder_suppression,
        allow_helper_decomposition=nested_decomposition_allowed,
    )
    decomposition_instruction = (
        "Do not emit new proposed helper obligations, helper-DAG plans, "
        "or sorry-stub theorem declarations in this child session. "
        "Manufacture any needed local theory inside the proof body with "
        "proved `have`/`suffices` steps. If the helper still fails, submit "
        "the concrete failed local `have`/`suffices` attempt and Lean "
        "diagnostics so the parent graph can mine follow-up work. Do not "
        "use absence of a convenient library lemma as the turn outcome."
    )
    if selected_parent_proof_idea_context:
        selected_context_message = child_conv.append_user(
            "Untrusted conserved proof-strategy lifecycle for the exact "
            "selected parent route, claim, and branch; Lean remains "
            "authoritative:\n"
            f"{selected_parent_proof_idea_context}"
        )
        selected_context_message["pinned"] = True
        selected_context_message["_required_prompt_context"] = {
            "kind": "recursive_helper_child_proof_idea_lifecycle",
            "units": [
                "selected_route",
                "selected_claim",
                "selected_branch",
                "current_attempt",
                "current_lean_residual",
            ],
        }
    child_conv.append_user(
        "You are proving ONE sub-step of the parent theorem identified "
        "above. The signature shown is the sub-step's obligation under "
        "the parent's bound variables and hypotheses; treat its "
        "premises as already-true facts (they come from the parent's "
        "hypotheses or earlier verified helpers) and prove its "
        "conclusion. This sub-step is a STEP TOWARD the parent — not "
        "an independent universal claim — so it is NOT your job to "
        "evaluate whether the parent itself is true; the parent search "
        "owns that. Still, do not blindly decompose a false extracted "
        "obligation: if the sub-step itself has a concrete counterexample, "
        "a contradictory hypothesis set, or a Lean-checkable reason it is "
        "overgeneralized, submit the Lean artifact or concrete failed local "
        "`have`/`suffices` attempt that exposes it so the parent can repair "
        "the claim. Counterexample evidence must check every premise of the "
        "sub-step, not just the conclusion; an invalid candidate is evidence "
        "to keep proving, not evidence to abandon the claim. Do not emit a "
        "standalone defect note. "
        "(Negation-shaped sub-steps like `¬ P x` or `a ≠ b` are still "
        "proved by deriving a contradiction from the positive form — "
        "that IS proving the sub-step, not refuting it.) Verified "
        "parent-side helpers are in Lean scope and may be cited by "
        "name. If the signature contains Fin indices, finite sums, or "
        "integer-valued indexed arithmetic, cast indices explicitly "
        "before normalization or ring/omega reasoning; do not let "
        "numerals or subtraction live at type Fin n. If the direct route "
        "does not close, keep working through Lean artifacts: prove the "
        "needed bridge from smaller local facts or pivot to a different "
        "formal route. "
        + decomposition_instruction
    )

    # --- Build the child proof state ---
    child_proof_state = ProofSearchState(
        theorem_name=helper_name,
        root_statement=target_statement,
        suppress_solution_placeholders=effective_placeholder_suppression,
        statement_environment_hash=str(
            getattr(child_dossier, "current_lean_environment_hash", "") or ""
        ).strip(),
    )
    # A recursive-helper action owns one concrete parent proof-state node.
    # Premise retrieval attached to that node is already target-specific and
    # remains valid when the same target is re-rooted in a child session.
    # Preserve that durable work memory instead of forcing the child to search
    # blind (or repay the same query) before formal-state search.  Never copy
    # session-wide/root hints here: those may describe a different theorem.
    parent_target_node = None
    if nested_node_id:
        parent_target_node = getattr(
            getattr(parent_session, "proof_state", None),
            "nodes",
            {},
        ).get(str(nested_node_id))
    if (
        parent_target_node is not None
        and canonical_dossier_statement_key(
            str(getattr(parent_target_node, "target", "") or "")
        )
        != canonical_dossier_statement_key(target_statement)
    ):
        parent_target_node = None
    inherited_target_premises = tuple(
        dict.fromkeys(
            str(name or "").strip()
            for name in list(
                getattr(parent_target_node, "retrieved_decl_names", ()) or ()
            )
            if str(name or "").strip()
        )
    )
    child_root_node = child_proof_state.nodes.get(child_proof_state.root_node_id)
    if child_root_node is not None and inherited_target_premises:
        child_root_node.retrieved_decl_names = list(inherited_target_premises)

    # --- Build the slim child MiniSession ---
    from .searcher_context import fork_searcher_context

    child_theory_library = getattr(parent_session, "theory_library", None)
    child_searcher = fork_searcher_context(
        parent_session.searcher,
        theory_enabled=bool(
            child_theory_library is not None
            and getattr(child_theory_library, "mode", "off") != "off"
        ),
    )
    child_session = MiniSession(
        problem=parent_session.problem,  # provenance only; not used in slim mode
        dossier=child_dossier,
        proof_state=child_proof_state,
        proof_cache=parent_session.proof_cache,
        conv=child_conv,
        lean=parent_session.lean,
        prover_client=parent_session.prover_client,
        refiner_client=parent_session.refiner_client if refine_enabled else None,
        searcher=child_searcher,
        recorder=parent_session.recorder,
        cost_controller=getattr(parent_session, "cost_controller", None),
        trace_prefix=str(parent_session.trace_prefix or "") + str(trace_label or ""),
        recursion_depth=new_depth,
        max_recursion_depth=max_recursion_depth,
        # Tight iteration cap: 1 LLM turn + cascade overhead per helper turn.
        max_iterations=int(max_turns or 1) + 5,
        scope="subgoal",
        parent=parent_session,
        theory_library=child_theory_library,
        theory_candidate_builder=getattr(
            parent_session, "theory_candidate_builder", None
        ),
        theory_context_pair=getattr(parent_session, "theory_context_pair", None),
        theory_domain=str(
            getattr(parent_session, "theory_domain", "general mathematics")
            or "general mathematics"
        ),
        theory_default_imports=tuple(
            getattr(parent_session, "theory_default_imports", ("Mathlib",))
            or ("Mathlib",)
        ),
        theory_imported_bundle_ids=tuple(
            getattr(parent_session, "theory_imported_bundle_ids", ()) or ()
        ),
        theory_snapshot=tuple(
            getattr(parent_session, "theory_snapshot", ()) or ()
        ),
        conversation_budget_topups_enabled=False,
    )
    # Recursive helper actions registered inside this child must not mint a
    # fresh wall-clock budget beyond the durable owner that created it.
    # putnam_2025_b1's outer child expired at t~=1284 while an inner helper
    # had incorrectly reset itself to t~=1857, converting ordinary nested
    # timeout composition into external cancellation and a hard watchdog kill.
    child_session.recursive_elapsed_deadline_epoch_s = max(
        0.0,
        float(action_deadline_epoch_s or 0.0),
    )
    child_session.configure_no_applicable_recovery(total_turn_budget)
    if child_searcher is not None and parent_premise_retrieval_enabled:
        # Mathematical retrieval is target-specific.  Inheriting only the
        # parent's searcher (or its root-query result) leaves a newly scoped
        # helper searching blindly.  Give the child its own one-shot prepass;
        # MiniSession's root-repair gate already guarantees this priority-5
        # action runs before formal-state search.
        child_session.register(
            PremiseRetrievalAction(top_k=parent_premise_top_k)
        )
        child_session.set_budget(
            "premise_retrieval",
            ActionBudget(max_invocations=1, max_total_seconds=0.0),
        )
    if child_session.theory_library is not None:
        from .actions.domain_theory import DomainTheoryAction

        child_session.register(
            DomainTheoryAction(
                stage="retrieve",
                id="domain_theory",
            )
        )
        child_session.set_budget(
            "domain_theory",
            ActionBudget(max_invocations=2, max_total_seconds=0.0),
        )
        if getattr(child_session.theory_library, "mode", "off") == "build":
            child_session.register(
                DomainTheoryAction(
                    candidate_builder=child_session.theory_candidate_builder,
                    stage="build",
                    id="domain_theory_build",
                )
            )
            child_session.set_budget(
                "domain_theory_build",
                ActionBudget(max_invocations=4, max_total_seconds=0.0),
            )

    child_timeout_s = float(
        getattr(
            parent_child_closure,
            "timeout_s",
            DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        )
        or DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S
    )
    child_max_nodes = int(getattr(parent_child_closure, "max_nodes", 3) or 3)
    child_max_candidates = int(
        getattr(parent_child_closure, "max_candidates", 32) or 32
    )
    child_max_decl_apps = int(
        getattr(parent_child_closure, "max_decl_applications", 6) or 6
    )
    child_parallelism = int(getattr(parent_child_closure, "batch_parallelism", 1) or 1)
    route_root_tactic_timeout_s = float(
        getattr(parent_route_assembly, "root_tactic_timeout_s", 40.0) or 0.0
    )
    route_root_tactic_max_candidates = int(
        getattr(parent_route_assembly, "root_tactic_max_candidates", 64) or 0
    )
    # ``or 6`` on a missing parent action made this unconditionally truthy, so
    # the child registered proof_state_retrieval even when the parent had none.
    child_retrieval_results = (
        int(getattr(parent_retrieval, "max_results", 6) or 6)
        if parent_retrieval is not None
        else 0
    )
    parent_failure_owner = parent_prove_action or parent_refine_action or parent_recursive
    child_repair_top_k = int(
        getattr(parent_failure_owner, "repair_retrieval_top_k", 6) or 6
    )
    child_raw_feedback = bool(getattr(parent_failure_owner, "raw_feedback", False))

    def _positive_float(value: Any) -> float:
        try:
            number = float(value or 0.0)
        except Exception:
            return 0.0
        return number if number > 0.0 else 0.0

    def _client_llm_turn_elapsed_budget_s(client: Any) -> float:
        cfg = getattr(client, "cfg", None)
        if cfg is None:
            return 0.0
        policy = str(
            getattr(cfg, "llm_deadline_policy", "soft") or "soft"
        ).strip().lower()
        if policy != "hard":
            return 0.0
        operation_timeout_s = _positive_float(
            getattr(cfg, "operation_timeout_s", 0.0)
        )
        if operation_timeout_s > 0.0:
            return operation_timeout_s
        request_timeout_s = _positive_float(getattr(cfg, "timeout_s", 0.0))
        if request_timeout_s > 0.0:
            # Match the provider client's fallback operation window and the
            # root factory: one request timeout plus one retry window.
            return request_timeout_s * 2.0
        return 0.0

    def _conversation_turn_kwargs(
        *,
        role: str,
        client: Any,
        parent_action: Optional[Any],
        turn_budget: int,
    ) -> Dict[str, Any]:
        action = parent_action or parent_prove_action
        llm_turn_elapsed_s = _positive_float(
            getattr(action, "llm_turn_elapsed_s", 0.0) if action else 0.0
        )
        if llm_turn_elapsed_s <= 0.0:
            llm_turn_elapsed_s = _client_llm_turn_elapsed_budget_s(client)
        formalization_llm_turn_elapsed_s = _positive_float(
            getattr(action, "formalization_llm_turn_elapsed_s", 0.0)
            if action
            else 0.0
        )
        if formalization_llm_turn_elapsed_s <= 0.0:
            formalization_llm_turn_elapsed_s = llm_turn_elapsed_s
        formalization_llm_request_timeout_s = _positive_float(
            getattr(action, "formalization_llm_request_timeout_s", 0.0)
            if action
            else 0.0
        )
        return {
            "role": role,
            "client": client,
            "sample_temperature": getattr(action, "sample_temperature", None)
            if action
            else None,
            "mini_phase_temperatures": getattr(
                action,
                "mini_phase_temperatures",
                None,
            )
            if action
            else None,
            # Every retrieval entry point in the child must use the isolated
            # session view.  Inheriting the parent action's override would
            # bypass ``child_session.searcher`` and reintroduce theory
            # visibility leaks through ConversationTurnAction tools.
            "searcher_override": child_searcher,
            "lean_check_tool_enabled": bool(
                getattr(action, "lean_check_tool_enabled", True)
                if action
                else True
            ),
            "try_lean_tool_enabled": bool(
                getattr(action, "try_lean_tool_enabled", False)
                if action
                else False
            ),
            "compute_examples_tool_enabled": bool(
                getattr(action, "compute_examples_tool_enabled", False)
                if action
                else False
            ),
            "apply_decl_to_goal_tool_enabled": bool(
                getattr(action, "apply_decl_to_goal_tool_enabled", False)
                if action
                else False
            ),
            "max_tool_calls_per_turn": max(
                0,
                min(
                    10,
                    int(
                        getattr(action, "max_tool_calls_per_turn", 10)
                        if action
                        else 10
                    ),
                ),
            ),
            "raw_feedback": bool(
                getattr(action, "raw_feedback", child_raw_feedback)
                if action
                else child_raw_feedback
            ),
            "repair_retrieval_enabled": bool(
                getattr(action, "repair_retrieval_enabled", True)
                if action
                else True
            ),
            "repair_retrieval_top_k": int(
                getattr(action, "repair_retrieval_top_k", child_repair_top_k)
                if action
                else child_repair_top_k
            ),
            "proof_state_child_tactics_enabled": bool(
                getattr(action, "proof_state_child_tactics_enabled", child_tactics_enabled)
                if action
                else child_tactics_enabled
            ),
            "proof_state_child_tactic_timeout_s": float(
                getattr(action, "proof_state_child_tactic_timeout_s", child_timeout_s)
                if action
                else child_timeout_s
            ),
            "proof_state_child_tactic_max_candidates": int(
                getattr(
                    action,
                    "proof_state_child_tactic_max_candidates",
                    child_max_candidates,
                )
                if action
                else child_max_candidates
            ),
            "proof_state_child_goal_limit": int(
                getattr(action, "proof_state_child_goal_limit", child_max_nodes)
                if action
                else child_max_nodes
            ),
            "proof_state_decl_application_limit": int(
                getattr(
                    action,
                    "proof_state_decl_application_limit",
                    child_max_decl_apps,
                )
                if action
                else child_max_decl_apps
            ),
            "proof_state_batch_parallelism": int(
                getattr(action, "proof_state_batch_parallelism", child_parallelism)
                if action
                else child_parallelism
            ),
            "max_turns_for_budget": turn_budget,
            "llm_turn_elapsed_s": llm_turn_elapsed_s,
            "formalization_llm_request_timeout_s": formalization_llm_request_timeout_s,
            "formalization_llm_turn_elapsed_s": formalization_llm_turn_elapsed_s,
        }

    # Graph route/native closers are structural graph consumers, not tactic
    # swarms. Keep them available even when child tactics are disabled.
    route_budget_invocations = max(1, total_turn_budget + 2)
    child_session.register(
        GraphRouteAssemblyAction(
            max_routes=child_max_nodes,
            root_tactic_timeout_s=route_root_tactic_timeout_s,
            root_tactic_max_candidates=route_root_tactic_max_candidates,
        )
    )
    child_session.set_budget(
        "graph_route_assembly",
        ActionBudget(
            max_invocations=route_budget_invocations,
            max_total_seconds=max(
                30.0,
                float(route_budget_invocations)
                * max(1.0, route_root_tactic_timeout_s)
                + 30.0,
            ),
        ),
    )
    child_session.register(GraphNativeShortcutAction())
    child_session.set_budget(
        "graph_native_shortcut",
        ActionBudget(max_invocations=max(1, total_turn_budget + 2), max_total_seconds=30.0),
    )

    if child_tactics_enabled:
        # Register the proof-state actions that let child sessions act like
        # real scoped prover sessions. Without this, a helper sub-session
        # could emit a give-up decomposition, materialize child goals, and
        # then never dispatch nested recursive proving for those children.
        child_session.register(
            InterTurnAssemblyAction(
                timeout_s=float(
                    getattr(parent_assembly, "timeout_s", child_timeout_s) or 0.0
                ),
                max_nodes=int(
                    getattr(parent_assembly, "max_nodes", child_max_nodes) or 0
                ),
            )
        )
        child_session.set_budget(
            "inter_turn_assembly",
            ActionBudget(
                max_invocations=max(1, total_turn_budget + 2),
                max_total_seconds=90.0,
            ),
        )
        # The deterministic root closer is gated on the parent's OWN root
        # tactic action, not on formal search. Gating it on formal search made
        # tactic_close vanish from every helper sub-session the moment formal
        # search went default-off, silently removing a closer the recursive
        # lane depends on and which --root-tactic-prepass could only restore
        # at the root.
        if parent_root_tactic is not None:
            child_session.register(
                RootTacticCloseAction(
                    phase="root_tactic_prepass",
                    timeout_s=float(
                        getattr(parent_root_tactic, "timeout_s", child_timeout_s)
                        or 0.0
                    ),
                    max_candidates=int(
                        getattr(
                            parent_root_tactic,
                            "max_candidates",
                            child_max_candidates,
                        )
                        or 0
                    ),
                )
            )
            child_session.set_budget(
                "tactic_close",
                ActionBudget(
                    max_invocations=max(2, total_turn_budget * 2),
                    max_total_seconds=60.0,
                ),
            )
            child_session.register(
                FormalStateSearchAction(config=parent_formal_search.config)
            )
            from .factory import (
                _formal_state_search_aggregate_seconds as _formal_aggregate_seconds,
            )

            child_session.set_budget(
                "formal_state_search",
                ActionBudget(
                    max_invocations=-1,
                    max_total_seconds=0.0,
                    scope="formal_context",
                    # Per-context no-improvement quanta reset on any rank or
                    # novelty gain and restart for each new context key, so they
                    # bound a single identity but never the total.  Declare the
                    # aggregate ceiling the design already implies: the whole
                    # no-improvement allowance spent end to end.
                    max_aggregate_seconds=_formal_aggregate_seconds(
                        parent_formal_search.config
                    ),
                ),
            )
        child_session.register(
            HelperOnlySalvageAction(
                timeout_s=float(
                    getattr(parent_salvage, "timeout_s", child_timeout_s) or 0.0
                ),
                max_nodes=int(
                    getattr(parent_salvage, "max_nodes", child_max_nodes) or 0
                ),
                max_candidates=int(
                    getattr(parent_salvage, "max_candidates", child_max_candidates)
                    or 0
                ),
                max_decl_applications=int(
                    getattr(parent_salvage, "max_decl_applications", child_max_decl_apps)
                    or 0
                ),
                batch_parallelism=int(
                    getattr(parent_salvage, "batch_parallelism", child_parallelism)
                    or 1
                ),
            )
        )
        child_session.set_budget(
            "helper_only_salvage",
            ActionBudget(
                max_invocations=max(1, total_turn_budget),
                max_total_seconds=120.0,
            ),
        )
        child_session.set_budget(
            "post_lean_failure",
            ActionBudget(
                max_invocations=max(1, total_turn_budget),
                max_total_seconds=180.0,
            ),
        )
    if (
        child_tactics_enabled
        and parent_retrieval is not None
        and child_retrieval_results > 0
    ):
        child_session.register(
            ProofStateRetrievalAction(
                max_nodes=int(getattr(parent_retrieval, "max_nodes", child_max_nodes) or 0),
                max_results=child_retrieval_results,
            )
        )
        child_session.set_budget(
            "proof_state_retrieval",
            ActionBudget(max_invocations=max(1, total_turn_budget), max_total_seconds=60.0),
        )
    if child_tactics_enabled:
        child_closure_action = ChildClosureAction(
            timeout_s=child_timeout_s,
            max_candidates=child_max_candidates,
            max_nodes=child_max_nodes,
            max_decl_applications=child_max_decl_apps,
            batch_parallelism=child_parallelism,
            formal_search_config=getattr(
                parent_child_closure,
                "formal_search_config",
                None,
            ),
        )
        child_session.register(child_closure_action)
        child_session.set_budget(
            "child_closure",
            ActionBudget(
                max_invocations=max(2, total_turn_budget),
                max_total_seconds=0.0,
            ),
        )
    if child_tactics_enabled and bool(getattr(child_conv, "allow_helper_decomposition", True)):
        child_session.register(LemmaDagDecomposeAction(timeout_s=child_timeout_s))
        child_session.set_budget(
            "lemma_dag_decompose",
            ActionBudget(
                max_invocations=max(1, total_turn_budget),
                max_total_seconds=0.0,
            ),
        )
    if child_tactics_enabled and parent_recursive is not None and bool(
        getattr(child_conv, "allow_helper_decomposition", True)
    ):
        child_session.register(
            RecursiveHelperProverAction(
                max_attempts_per_node=int(
                    getattr(parent_recursive, "max_attempts_per_node", 2)
                    if getattr(parent_recursive, "max_attempts_per_node", 2)
                    is not None
                    else 2
                ),
                max_giveups_per_cluster_per_node=int(
                    getattr(
                        parent_recursive,
                        "max_giveups_per_cluster_per_node",
                        2,
                    )
                    or 2
                ),
                helper_turns=int(getattr(parent_recursive, "helper_turns", max_turns) or max_turns),
                refine_enabled=bool(getattr(parent_recursive, "refine_enabled", False)),
                max_elapsed_s=float(
                    getattr(parent_recursive, "max_elapsed_s", max_elapsed_s)
                    or 0.0
                ),
            )
        )
        child_session.set_budget(
            "recursive_helper_prover",
            ActionBudget(
                max_invocations=max(1, total_turn_budget),
                max_total_seconds=300.0,
            ),
        )

    # --- Register the prove ConversationTurnAction ---
    prove_action = ConversationTurnAction(
        **_conversation_turn_kwargs(
            role="prove",
            client=parent_session.prover_client,
            parent_action=parent_prove_action,
            turn_budget=prove_turn_budget,
        )
    )
    child_session.register(prove_action)
    child_session.set_budget(
        prove_action.id,
        ActionBudget(
            max_invocations=prove_turn_budget,
            max_total_seconds=0.0,  # count-based cap matches root behavior
        ),
    )
    refine_action: Optional[ConversationTurnAction] = None
    refine_registered = False
    if (
        bool(refine_enabled)
        and parent_session.refiner_client is not None
        and refine_turn_budget > 0
    ):
        # Register refine before the first child run. Otherwise the prove
        # phase uses "no applicable action" as an implicit phase boundary,
        # which burns terminal scheduler telemetry and can strand remaining
        # deterministic repair work behind a max_recoveries=0 child session.
        refine_action = ConversationTurnAction(
            **_conversation_turn_kwargs(
                role="refine",
                client=parent_session.refiner_client,
                parent_action=parent_refine_action,
                turn_budget=refine_turn_budget,
            )
        )
        child_session.register(refine_action)
        child_session.set_budget(
            refine_action.id,
            ActionBudget(
                max_invocations=refine_turn_budget,
                max_total_seconds=0.0,
            ),
        )
        refine_registered = True
    child_session.expand_max_iterations_to_action_budgets(headroom=5)

    def merge_eligible_child_verified_helpers() -> None:
        """Admit timeout/success side helpers through the parent trust gates."""

        if parent_dossier is None:
            return
        child_target_dependent_names = helper_dependency_closure(
            getattr(child_dossier, "verified_helpers", {}) or {},
            {helper_name},
        )
        incoming_helpers = [
            (str(name or "").strip(), helper)
            for name, helper in (child_dossier.verified_helpers or {}).items()
            if str(name or "").strip()
            and str(name or "").strip() != helper_name
            and str(name or "").strip() not in child_target_dependent_names
        ]
        eligible_incoming_helpers = []
        for name, helper in incoming_helpers:
            source = str(getattr(helper, "source", "") or "")
            if not source or is_answer_unsafe_helper_source(
                source,
                **answer_safety_kwargs,
            ):
                continue
            existing = getattr(parent_dossier, "verified_helpers", {}).get(name)
            helper_hash = str(getattr(helper, "source_hash", "") or "")
            existing_hash = str(getattr(existing, "source_hash", "") or "")
            if (
                existing is not None
                and existing_hash != helper_hash
                and helper_source_hash_was_superseded(
                    parent_dossier,
                    name,
                    helper_hash,
                )
            ):
                continue
            if helper_uses_superseded_support(parent_dossier, helper):
                continue
            eligible_incoming_helpers.append((name, helper))
        incoming_helpers = preflight_dependency_ordered_verified_helper_items(
            parent_dossier,
            eligible_incoming_helpers,
        )
        for name, helper in incoming_helpers:
            existing = getattr(parent_dossier, "verified_helpers", {}).get(name)
            if existing is not None and str(
                getattr(existing, "source_hash", "") or ""
            ) == str(getattr(helper, "source_hash", "") or ""):
                if helper_provenance_is_trust_monotone(
                    parent_dossier,
                    existing,
                    helper,
                ):
                    parent_dossier.record_imported_verified_helper(helper)
                continue
            source = str(getattr(helper, "source", "") or "")
            if not source or is_answer_unsafe_helper_source(
                source,
                **answer_safety_kwargs,
            ):
                continue
            try:
                parent_dossier.record_imported_verified_helper(
                    helper,
                    phase=str(
                        getattr(helper, "phase", "recursive_helper_prover")
                        or "recursive_helper_prover"
                    ),
                )
            except Exception:
                # Parent admission is deliberately fail-closed.
                pass
        if getattr(parent_dossier, "proof_graph", None) is not None:
            verified_names = set(
                getattr(parent_dossier, "verified_helpers", {}) or {}
            )
            graph_helper_names = set(
                getattr(
                    parent_dossier.proof_graph,
                    "helper_name_to_node_id",
                    {},
                )
                or {}
            )
            for stale_name in sorted(graph_helper_names - verified_names):
                parent_dossier.proof_graph.remove_helper(stale_name)

    # --- Drive the child prove session ---
    # Defense-in-depth: sanitize orphan tool_calls before driving the
    # child loop. The parent's prover may have left an unconsumed
    # assistant tool_calls entry in conv.history; the child's first
    # OpenAI call would 400 on that. (Bonus #4 carried forward.)
    sanitize_orphan = getattr(child_conv, "sanitize_orphan_tool_calls", None)
    if callable(sanitize_orphan):
        try:
            sanitize_orphan()
        except Exception:
            pass
    ok, proof_text, action_elapsed_budget_exhausted = (
        await _run_child_with_elapsed_budget(
            child_session,
            max_elapsed_s=max_elapsed_s,
            deadline_epoch_s=action_deadline_epoch_s,
        )
    )
    # Sanitize again after the prove pass so a refine pass (when
    # enabled) doesn't inherit an orphan from the prove cascade.
    if callable(sanitize_orphan):
        try:
            sanitize_orphan()
        except Exception:
            pass

    last_action_metadata = dict(
        getattr(child_session, "last_action_outcome_metadata", {}) or {}
    )
    cleanup_infrastructure_outcome = dict(
        getattr(child_session, _RECURSIVE_CLEANUP_OUTCOME_ATTR, {}) or {}
    )
    child_provider_calls_completed, child_provider_dispatches_started = (
        _child_provider_exposure(
            child_session,
            include_inflight=action_elapsed_budget_exhausted,
        )
    )
    child_llm_failure_kind = str(
        last_action_metadata.get("llm_failure_kind") or ""
    ).strip()
    child_llm_error = str(last_action_metadata.get("llm_error") or "").strip()
    child_llm_retryable = bool(last_action_metadata.get("llm_retryable"))

    if action_elapsed_budget_exhausted:
        cleanup_infrastructure_yield = bool(cleanup_infrastructure_outcome)
        if not cleanup_infrastructure_yield:
            child_session.terminal_failure_reason = (
                "recursive_helper_action_elapsed_budget_exhausted"
            )
            child_session.terminal_failure_kind = "action_elapsed_budget"
        # Cancellation settles the child before this branch.  Preserve useful
        # Lean-verified side work exactly as on the normal return path, while
        # still excluding the target helper and its dependency closure.  The
        # parent theory install and helper admission routines are the same
        # fail-closed gates used after a non-timeout child run.
        # A cleanup-resistant child is deliberately *not* quiescent. Its
        # speculative in-memory helpers cannot be admitted; the last durable
        # nested cutpoint remains the only retry authority.
        if not cleanup_infrastructure_yield:
            if publication_guard is not None:
                publication_guard()
            merge_child_theory_context(parent_session, child_session)
            if publication_guard is not None:
                publication_guard()
            merge_eligible_child_verified_helpers()
        telemetry = {
            "conv_turn_count": int(
                getattr(child_session, "_conversation_turn_count", 0) or 0
            ),
            "iteration": int(getattr(child_session, "iteration", 0) or 0),
            "stagnation_counter": int(
                getattr(child_session, "stagnation_counter", 0) or 0
            ),
            "recursion_depth": new_depth,
            "max_recursion_depth": max_recursion_depth,
            "child_seeded_helpers": child_seeded_helpers,
            "child_seeded_proposed_helpers": child_seeded_proposed_helpers,
            "child_skipped_solution_helpers": child_skipped_solution_helpers,
            "child_skipped_target_dependent_helpers": (
                child_skipped_target_dependent_helpers
            ),
            "child_helpers_added": list(child_dossier.verified_helpers.keys()),
            "giveup_cluster": None,
            "giveup_match": "",
            "child_goal_falsified": False,
            "falsification_certificate_hash": "",
            "refine_attempted": False,
            "refine_solved": False,
            "refine_skipped": bool(refine_enabled),
            "refine_skip_reason": (
                "recursive_helper_cleanup_infrastructure_yield"
                if cleanup_infrastructure_yield
                else "action_elapsed_budget_exhausted"
            ),
            "prove_turn_budget": prove_turn_budget,
            "refine_turn_budget": refine_turn_budget,
            "nested_decomposition_allowed": nested_decomposition_allowed,
            "nested_decomposition_available": nested_decomposition_available,
            "nested_decomposition_suppressed_reason": (
                "child_sessions_are_proof_only"
                if nested_decomposition_available
                else ""
            ),
            "action_elapsed_budget_s": max(
                0.0,
                float(max_elapsed_s or 0.0),
            ),
            "action_deadline_epoch_s": float(
                action_deadline_epoch_s or 0.0
            ),
            "action_elapsed_budget_exhausted": True,
            "provider_calls_completed": child_provider_calls_completed,
            "provider_dispatches_started": (
                child_provider_dispatches_started
            ),
            "llm_failure_kind": child_llm_failure_kind,
            "llm_error": child_llm_error,
            "llm_retryable": bool(
                cleanup_infrastructure_outcome.get("llm_retryable")
                or child_llm_retryable
            ),
            "zero_provider_failure": bool(
                cleanup_infrastructure_outcome.get("zero_provider_failure")
            ),
            "retryable_infrastructure": bool(
                cleanup_infrastructure_outcome.get(
                    "retryable_infrastructure"
                )
            ),
            "retryable_infrastructure_reason": str(
                cleanup_infrastructure_outcome.get(
                    "retryable_infrastructure_reason"
                )
                or ""
            ),
            "shared_capabilities_revoked": bool(
                cleanup_infrastructure_outcome.get("shared_capabilities_revoked")
            ),
            "terminal_failure": False,
            "preserve_frontier_work": bool(cleanup_infrastructure_yield),
            "preserve_action_budget": bool(
                cleanup_infrastructure_outcome.get("preserve_action_budget")
            ),
            "iteration_neutral": bool(
                cleanup_infrastructure_outcome.get("iteration_neutral")
            ),
            "scheduler_neutral": bool(cleanup_infrastructure_yield),
            "stagnation_neutral": bool(cleanup_infrastructure_yield),
            "hard_pivot_neutral": bool(cleanup_infrastructure_yield),
            "verdict": (
                "recursive_helper_cleanup_infrastructure_yield"
                if cleanup_infrastructure_yield
                else "action_elapsed_budget_exhausted"
            ),
        }
        return False, None, telemetry

    refine_role_turns = 0
    try:
        role_counts = getattr(child_session, "_conversation_role_turn_counts", {}) or {}
        refine_role_turns = int(role_counts.get("refine", 0) or 0)
    except Exception:
        refine_role_turns = 0
    refine_budget_invocations = 0
    if refine_action is not None:
        try:
            refine_budget_invocations = int(
                getattr(
                    child_session.budgets.get(refine_action.id),
                    "invocations",
                    0,
                )
                or 0
            )
        except Exception:
            refine_budget_invocations = 0
    refine_ran = bool(refine_role_turns > 0 or refine_budget_invocations > 0)
    refine_attempted = bool(refine_ran or (refine_registered and not ok))
    refine_solved = bool(ok and proof_text and refine_ran)
    refine_skip_reason = ""
    refine_skipped = False
    if bool(refine_enabled) and parent_session.refiner_client is None:
        refine_skipped = True
        refine_skip_reason = "missing_refiner_client"
    elif bool(refine_enabled) and refine_turn_budget <= 0:
        refine_skipped = True
        refine_skip_reason = "turn_budget_exhausted"

    # --- Optional refine pass, explicitly after a failed prove pass ---
    if (
        not ok
        and bool(refine_enabled)
        and parent_session.refiner_client is not None
        and refine_turn_budget > 0
        and not refine_registered
    ):
        refine_attempted = True
        refine_action = ConversationTurnAction(
            **_conversation_turn_kwargs(
                role="refine",
                client=parent_session.refiner_client,
                parent_action=parent_refine_action,
                turn_budget=refine_turn_budget,
            )
        )
        child_session.register(refine_action)
        child_session.set_budget(
            refine_action.id,
            ActionBudget(
                max_invocations=refine_turn_budget,
                max_total_seconds=0.0,
            ),
        )
        child_session.max_iterations = max(
            int(getattr(child_session, "max_iterations", 0) or 0),
            int(getattr(child_session, "iteration", 0) or 0)
            + refine_turn_budget
            + 5,
        )
        child_session.expand_max_iterations_to_action_budgets(headroom=5)
        if callable(sanitize_orphan):
            try:
                sanitize_orphan()
            except Exception:
                pass
        ok, proof_text = await child_session.run()
        refine_solved = bool(ok and proof_text)
        if callable(sanitize_orphan):
            try:
                sanitize_orphan()
            except Exception:
                pass

    # A refine pass, when present, owns the final provider result for the
    # child. Refresh the producer accounting after all child model work.
    last_action_metadata = dict(
        getattr(child_session, "last_action_outcome_metadata", {}) or {}
    )
    child_provider_calls_completed, child_provider_dispatches_started = (
        _child_provider_exposure(child_session)
    )
    child_llm_failure_kind = str(
        last_action_metadata.get("llm_failure_kind") or ""
    ).strip()
    child_llm_error = str(last_action_metadata.get("llm_error") or "").strip()
    child_llm_retryable = bool(last_action_metadata.get("llm_retryable"))

    if publication_guard is not None:
        publication_guard()
    merge_child_theory_context(parent_session, child_session)

    parent_target_graph_id = str(
        getattr(parent_target_graph_node, "node_id", "") or ""
    ).strip()
    if publication_guard is not None:
        publication_guard()
    merge_relevant_child_proof_ideas(
        parent_dossier,
        child_dossier,
        proof_idea_ids=child_proof_idea_ids,
        source_to_target_node_id=(
            {str(child_dossier.proof_graph.root_node_id): parent_target_graph_id}
            if parent_target_graph_id
            else {}
        ),
        branch_source="recursive-helper-child",
        branch_key=child_proof_idea_branch_id,
    )

    # --- Extract the most-recent give-up cluster from the child ---
    # The child's ConversationTurnAction sets giveup_cluster on every
    # outcome metadata (when the gate fires). The most recent
    # outcome's metadata is the source of truth for "did the child
    # give up at depth N+1". We surface it here so the parent action
    # can persist it on the open child_goal node.
    child_giveup_cluster: Optional[str] = None
    child_giveup_match: str = ""
    # Scan the child session's most-recent action outcomes by polling
    # the recorder is too brittle; instead the ConversationTurnAction
    # posts giveup_cluster on session.last_post_failure_result when the
    # ConversationTurnAction inline cascade fires, and on its own outcome
    # metadata. We use a simple approach: the child's last cascade-result
    # holds the answer.
    last_pf = getattr(child_session, "last_post_failure_result", None)
    if last_pf is not None:
        cluster = getattr(last_pf, "giveup_cluster", None)
        if cluster:
            child_giveup_cluster = str(cluster)
            child_giveup_match = str(getattr(last_pf, "giveup_match", "") or "")
    if not child_giveup_cluster:
        cluster = getattr(child_session, "last_giveup_cluster", None)
        if cluster:
            child_giveup_cluster = str(cluster)
            child_giveup_match = str(
                getattr(child_session, "last_giveup_match", "") or ""
            )

    # --- Merge child verified helpers back into parent ---
    # HIGH fix (2026-05-09): route merge through record_verified_helper
    # so the answer-unsafe filter applies and proof_graph stays
    # consistent. Direct dict assignment (the prior approach) bypassed
    # both. Skip the proposed_name ``helper_name`` so the parent's
    # subsequent recheck path can see it as "not yet in dossier" and
    # adjudicate fresh (the action's CRITICAL ordering depends on
    # this).
    if publication_guard is not None:
        publication_guard()
    merge_eligible_child_verified_helpers()
    # Child helper sessions are proof-only. Proposed helpers produced by a
    # failed child are the exact "shift the bridge elsewhere" shape this path
    # is meant to avoid, so they are intentionally not propagated upward.

    # --- Durable falsification of a proven-FALSE child goal --------------------
    # When the child prove pass FAILS but its transcript contains an ACCEPTED
    # try_lean proof of ¬target_statement, promote that checked evidence into an
    # axiom-audited negation certificate and durably mark the proof-state node
    # falsified so the scheduler stops re-probing it. Soundness boundary and
    # rationale live in child_goal_falsification.py.
    child_goal_falsified = False
    falsification_certificate_hash = ""
    if not ok:
        from .child_goal_falsification import (
            maybe_falsify_child_goal_from_child_transcript,
        )

        child_goal_falsified, falsification_certificate_hash = (
            await maybe_falsify_child_goal_from_child_transcript(
                parent_session=parent_session,
                dossier=parent_dossier,
                node_id=str(nested_node_id or ""),
                target_statement=target_statement,
                child_conv=child_conv,
                preamble=(
                    parent_session.acceptance_preamble()
                    if hasattr(parent_session, "acceptance_preamble")
                    else parent_preamble
                ),
                publication_guard=publication_guard,
            )
        )

    child_verified_helper_names = {
        str(name or "").strip()
        for name in list(getattr(child_dossier, "verified_helpers", {}) or {})
        if str(name or "").strip()
    }
    seeded_child_helper_names = {
        str(name or "").strip()
        for name in (*child_seeded_helpers, *child_seeded_proposed_helpers)
        if str(name or "").strip()
    }
    zero_provider_failure = bool(
        not ok
        and child_llm_retryable
        and child_provider_calls_completed == 0
        and child_provider_dispatches_started == 0
        and bool(child_llm_error or child_llm_failure_kind)
        and not (child_verified_helper_names - seeded_child_helper_names)
        and not child_goal_falsified
    )

    telemetry: Dict[str, Any] = {
        "conv_turn_count": int(getattr(child_session, "_conversation_turn_count", 0) or 0),
        "iteration": int(getattr(child_session, "iteration", 0) or 0),
        "stagnation_counter": int(getattr(child_session, "stagnation_counter", 0) or 0),
        "recursion_depth": new_depth,
        "max_recursion_depth": max_recursion_depth,
        "child_seeded_helpers": child_seeded_helpers,
        "child_seeded_proposed_helpers": child_seeded_proposed_helpers,
        "child_skipped_solution_helpers": child_skipped_solution_helpers,
        "child_skipped_target_dependent_helpers": (
            child_skipped_target_dependent_helpers
        ),
        "child_helpers_added": list(child_dossier.verified_helpers.keys())
        if child_dossier is not None
        else [],
        "giveup_cluster": child_giveup_cluster,
        "giveup_match": child_giveup_match,
        "child_goal_falsified": child_goal_falsified,
        "falsification_certificate_hash": falsification_certificate_hash,
        "refine_attempted": refine_attempted,
        "refine_solved": refine_solved,
        "refine_skipped": refine_skipped,
        "refine_skip_reason": refine_skip_reason,
        "prove_turn_budget": prove_turn_budget,
        "refine_turn_budget": refine_turn_budget,
        "nested_decomposition_allowed": nested_decomposition_allowed,
        "nested_decomposition_available": nested_decomposition_available,
        "nested_decomposition_suppressed_reason": (
            "child_sessions_are_proof_only"
            if nested_decomposition_available
            else ""
        ),
        "action_elapsed_budget_s": max(0.0, float(max_elapsed_s or 0.0)),
        "action_deadline_epoch_s": float(action_deadline_epoch_s or 0.0),
        "action_elapsed_budget_exhausted": False,
        "provider_calls_completed": child_provider_calls_completed,
        "provider_dispatches_started": child_provider_dispatches_started,
        "llm_failure_kind": child_llm_failure_kind,
        "llm_error": child_llm_error,
        "llm_retryable": child_llm_retryable,
        "zero_provider_failure": zero_provider_failure,
        "verdict": "ran",
    }
    return ok, proof_text, telemetry
