"""Lean/tactic executor workers for proof-state search."""

from __future__ import annotations

import asyncio
import copy
import inspect
import json
import math
import re
import time
import weakref
from dataclasses import dataclass, replace
from types import SimpleNamespace
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .helper_salvage import (
    HelperSalvager,
    _fresh_helper_collision_name,
    _helper_relevance_probe_proof,
    _rename_helper_identifier,
    _helper_referenced_names,
    collect_open_child_targets,
    lean_invalid_helpers_after_replacement,
    lean_valid_helper_context_excluding_name,
    merge_context_helpers,
    order_helpers_for_incremental_validation,
    refresh_revalidated_dependent_support_hashes,
)
from .deadline_guard import (
    await_with_strict_deadline,
    create_result_only_deadline_task,
    outer_guard_timeout_s,
)
from .lean_parser import canonical_error_type, fallback_error_type_from_text
from .lean_runner import (
    LEAN_RESIDUAL_VERIFIER_GENERATION,
    LeanRunner,
    lean_residual_elaboration_context_hash,
)
from .theorem_project import (
    decode_theorem_target_context,
    has_theorem_target_context,
)
from .mini_tactic_closer import (
    TacticCandidate,
    TacticPatternCache,
    is_transient_tactic_close_failure,
    try_close_with_tactics,
)
from .mini_falsification import (
    FalsificationOutcome,
    FalsificationPolicy,
    FalsificationService,
    TargetKind,
)
from .mini_falsification.generators import binder_domain, leading_forall_binders
from .mini_root_tactic import (
    root_tactic_success_contract_status,
    try_close_root_with_active_lift,
)
from .mini_deadline_transaction import DeadlineMutationTransaction
from .proof_dossier import (
    ProofDossier,
    _decl_application_error_is_lean_diagnostic,
    active_root_target_statement,
    dossier_root_equivalence_placeholder,
    helper_decl_name,
    is_answer_unsafe_statement_text,
    text_hash,
)
from .proof_graph import helper_decl_body, helper_decl_statement
import hashlib

from .proof_state import (
    PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION,
    ProofSearchState,
    ProofStateNode,
    _LEAN_LOCAL_IDENT_RE,
    _residual_goal_attestation_authorities,
    canonicalize_lean_statement_for_identity,
    lean_statement_bound_names,
    proof_state_source_requires_residual_goal_attestation,
    proof_state_decl_application_candidate_names,
    proof_state_decl_application_pending_names,
    proof_state_begin_decl_application_batch,
    validated_root_tactic_portfolio_continuation,
)
from .proof_state_cache import (
    MiniVerifiedLemmaCache,
    _proof_state_helper_policy_rejection,
    stage_verified_helper_for_dossier,
    store_verified_helper_for_dossier,
)
from .tactic_attempt_telemetry import (
    LeanAttemptObserver,
    dossier_lean_attempt_observer,
    notify_lean_attempt_observer,
    record_dossier_lean_attempt_event,
    tactic_attempt_telemetry_fields,
)


_VERIFIED_HELPER_ACCEPT_SESSIONS: dict[int, weakref.ReferenceType[Any]] = {}


def register_verified_helper_accept_session(dossier: Any, session: Any) -> None:
    """Associate a live session capability without mutating the dossier."""

    dossier_id = id(dossier)

    def discard(reference: Any) -> None:
        if _VERIFIED_HELPER_ACCEPT_SESSIONS.get(dossier_id) is reference:
            _VERIFIED_HELPER_ACCEPT_SESSIONS.pop(dossier_id, None)

    _VERIFIED_HELPER_ACCEPT_SESSIONS[dossier_id] = weakref.ref(session, discard)


def unregister_verified_helper_accept_session(dossier: Any) -> None:
    _VERIFIED_HELPER_ACCEPT_SESSIONS.pop(id(dossier), None)


def _registered_verified_helper_accept_callback(dossier: Any) -> Any:
    reference = _VERIFIED_HELPER_ACCEPT_SESSIONS.get(id(dossier))
    session = reference() if reference is not None else None
    return getattr(session, "theory_verified_helper_accept_callback", None)


def _registered_verified_helper_reconcile_callback(dossier: Any) -> Any:
    reference = _VERIFIED_HELPER_ACCEPT_SESSIONS.get(id(dossier))
    session = reference() if reference is not None else None
    return getattr(session, "theory_verified_helper_reconcile_callback", None)


def _fully_funded_operation_timeout(
    timeout_s: float,
    deadline_monotonic: float = 0.0,
) -> float:
    """Return the full per-operation timeout or defer without launching.

    An enclosing hard deadline is an admission boundary, not permission to
    turn a configured 120-second Lean operation into a 7-second experiment.
    Underfunded work remains on the frontier for a later action quantum.
    """

    try:
        current = asyncio.current_task()
    except RuntimeError:
        current = None
    if current is not None and current.cancelling() > 0:
        return 0.0
    requested = max(0.0, float(timeout_s or 0.0))
    if requested <= 0.0:
        return 0.0
    deadline = float(deadline_monotonic or 0.0)
    if deadline <= 0.0:
        return requested
    remaining = deadline - time.monotonic()
    return requested if remaining >= requested else 0.0


def _durable_nonnegative_int(value: Any) -> int:
    """Decode an advisory durable counter without trusting checkpoint shape."""

    if isinstance(value, bool):
        return 0
    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError):
        return 0


class _LeanOperationDeadline(asyncio.TimeoutError):
    """The executor guard expired, distinct from adapter-raised TimeoutError."""


class _LeanAdmissionDeferred(_LeanOperationDeadline):
    """Lock admission expired before this operation launched any Lean work."""


_LEAN_LOCK_ADMISSION_TIMEOUT_S = 1.0


class _SerializedFalsificationLeanProxy:
    """Serialize each actual falsification Lean call, including late tails."""

    _OPERATION_NAMES = frozenset(
        {
            "check",
            "audit_proof_axioms",
            "analyze_statement_contracts",
            "_execute_content",
        }
    )

    def __init__(
        self,
        lean: Any,
        *,
        timeout_s: float,
        deadline_monotonic: float,
    ) -> None:
        self._lean = lean
        self._timeout_s = max(0.0, float(timeout_s or 0.0))
        self._deadline_monotonic = max(
            0.0,
            float(deadline_monotonic or 0.0),
        )

    def __getattr__(self, name: str) -> Any:
        attribute = getattr(self._lean, name)
        if name not in self._OPERATION_NAMES or not callable(attribute):
            return attribute

        async def serialized_operation(*args: Any, **kwargs: Any) -> Any:
            try:
                requested_timeout = max(
                    0.0,
                    float(kwargs.get("timeout_s") or self._timeout_s),
                )
            except (TypeError, ValueError):
                requested_timeout = self._timeout_s

            async def invoke() -> Any:
                result = attribute(*args, **kwargs)
                if inspect.isawaitable(result):
                    return await result
                return result

            return await _await_serialized_lean_operation(
                self._lean,
                invoke,
                timeout_s=requested_timeout,
                deadline_monotonic=self._deadline_monotonic,
                operation_label=f"proof_state_child_falsification:{name}",
            )

        return serialized_operation


async def _await_serialized_lean_operation(
    lean: Any,
    operation: Callable[[], Any],
    *,
    timeout_s: Optional[float] = None,
    deadline_monotonic: float = 0.0,
    operation_label: str = "proof_state_lean_operation",
    deadline_elapsed: Optional[Callable[[], bool]] = None,
    release_unrecyclable_tail: bool = False,
) -> Any:
    """Strictly bound one Lean operation and retain its tail lease.

    The operation is created only after the per-adapter lock is acquired. If
    an adapter suppresses cancellation, the controller returns at its strict
    deadline while the detached task retains the lock until the adapter really
    settles. This prevents both wall-budget renewal and overlapping access to a
    stateful Lean process. Prove-turn tools pass ``release_unrecyclable_tail``
    so a discarded zombie cannot park a submitted proof. Intra-search callers
    leave it false and defer instead of overlapping a still-running adapter.
    Detach always publishes that tail so the next waiter can recycle.
    """

    from .mini_formal_state_search import (
        _mark_lean_late_tail,
        _once_only_lock_release,
        acquire_prepared_lean_lock,
        bind_owned_lean_lock,
        currently_owns_lean_lock,
        reset_owned_lean_lock,
    )
    from .runtime_context import mark_runtime_owned_callback

    unbounded = timeout_s is None
    if currently_owns_lean_lock(lean):
        if deadline_elapsed is not None and deadline_elapsed():
            raise _LeanOperationDeadline
        if not unbounded:
            nested_timeout = _fully_funded_operation_timeout(
                float(timeout_s or 0.0),
                deadline_monotonic,
            )
            if nested_timeout <= 0.0:
                raise _LeanOperationDeadline
        return await operation()

    requested = None if unbounded else _fully_funded_operation_timeout(
        timeout_s,
        deadline_monotonic,
    )
    if not unbounded and requested <= 0.0:
        raise _LeanOperationDeadline
    if unbounded:
        admission_s: Optional[float] = None
        admitted: Optional[float] = None
    else:
        admission_s = min(
            float(requested or 0.0),
            max(0.0, float(_LEAN_LOCK_ADMISSION_TIMEOUT_S)),
        )
        if admission_s <= 0.0:
            raise _LeanAdmissionDeferred
        admitted = float(requested or 0.0)

    try:
        live, lock = await acquire_prepared_lean_lock(
            lean,
            admission_timeout_s=admission_s,
            deadline_elapsed=deadline_elapsed,
            deadline_monotonic=deadline_monotonic,
            release_unrecyclable_tail=release_unrecyclable_tail,
        )
    except asyncio.TimeoutError as exc:
        raise _LeanAdmissionDeferred from exc
    del live

    release_owned_lock = _once_only_lock_release(lock)
    try:
        if deadline_elapsed is not None and deadline_elapsed():
            raise _LeanOperationDeadline
        if not unbounded:
            admitted = _fully_funded_operation_timeout(
                float(timeout_s or 0.0),
                deadline_monotonic,
            )
            if admitted <= 0.0:
                raise _LeanOperationDeadline
    except BaseException:
        release_owned_lock()
        raise

    async def run_with_owned_lock() -> Any:
        token = bind_owned_lean_lock(lock)
        try:
            try:
                return True, await operation()
            except asyncio.CancelledError as exc:
                # Keep adapter cancellation distinct from the operation
                # watchdog. ``await_with_strict_deadline`` otherwise turns a
                # completed CancelledError into TimeoutError.
                return False, exc
            except Exception as exc:
                # Preserve adapter exceptions as operation outcomes. In
                # particular, an adapter-raised TimeoutError is transient
                # evidence, not proof that this strict guard expired.
                return False, exc
        finally:
            reset_owned_lean_lock(token)
            release_owned_lock()

    operation_task = create_result_only_deadline_task(run_with_owned_lock())
    operation_task.add_done_callback(
        mark_runtime_owned_callback(release_owned_lock)
    )
    try:
        completed, value = await await_with_strict_deadline(
            operation_task,
            # Admission above reserved the complete operation capability.
            # Reapplying the enclosing deadline here would shave lock and
            # scheduler latency off that capability and recreate the 7-second
            # remainder bug at a lower layer.
            #
            # Headroom on top: the operation was handed this same budget as
            # its own ``timeout_s``, and only its copy reclaims -- it kills
            # and reaps the Lean child. This guard can merely cancel and
            # detach (``result_only`` joins for 0.005s, far short of a reap),
            # so arming it with the identical number made a guard win discard
            # a landing verdict and leave the child alive holding the lock.
            # Funding and admission above are deliberately left untouched, so
            # nothing defers that would previously have run.
            timeout_s=outer_guard_timeout_s(admitted),
            deadline_monotonic=0.0,
            operation_label=operation_label,
            operation_ownership="result_only",
        )
    except asyncio.TimeoutError as exc:
        if not operation_task.done():
            _mark_lean_late_tail(
                lock,
                operation_task,
                operation_label=operation_label,
                release_lock=release_owned_lock,
            )
        raise _LeanOperationDeadline from exc
    except asyncio.CancelledError:
        if not operation_task.done():
            _mark_lean_late_tail(
                lock,
                operation_task,
                operation_label=operation_label,
                release_lock=release_owned_lock,
            )
        raise
    if not completed:
        if isinstance(value, asyncio.CancelledError):
            raise asyncio.CancelledError() from value
        raise value
    return value


def _record_completed_tactic_observer_events(
    dossier: ProofDossier,
    lane: str,
    result: Any,
) -> None:
    """Publish observer telemetry only after a tactic operation completed on time."""

    observer = dossier_lean_attempt_observer(dossier, lane)
    attempts = [
        dict(attempt)
        for attempt in list(getattr(result, "attempts", ()) or ())
        if isinstance(attempt, Mapping)
    ]
    notify_lean_attempt_observer(
        observer,
        "portfolio",
        {"candidate_count": int(getattr(result, "candidate_count", 0) or 0)},
    )
    for attempt in attempts:
        notify_lean_attempt_observer(observer, "started", attempt)
        notify_lean_attempt_observer(observer, "finished", attempt)


def _formal_state_root_bottlenecks(
    proof_state: ProofSearchState,
    node: ProofStateNode,
    raw_bottlenecks: Sequence[Mapping[str, Any]],
    helper_blocks: Sequence[str],
) -> List[Dict[str, Any]]:
    """Attach proof-DAG root impact and helper-route attribution to Lean states."""

    parent_groups = getattr(proof_state, "parent_groups_for_child", None)

    def parents_for(node_id: str) -> List[Tuple[str, str]]:
        if callable(parent_groups):
            try:
                return [
                    (str(parent_id or ""), str(assembly_id or ""))
                    for parent_id, assembly_id in parent_groups(node_id)
                    if str(parent_id or "").strip()
                ]
            except Exception:
                pass
        current = proof_state.nodes.get(node_id)
        legacy_parent = str(
            getattr(current, "parent_node_id", "") if current is not None else ""
        ).strip()
        return [(legacy_parent, "")] if legacy_parent else []

    group_tryable = getattr(proof_state, "_group_tryable_for_attempt", None)
    viability_cache: Dict[Tuple[str, Tuple[str, ...]], bool] = {}

    def declared_children(group: Any) -> List[str]:
        return list(
            dict.fromkeys(
                str(child_id or "").strip()
                for child_id in list(getattr(group, "child_node_ids", ()) or ())
                if str(child_id or "").strip()
            )
        )

    def group_is_viable(
        group: Any,
        *,
        focus_node_id: str = "",
        visiting: Set[str],
    ) -> bool:
        try:
            if callable(group_tryable) and not group_tryable(group):
                return False
        except Exception:
            return False
        child_ids = declared_children(group)
        if not child_ids or any(child_id not in proof_state.nodes for child_id in child_ids):
            return False
        if focus_node_id and focus_node_id not in child_ids:
            return False
        return all(
            child_id == focus_node_id or node_has_viable_closure(child_id, visiting)
            for child_id in child_ids
        )

    def node_has_viable_closure(node_id: str, visiting: Set[str]) -> bool:
        """Cycle-safe OR-over-groups / AND-over-children closure viability."""

        cache_key = (node_id, tuple(sorted(visiting)))
        if cache_key in viability_cache:
            return viability_cache[cache_key]
        if node_id in visiting:
            return False
        candidate = proof_state.nodes.get(node_id)
        if candidate is None:
            return False
        status = str(getattr(candidate, "status", "") or "")
        if status == "proved":
            viability_cache[cache_key] = True
            return True
        if status in {"rejected", "failed", "obsolete"}:
            viability_cache[cache_key] = False
            return False
        if status not in {"open", "blocked"}:
            viability_cache[cache_key] = False
            return False
        groups = list(getattr(candidate, "assembly_attempt_groups", ()) or ())
        if not groups:
            # An open/blocked leaf remains a mathematical work item even when
            # it has not yet been decomposed into an assembly route.
            viability_cache[cache_key] = True
            return True
        next_visiting = {*visiting, node_id}
        viable = any(
            group_is_viable(group, visiting=next_visiting) for group in groups
        )
        viability_cache[cache_key] = viable
        return viable

    def viable_parents_for(node_id: str) -> List[Tuple[str, str]]:
        """Return only assembly edges that can still carry proof to a parent."""

        viable: List[Tuple[str, str]] = []
        for parent_id, assembly_id in parents_for(node_id):
            parent = proof_state.nodes.get(parent_id)
            if parent is None or str(getattr(parent, "status", "")) != "open":
                continue
            # A legacy parent pointer has no assembly contract to falsify.
            if not assembly_id:
                viable.append((parent_id, assembly_id))
                continue
            group = next(
                (
                    candidate
                    for candidate in list(
                        getattr(parent, "assembly_attempt_groups", ()) or ()
                    )
                    if str(getattr(candidate, "assembly_id", "") or "")
                    == assembly_id
                ),
                None,
            )
            if group is None:
                continue
            if not group_is_viable(
                group,
                focus_node_id=node_id,
                visiting={parent_id},
            ):
                continue
            viable.append((parent_id, assembly_id))
        return viable

    first_parents = parents_for(node.node_id)
    root_id = str(getattr(proof_state, "root_node_id", "") or "")
    root_distance: Optional[int] = None
    frontier = [(node.node_id, 0)]
    seen: Set[str] = set()
    while frontier:
        current_id, distance = frontier.pop(0)
        if current_id in seen:
            continue
        seen.add(current_id)
        if current_id == root_id:
            root_distance = distance
            break
        for parent_id, _assembly_id in viable_parents_for(current_id):
            if parent_id and parent_id not in seen:
                frontier.append((parent_id, distance + 1))

    helper_names = [
        helper_decl_name(block)
        for block in helper_blocks
        if helper_decl_name(block)
    ]
    records: List[Dict[str, Any]] = []
    for raw in raw_bottlenecks:
        record = dict(raw)
        tactic_text = "\n".join(
            str(item or "") for item in list(record.get("tactics") or ())
        )
        referenced_helpers = [
            name
            for name in helper_names
            if re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'.])", tactic_text)
        ]
        record.update(
            {
                "proof_state_node_id": node.node_id,
                "root_unlocking_candidate": bool(
                    root_distance is not None and record.get("actionable", False)
                ),
                "root_distance": root_distance,
                "parent_node_ids": tuple(
                    dict.fromkeys(parent_id for parent_id, _ in first_parents)
                ),
                "blocking_assembly_ids": tuple(
                    dict.fromkeys(
                        assembly_id
                        for _parent_id, assembly_id in first_parents
                        if assembly_id
                    )
                ),
                "referenced_verified_helpers": tuple(referenced_helpers),
            }
        )
        records.append(record)
    return records


def _proof_state_verified_helper_blocks(
    dossier: Optional[ProofDossier],
    *,
    refresh_quality: bool = True,
) -> List[str]:
    if dossier is None:
        return []
    helpers = list(
        dossier.verified_helper_blocks(refresh_quality=refresh_quality)
    )
    forced_context_helpers = [
        str(block or "").strip()
        for block in list(getattr(dossier, "forced_context_helper_blocks", ()) or ())
        if str(block or "").strip()
    ]
    if forced_context_helpers:
        return ProofDossier._merge_replay_helper_blocks(
            helpers,
            forced_context_helpers,
        )
    return helpers


def _proof_state_active_root_targets_for_frame(dossier: ProofDossier) -> Tuple[Mapping[str, Any], ...]:
    current_frame = getattr(dossier, "active_root_targets_for_current_frame", None)
    if callable(current_frame):
        try:
            return tuple(
                dict(item)
                for item in list(current_frame() or ())
                if isinstance(item, Mapping)
            )
        except Exception:
            return ()
    return ()


def _proof_state_helper_relevance_targets(
    dossier: ProofDossier,
    proof_state: Optional[ProofSearchState],
    *,
    target_statement: str = "",
) -> Tuple[str, ...]:
    """Return the root/open-node targets used by proof-state helper relevance."""

    targets: List[str] = []
    root = str(getattr(dossier, "root_statement", "") or "").strip()
    if root:
        targets.append(root)
    active_root = str(active_root_target_statement(dossier) or "").strip()
    if active_root:
        targets.append(active_root)
    direct_target = str(target_statement or "").strip()
    if direct_target:
        targets.append(direct_target)
    targets.extend(collect_open_child_targets(proof_state))
    out: List[str] = []
    seen: Set[str] = set()
    for target in targets:
        clean = str(target or "").strip()
        if clean and clean not in seen:
            seen.add(clean)
            out.append(clean)
    return tuple(out)


async def _proof_state_helper_passes_relevance_gate(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    proof_state: Optional[ProofSearchState],
    helper_block: str,
    check_lemmas: List[str],
    timeout_s: float,
    target_statement: str = "",
) -> Tuple[bool, str]:
    """Mirror helper-salvage's root/open-target relevance gate for proof-state helpers."""

    root = str(getattr(dossier, "root_statement", "") or "").strip()
    if not root or dossier_root_equivalence_placeholder(root):
        return True, ""
    targets = _proof_state_helper_relevance_targets(
        dossier,
        proof_state,
        target_statement=target_statement,
    )
    if not targets:
        return True, ""
    name = helper_decl_name(helper_block) or ""
    if not name:
        return False, "missing_helper_name"
    salvager = HelperSalvager(
        lean,
        preamble=_proof_state_check_preamble(conv),
        timeout_s=timeout_s,
        relevance_gate_root_statement=root,
        relevance_gate_open_targets=targets[1:],
    )
    probe = _helper_relevance_probe_proof(name)
    probe_passed = False
    probe_inconclusive = False
    for target in targets:
        probe_result = await salvager._run_relevance_probe(
            target,
            probe,
            check_lemmas,
        )
        if probe_result is True:
            probe_passed = True
            break
        if probe_result is None:
            probe_inconclusive = True
    if probe_passed:
        return True, ""
    if probe_inconclusive:
        return False, "relevance_probe_inconclusive"
    return False, "off_topic"


def _trace(prefix: str, msg: str) -> None:
    print(f"{prefix}{msg}", flush=True)


def _proof_state_tactic_pattern_cache(
    proof_state: ProofSearchState,
) -> TacticPatternCache:
    cache = getattr(proof_state, "_tactic_pattern_cache", None)
    if not isinstance(cache, TacticPatternCache):
        cache = TacticPatternCache()
        setattr(proof_state, "_tactic_pattern_cache", cache)
    return cache


def _proof_state_tactic_pattern_context(
    proof_state: ProofSearchState,
    node: ProofStateNode,
    *,
    scope: str,
    mode: str = "",
) -> Dict[str, str]:
    goal = getattr(node, "goal", None)
    if goal is not None:
        shape_key = "|".join(
            [
                f"result={getattr(goal, 'result_head', '') or ''}",
                "tags=" + ",".join(list(getattr(goal, "shape_tags", []) or [])[:12]),
                "binders="
                + ",".join(list(getattr(goal, "binder_structure", []) or [])[:8]),
                "typeclasses="
                + ",".join(list(getattr(goal, "typeclass_needs", []) or [])[:8]),
            ]
        )
        shape_context = "consts=" + ",".join(
            list(getattr(goal, "constants_used", []) or [])[:16]
        )
    else:
        shape_key = canonicalize_lean_statement_for_identity(
            str(getattr(node, "target", "") or "")
        )
        shape_context = ""
    return {
        "scope": str(scope or "").strip(),
        "mode": str(mode or "").strip(),
        "node_kind": str(getattr(node, "kind", "") or ""),
        "shape_key": shape_key,
        "shape_context": shape_context,
        "local_context_hash": text_hash(
            "\n".join(str(item or "") for item in getattr(node, "local_context", []) or [])
        ),
        "parent_stub_hash": text_hash(str(getattr(node, "parent_proof_stub", "") or "")),
    }


def _merge_tactic_cache_metadata(
    base: Optional[Dict[str, Any]],
    update: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    out = dict(base or {})
    for key, value in dict(update or {}).items():
        if isinstance(value, bool):
            out[key] = value
            continue
        if isinstance(value, int):
            out[key] = int(out.get(key, 0) or 0) + value
            continue
        out[key] = value
    return out


def _needs_answer_safe_feedback_check(conv: Any) -> bool:
    if not bool(getattr(conv, "suppress_solution_placeholders", True)):
        return False
    prompt_preamble = (getattr(conv, "preamble", "") or "").strip()
    lean_preamble = (getattr(conv, "lean_preamble", "") or "").strip()
    lean_base = decode_theorem_target_context(lean_preamble)[0].strip()
    return bool(prompt_preamble and lean_base and prompt_preamble != lean_base)


def _root_assembly_contract_status(
    dossier: Any,
    *,
    target_statement: str = "",
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {
            "ready": False,
            "verdict": "missing_proof_graph",
        }
    status_getter = getattr(graph, "ready_root_assembly_contract_status", None)
    if not callable(status_getter):
        return {
            "ready": False,
            "verdict": "root_assembly_contract_status_api_missing",
        }
    try:
        status = dict(
            status_getter(
                target_statement=str(
                    target_statement
                    or getattr(dossier, "root_statement", "")
                    or ""
                ),
            )
            or {}
        )
    except Exception as exc:
        status = {
            "ready": False,
            "verdict": "root_assembly_contract_status_exception",
            "exception_type": type(exc).__name__,
        }
    if not bool(status.get("ready")):
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            try:
                increment("mini_root_assembly_contract_blocked", 1)
            except Exception:
                pass
    return status


def _declaration_body_assign(tail: str, *, start: int) -> Optional[int]:
    depth = 0
    in_top_level_let = False
    s = str(tail or "")
    index = max(0, int(start or 0))
    while index < len(s) - 1:
        ch = s[index]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and s.startswith("let", index):
            before = s[index - 1] if index > 0 else " "
            after_i = index + 3
            after = s[after_i] if after_i < len(s) else " "
            if not (before.isalnum() or before == "_") and not (
                after.isalnum() or after == "_"
            ):
                in_top_level_let = True
                index += 3
                continue
        elif depth == 0 and in_top_level_let and ch == ";":
            in_top_level_let = False
        elif depth == 0 and in_top_level_let and ch in "\n\r":
            in_top_level_let = False
        elif ch == ":" and s[index + 1] == "=" and depth == 0:
            if in_top_level_let:
                index += 2
                continue
            return index
        index += 1
    return None


def _find_top_level_assign(src: str) -> int:
    text = str(src or "")
    marker = _declaration_body_assign(text, start=0)
    return -1 if marker is None else marker + 2


def _axiomatize_helper_for_feedback(block: str) -> str:
    text = str(block or "").strip()
    sep_end = _find_top_level_assign(text)
    if sep_end >= 2:
        head = text[: sep_end - 2].strip()
    else:
        head = text.split(":=", 1)[0].strip()
    if not head:
        return text
    axiom = re.sub(
        r"^\s*"
        r"(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|axiom)\s+",
        "axiom ",
        head,
        count=1,
    )
    return axiom if axiom != head else text


def _feedback_lemmas_for_answer_safe_recheck(
    lemmas: Sequence[str],
    conv: Any,
) -> List[str]:
    if (
        not _needs_answer_safe_feedback_check(conv)
        or getattr(conv, "official_answer_payload_present", None) is False
    ):
        return [str(item or "") for item in (lemmas or ())]
    return [_axiomatize_helper_for_feedback(str(item or "")) for item in (lemmas or ())]


def _helper_names_from_blocks(blocks: Sequence[str]) -> List[str]:
    names: List[str] = []
    seen: set[str] = set()
    for block in blocks:
        name = helper_decl_name(str(block or ""))
        if name and name not in seen:
            seen.add(name)
            names.append(name)
    return names


def _helper_blocks_for_names(
    blocks: Sequence[str],
    names: Sequence[str],
) -> List[str]:
    wanted = {
        str(name or "").strip()
        for name in list(names or [])
        if str(name or "").strip()
    }
    if not wanted:
        return [str(block or "") for block in list(blocks or ())]
    return [
        str(block or "")
        for block in list(blocks or ())
        if (helper_decl_name(str(block or "")) or "") in wanted
    ]


def _root_replay_blocks_for_helper_names(
    *,
    dossier: ProofDossier,
    helper_context: Sequence[str],
    helper_names: Sequence[str],
) -> List[str]:
    clean_names = [
        str(name or "").strip()
        for name in list(helper_names or ())
        if str(name or "").strip()
    ]
    selected_blocks = _helper_blocks_for_names(helper_context, clean_names)
    replay_closure = getattr(dossier, "root_replay_helper_closure", None)
    if callable(replay_closure):
        closed = replay_closure(
            replay_helpers=selected_blocks,
            support_helper_names=clean_names,
        )
        if closed:
            return list(closed)
    return selected_blocks


def _root_tactic_context_key(
    *,
    goal_statement: str,
    preamble: str,
    helpers: Sequence[str],
    timeout_s: float,
    max_candidates: int,
    active_root_targets: Sequence[Mapping[str, Any]] = (),
) -> str:
    canonical_goal = (
        canonicalize_lean_statement_for_identity(goal_statement)
        or str(goal_statement or "").strip()
    )
    helper_payload = sorted(
        [
            {
                "name": helper_decl_name(str(block or "")) or "",
                "source_hash": text_hash(str(block or "")),
            }
            for block in helpers
            if str(block or "").strip()
        ],
        key=lambda item: (item["name"], item["source_hash"]),
    )
    active_target_payload = []
    for item in list(active_root_targets or ()):
        if not isinstance(item, Mapping):
            continue
        target = str(
            item.get("working_target") or item.get("target") or ""
        ).strip()
        if not target:
            continue
        hypotheses = [
            str(hyp or "").strip()
            for hyp in list(item.get("hypotheses") or ())
            if str(hyp or "").strip()
        ]
        # A transient root-exact route can register the unchanged root as an
        # active target and then retire it after rejection.  With no local
        # hypotheses that target contributes no new tactic evidence, so it
        # must not manufacture a fresh context key after route cleanup.
        target_key = canonicalize_lean_statement_for_identity(target) or target
        if not hypotheses and target_key == canonical_goal:
            continue
        active_target_payload.append(
            {"target": target_key, "hypotheses": hypotheses}
        )
    payload = {
        "goal": canonical_goal,
        "preamble_hash": text_hash(str(preamble or "")),
        "helpers": helper_payload,
        "active_root_targets": active_target_payload,
        "timeout_s": round(max(0.0, float(timeout_s or 0.0)), 3),
        "max_candidates": max(0, int(max_candidates or 0)),
    }
    return text_hash(json.dumps(payload, sort_keys=True, default=str))


def _root_tactic_attempted_context_keys(proof_state: ProofSearchState) -> Set[str]:
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return set()
    return {
        str(item or "").strip()
        for item in list(getattr(root, "root_tactic_attempted_context_keys", []) or ())
        if str(item or "").strip()
    }


def _root_tactic_deferred_context_keys(proof_state: ProofSearchState) -> Set[str]:
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return set()
    return {
        str(item or "").strip()
        for item in list(getattr(root, "root_tactic_deferred_context_keys", []) or ())
        if str(item or "").strip()
    }


def _root_tactic_continued_context_keys(proof_state: ProofSearchState) -> Set[str]:
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return set()
    return {
        str(item or "").strip()
        for item in list(getattr(root, "root_tactic_continued_context_keys", []) or ())
        if str(item or "").strip()
    }


def _mark_root_tactic_context_attempted(
    proof_state: ProofSearchState,
    context_key: str,
) -> None:
    key = str(context_key or "").strip()
    if not key:
        return
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return
    if key not in root.root_tactic_attempted_context_keys:
        root.root_tactic_attempted_context_keys.append(key)
        del root.root_tactic_attempted_context_keys[:-4096]
    try:
        proof_state.root_tactic_context_attempts += 1
    except Exception:
        pass


def _mark_root_tactic_context_continued(
    proof_state: ProofSearchState,
    context_key: str,
) -> None:
    key = str(context_key or "").strip()
    if not key:
        return
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return
    if key not in root.root_tactic_continued_context_keys:
        root.root_tactic_continued_context_keys.append(key)
        del root.root_tactic_continued_context_keys[:-4096]


def _mark_root_tactic_context_deferred(
    proof_state: ProofSearchState,
    context_key: str,
) -> None:
    key = str(context_key or "").strip()
    if not key:
        return
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return
    if key not in root.root_tactic_deferred_context_keys:
        root.root_tactic_deferred_context_keys.append(key)
        del root.root_tactic_deferred_context_keys[:-4096]
        try:
            proof_state.root_tactic_transient_deferrals += 1
        except Exception:
            pass


def _mark_root_tactic_context_reenabled(
    proof_state: ProofSearchState,
    context_key: str,
) -> None:
    key = str(context_key or "").strip()
    if not key:
        return
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None or not root.root_tactic_deferred_context_keys:
        return
    if key in root.root_tactic_deferred_context_keys:
        return
    if key in root.root_tactic_reenabled_context_keys:
        return
    root.root_tactic_reenabled_context_keys.append(key)
    del root.root_tactic_reenabled_context_keys[:-4096]
    try:
        proof_state.root_tactic_reenabled_by_new_evidence += 1
    except Exception:
        pass


def _clear_root_tactic_context_retry_markers(
    proof_state: ProofSearchState,
    context_key: str,
) -> None:
    """Keep a proof-producing context retryable while finalization is pending."""

    key = str(context_key or "").strip()
    if not key:
        return
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return
    for attr in (
        "root_tactic_attempted_context_keys",
        "root_tactic_deferred_context_keys",
        "root_tactic_continued_context_keys",
    ):
        values = getattr(root, attr, None)
        if not isinstance(values, list):
            continue
        setattr(root, attr, [item for item in values if str(item or "").strip() != key])


def _root_tactic_finalization_pending_retryable(verdict: str) -> bool:
    clean = str(verdict or "").strip()
    if not clean:
        return False
    if clean in {
        "missing_ready_root_assembly_contract",
        "missing_ready_root_exact_helper_contract",
        "root_finalization_contract_not_ready",
        "route_candidate_helper_support_mismatch",
        "route_candidate_missing_declared_helper_support",
    }:
        return True
    return bool(
        ("contract" in clean and "not_ready" in clean)
        or clean.startswith("route_candidate_")
    )


def _root_tactic_transient_should_defer(result: Any) -> bool:
    attempts = list(getattr(result, "attempts", None) or [])
    try:
        candidate_count = int(getattr(result, "candidate_count", 0) or 0)
    except (TypeError, ValueError):
        candidate_count = 0
    exit_reason = str(getattr(result, "exit_reason", "") or "").strip().lower()
    return bool(
        exit_reason == "timeout"
        and candidate_count > 0
        and len(attempts) < candidate_count
    )


def _has_untried_proof_state_root_tactic_context(
    *,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    timeout_s: float,
    max_candidates: int,
    include_deferred: bool = True,
    touch: bool = True,
) -> bool:
    if conv is None or dossier is None or proof_state is None:
        return False
    if max(0, int(max_candidates or 0)) <= 0:
        return False
    helpers = _proof_state_root_tactic_helper_blocks(conv=conv, dossier=dossier)
    if not helpers:
        return False
    key = _root_tactic_context_key(
        goal_statement=str(getattr(conv, "goal_statement", "") or ""),
        preamble=_proof_state_acceptance_preamble(conv),
        helpers=helpers,
        timeout_s=timeout_s,
        max_candidates=max_candidates,
        active_root_targets=_proof_state_active_root_targets_for_frame(dossier),
    )
    deferred_keys = _root_tactic_deferred_context_keys(proof_state)
    if key in deferred_keys:
        if not include_deferred:
            return False
        if (
            key not in _root_tactic_continued_context_keys(proof_state)
            and key not in _root_tactic_attempted_context_keys(proof_state)
        ):
            return True
        if touch:
            try:
                proof_state.root_tactic_deferred_skips += 1
            except Exception:
                pass
        return False
    attempted_keys = _root_tactic_attempted_context_keys(proof_state)
    untried = key not in attempted_keys
    if touch and untried and deferred_keys:
        _mark_root_tactic_context_reenabled(proof_state, key)
    return untried


def _has_current_root_tactic_portfolio_continuation(
    *,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    timeout_s: float,
    max_candidates: int,
) -> bool:
    """Return whether the root owns an exact continuation for this context."""

    if conv is None or dossier is None or proof_state is None:
        return False
    root_node = proof_state.nodes.get(proof_state.root_node_id)
    raw_continuation = (
        getattr(root_node, "root_tactic_portfolio_continuation", {})
        if root_node is not None
        else {}
    )
    continuation = validated_root_tactic_portfolio_continuation(raw_continuation)
    if not continuation:
        return False
    helpers = _proof_state_root_tactic_helper_blocks(conv=conv, dossier=dossier)
    if not helpers:
        return False
    context_key = _root_tactic_context_key(
        goal_statement=str(getattr(conv, "goal_statement", "") or ""),
        preamble=_proof_state_acceptance_preamble(conv),
        helpers=helpers,
        timeout_s=timeout_s,
        max_candidates=max_candidates,
        active_root_targets=_proof_state_active_root_targets_for_frame(dossier),
    )
    if str(continuation.get("context_key") or "") != context_key:
        return False
    # A continuation is lower authority than newly ready exact-root or parent
    # assembly work. Those frontiers may change without changing the tactic's
    # helper-context hash, so never let the fast resume path hide them.
    if _root_equivalent_helper_names(
        conv=conv,
        dossier=dossier,
        proof_state=proof_state,
    ):
        return False
    assembly_frontier = getattr(proof_state, "assembly_frontier", None)
    if callable(assembly_frontier):
        try:
            if assembly_frontier(
                max_nodes=1,
                graph=getattr(dossier, "proof_graph", None),
                mutate=False,
            ):
                return False
        except Exception:
            # The fast path is an optimization only. If a lightweight
            # readiness probe cannot prove it is safe, run normal prechecks.
            return False
    phase = str(continuation.get("phase") or "")
    direct_root_tactic = not _proof_state_active_root_targets_for_frame(dossier)
    return bool(
        (direct_root_tactic and phase in {"", "direct"})
        or (not direct_root_tactic and phase in {"", "active", "fallback"})
    )


def _is_tactic_mode_proof(body: str) -> bool:
    return body == "by" or (
        len(body) > 2 and body.startswith("by") and body[2].isspace()
    )


def _proof_from_decl_application_stub(proof_stub: str) -> str:
    body = str(proof_stub or "").strip()
    if not body:
        return ""
    if _is_tactic_mode_proof(body):
        return body
    lines = [line.rstrip() for line in body.splitlines()]
    if not lines:
        return ""
    proof_lines: List[str] = ["by"]
    for line in lines:
        if not line:
            proof_lines.append("")
        elif line[:1].isspace():
            proof_lines.append(line)
        else:
            proof_lines.append(f"  {line}")
    return "\n".join(proof_lines)


def _proof_from_closed_typed_residual_stub(proof_stub: str) -> str:
    """Mirror ``LeanRunner.extract_typed_residual_batch`` proof semantics."""

    body = str(proof_stub or "").strip()
    if not body:
        return ""
    if _is_tactic_mode_proof(body):
        return body
    return f"by\n  refine ({body})"


def _proof_state_check_preamble(conv: Any) -> str:
    """Return the authoritative preamble for internal proof-state checks."""

    return str(getattr(conv, "lean_preamble", "") or getattr(conv, "preamble", "") or "")


def _proof_state_acceptance_preamble(conv: Any) -> str:
    """Return the preamble that is allowed to certify root acceptance.

    Putnam-style checker preambles carry ``-- ensemble-theorem-target-context:``
    even when the encoded body is a filled solution. When prompt/checker
    bodies differ under answer-safe mode, certify against the prompt-visible
    preamble. Otherwise keep the encoded checker preamble so generic
    omit-variables context is preserved.
    """

    lean_preamble = str(getattr(conv, "lean_preamble", "") or "")
    prompt_preamble = str(getattr(conv, "preamble", "") or "")
    if _needs_answer_safe_feedback_check(conv):
        return prompt_preamble or lean_preamble
    if has_theorem_target_context(lean_preamble):
        return lean_preamble
    return prompt_preamble or lean_preamble


def _proof_state_residual_preamble(conv: Any) -> str:
    """Return the exact Lean environment used to create typed residuals."""

    return _proof_state_check_preamble(conv)


def _proof_state_residual_lemmas(
    conv: Any,
    lemmas: Sequence[str],
) -> List[str]:
    """Return the exact ordered verified-helper context for residual replay."""

    del conv
    return [str(lemma or "") for lemma in lemmas]


def proof_state_residual_elaboration_context_hash(
    conv: Any,
    dossier: Optional[ProofDossier],
    *,
    lean: Any,
    parent_proof_stub: str,
) -> str:
    """Hash one residual route's exact Lean execution environment."""

    return lean_residual_elaboration_context_hash(
        lean,
        preamble_override=_proof_state_residual_preamble(conv),
        ordered_lemmas=_proof_state_residual_lemmas(
            conv,
            _proof_state_verified_helper_blocks(dossier),
        ),
        proof_code=str(parent_proof_stub or ""),
    )


def proof_state_current_residual_route_context_hashes(
    *,
    conv: Any,
    dossier: Optional[ProofDossier],
    lean: Any,
    proof_state: Optional[ProofSearchState],
) -> Dict[Tuple[str, str], str]:
    """Return exact current context hashes once for every residual route."""

    if proof_state is None:
        return {}
    contexts: Dict[Tuple[str, str], str] = {}
    for parent in proof_state.nodes.values():
        for group in list(parent.assembly_attempt_groups or ()):
            if not proof_state_source_requires_residual_goal_attestation(
                group.source
            ):
                continue
            contexts[(parent.node_id, group.assembly_id)] = (
                proof_state_residual_elaboration_context_hash(
                    conv,
                    dossier,
                    lean=lean,
                    parent_proof_stub=group.proof_stub,
                )
            )
    return contexts


def proof_state_node_current_residual_attestation_status(
    *,
    conv: Any,
    dossier: Optional[ProofDossier],
    lean: Any,
    proof_state: Optional[ProofSearchState],
    node_or_id: Any,
) -> str:
    """Validate a child against every exact current route in one graph pass."""

    if proof_state is None:
        return "residual_elaboration_attestation_required"
    getter = getattr(proof_state, "residual_goal_attestation_status", None)
    if not callable(getter):
        return "residual_elaboration_attestation_required"
    contexts = proof_state_current_residual_route_context_hashes(
        conv=conv,
        dossier=dossier,
        lean=lean,
        proof_state=proof_state,
    )
    return str(
        getter(
            node_or_id,
            route_elaboration_context_hashes=contexts,
        )
        or ""
    ).strip()


def _typed_residual_operation_timeout(lean: Any, timeout_s: float) -> float:
    """Give typed residual replay a useful, operator-controlled time slice."""

    configured = 0.0
    try:
        configured = float(getattr(getattr(lean, "cfg", None), "timeout_s", 0.0) or 0.0)
    except (TypeError, ValueError):
        configured = 0.0
    try:
        requested = float(timeout_s or 0.0)
    except (TypeError, ValueError):
        requested = 0.0
    # This is a recoverable Lean-operation admission timeout, not a worker or
    # session lease. Underfunded enclosing actions defer before launch below.
    return max(300.0, configured, requested)


def stage_closed_typed_residual_acceptance(
    *,
    conv: Any,
    dossier: Optional[ProofDossier],
    lean: Any,
    proof_state: ProofSearchState,
    parent_node: ProofStateNode,
    source: str,
    parent_proof_stub: str,
    max_goals: int,
    origin_metadata: Optional[Mapping[str, Any]] = None,
    action_metadata: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Durably hand a zero-goal receipt to normal helper acceptance.

    A typed extraction receipt establishes only that the exact stub closes in
    its current Lean context. It is not the answer-safe helper/root acceptance
    boundary. Persist that paid candidate so a later action quantum performs
    normal acceptance without rerunning extraction or discarding the proof.
    """

    exact_stub = str(parent_proof_stub or "").strip()
    exact_source = str(source or "").strip()
    if not exact_stub or not exact_source:
        return False
    preamble = _proof_state_residual_preamble(conv)
    lemmas = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    request_hash, context_hash = _typed_residual_request_hashes(
        lean=lean,
        proof_state=proof_state,
        parent_node=parent_node,
        parent_proof_stub=exact_stub,
        source=exact_source,
        preamble=preamble,
        lemmas=lemmas,
        max_goals=max(1, int(max_goals or 0)),
    )
    next_action_metadata = dict(action_metadata or {})
    next_action_metadata["typed_residual_closed_pending_acceptance"] = True
    next_action_metadata.setdefault("acceptance_attempt_count", 0)
    retry_key = _verifier_retry_key(
        stage="typed_residual_helper_acceptance",
        request_hash=request_hash,
        context_hash=context_hash,
        verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
    )
    return proof_state.record_pending_residual_goal_extraction(
        parent_node_id=parent_node.node_id,
        source=exact_source,
        parent_proof_stub=exact_stub,
        max_goals=max(1, int(max_goals or 0)),
        request_context_hash=request_hash,
        elaboration_context_hash=context_hash,
        origin_metadata=dict(origin_metadata or {}),
        action_metadata=next_action_metadata,
        retry_count=0,
        verifier_retry_key=retry_key,
    )


_TYPED_RESIDUAL_REATTESTATION_MAX_GOALS = 256


def _typed_residual_route_goal_cap(
    *,
    proof_state: ProofSearchState,
    parent: ProofStateNode,
    group: Any,
    surviving_child_ids: Sequence[str],
) -> int:
    """Recover the original residual batch width after graph pruning.

    New routes persist ``residual_goal_slot_count`` on the assembly group.
    Legacy routes can recover it from any surviving exact child receipt. If a
    damaged legacy graph lost every child projection, use the Lean receipt
    schema's bounded maximum: verifier replay remains the authority and this
    avoids discarding a paid parent proof solely because public topology was
    incomplete.
    """

    try:
        expected = max(0, int(getattr(group, "residual_goal_slot_count", 0) or 0))
    except (TypeError, ValueError):
        expected = 0
    expected = max(expected, len(list(getattr(group, "child_node_ids", []) or [])))
    parent_stub_sha256 = hashlib.sha256(
        str(getattr(group, "proof_stub", "") or "").encode("utf-8")
    ).hexdigest()
    for child_id in list(surviving_child_ids or ()):
        child = proof_state.nodes.get(str(child_id or ""))
        if child is None:
            continue
        for authority in _residual_goal_attestation_authorities(
            getattr(child, "residual_goal_attestation", {}) or {}
        ):
            if (
                str(authority.get("source") or "")
                != str(getattr(group, "source", "") or "")
                or str(authority.get("parent_node_id") or "") != parent.node_id
                or str(authority.get("parent_proof_stub_sha256") or "")
                != parent_stub_sha256
            ):
                continue
            slot_count = authority.get("slot_count")
            if (
                isinstance(slot_count, bool)
                or not isinstance(slot_count, int)
                or slot_count <= 0
            ):
                continue
            expected = max(expected, int(slot_count))
    if expected <= 0:
        expected = _TYPED_RESIDUAL_REATTESTATION_MAX_GOALS
    return min(_TYPED_RESIDUAL_REATTESTATION_MAX_GOALS, expected)


def _typed_residual_request_hashes(
    *,
    lean: Any,
    proof_state: ProofSearchState,
    parent_node: ProofStateNode,
    parent_proof_stub: str,
    source: str,
    preamble: str,
    lemmas: Sequence[str],
    max_goals: int,
) -> Tuple[str, str]:
    exact_lemmas = list(lemmas or ())
    context_hash = lean_residual_elaboration_context_hash(
        lean,
        preamble_override=str(preamble or ""),
        ordered_lemmas=exact_lemmas,
        proof_code=str(parent_proof_stub or ""),
    )
    request_hash = hashlib.sha256(
        json.dumps(
            {
                "format": "pending-typed-residual-request-v2",
                "verifier_generation": LEAN_RESIDUAL_VERIFIER_GENERATION,
                "source": str(source or ""),
                "parent_node_id": str(parent_node.node_id or ""),
                "parent_target_sha256": hashlib.sha256(
                    str(parent_node.target or "").encode("utf-8")
                ).hexdigest(),
                "statement_environment_hash": str(
                    getattr(proof_state, "statement_environment_hash", "") or ""
                ),
                "parent_proof_stub_sha256": hashlib.sha256(
                    str(parent_proof_stub or "").encode("utf-8")
                ).hexdigest(),
                "elaboration_context_hash": context_hash,
                "max_goals": max(0, int(max_goals or 0)),
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    ).hexdigest()
    return request_hash, context_hash


def _verifier_retry_key(
    *,
    stage: str,
    request_hash: str,
    context_hash: str,
    verifier_generation: str,
) -> str:
    """Bind retry frequency to one exact candidate, stage, and verifier."""

    return hashlib.sha256(
        json.dumps(
            {
                "format": "proof-state-verifier-retry-identity-v1",
                "stage": str(stage or ""),
                "request_hash": str(request_hash or ""),
                "context_hash": str(context_hash or ""),
                "verifier_generation": str(verifier_generation or ""),
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    ).hexdigest()


_HELPER_ACCEPTANCE_VERIFIER_GENERATION = "proof-state-helper-acceptance-v1"


def _helper_acceptance_request_hashes(
    *,
    conv: Any,
    dossier: ProofDossier,
    node: ProofStateNode,
    helper_block: str,
    source: str,
    context_hash: str = "",
    refresh_quality: bool = True,
) -> Tuple[str, str, str]:
    """Hash the complete answer-safe helper acceptance plan."""

    verified_helpers = list(
        _proof_state_verified_helper_blocks(
            dossier,
            refresh_quality=refresh_quality,
        )
    )
    exact_context_hash = hashlib.sha256(
        json.dumps(
            {
                "format": "helper-acceptance-context-v1",
                "primary_preamble": _proof_state_check_preamble(conv),
                "answer_safe_preamble": str(
                    getattr(conv, "preamble", "") or ""
                ),
                "verified_helpers": verified_helpers,
                "target": str(node.target or ""),
                "statement_environment_hash": str(
                    getattr(node, "statement_environment_hash", "") or ""
                ),
                "caller_context_hash": str(context_hash or ""),
                "suppress_solution_placeholders": bool(
                    getattr(conv, "suppress_solution_placeholders", False)
                ),
                "allow_official_answer_visibility": bool(
                    getattr(conv, "allow_official_answer_visibility", False)
                ),
                "reserved_helper_names": sorted(
                    str(name)
                    for name in getattr(dossier, "verified_helpers", {})
                ),
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    ).hexdigest()
    request_hash = hashlib.sha256(
        json.dumps(
            {
                "format": "helper-acceptance-request-v1",
                "helper_block_sha256": hashlib.sha256(
                    str(helper_block or "").encode("utf-8")
                ).hexdigest(),
                "source": str(source or ""),
                "context_hash": exact_context_hash,
                "verifier_generation": _HELPER_ACCEPTANCE_VERIFIER_GENERATION,
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    ).hexdigest()
    retry_key = _verifier_retry_key(
        stage="helper_acceptance",
        request_hash=request_hash,
        context_hash=exact_context_hash,
        verifier_generation=_HELPER_ACCEPTANCE_VERIFIER_GENERATION,
    )
    return request_hash, exact_context_hash, retry_key


def stage_pending_helper_acceptance(
    *,
    conv: Any,
    dossier: ProofDossier,
    node: ProofStateNode,
    helper_block: str,
    source: str,
    context_hash: str = "",
    continuation: Optional[Mapping[str, Any]] = None,
    refresh_quality: bool = True,
) -> bool:
    """Persist one exact paid helper candidate before verifier launch."""

    exact_block = str(helper_block or "").strip()
    if not exact_block or not helper_decl_name(exact_block):
        return False
    request_hash, exact_context_hash, retry_key = (
        _helper_acceptance_request_hashes(
            conv=conv,
            dossier=dossier,
            node=node,
            helper_block=exact_block,
            source=source,
            context_hash=context_hash,
            refresh_quality=refresh_quality,
        )
    )
    try:
        exact_continuation = json.loads(
            json.dumps(dict(continuation or {}), sort_keys=True)
        )
    except (TypeError, ValueError):
        return False
    existing = dict(getattr(node, "pending_helper_acceptance", {}) or {})
    if existing:
        existing_block = str(existing.get("helper_block") or "").strip()
        existing_source = str(existing.get("source") or "")
        existing_target_hash = str(existing.get("target_hash") or "")
        if (
            not existing_block
            or not helper_decl_name(existing_block)
            or existing_target_hash != text_hash(node.target)
        ):
            # A malformed or target-stale owner can never be projected onto
            # the acceptance frontier. Reclaim the single-owner slot instead
            # of letting an unreachable write-ahead record lock it forever.
            node.pending_helper_acceptance = {}
            existing = {}
    if existing:
        existing_block = str(existing.get("helper_block") or "").strip()
        existing_source = str(existing.get("source") or "")
        existing_target_hash = str(existing.get("target_hash") or "")
        if (
            existing_block != exact_block
            or existing_source != str(source or "")
            or existing_target_hash != text_hash(node.target)
        ):
            # This is a single-owner write-ahead slot. A second producer must
            # yield to the already-paid candidate instead of overwriting it.
            return False
        if str(existing.get("acceptance_request_hash") or "") == request_hash:
            # The exact candidate is already durably owned. Only the
            # first-class helper-acceptance lane may consult its cooldown and
            # launch it; returning false here prevents producer re-entry (and
            # process restart) from bypassing durable verifier backoff or
            # replacing the original typed continuation.
            return False
    node.pending_helper_acceptance = {
        "schema_version": 1,
        "helper_block": exact_block,
        "source": str(source or ""),
        "target_hash": text_hash(node.target),
        "context_hash": exact_context_hash,
        "caller_context_hash": str(context_hash or ""),
        "acceptance_request_hash": request_hash,
        "verifier_retry_key": retry_key,
        "attempt_count": "0",
        "continuation": exact_continuation,
    }
    return True


def ensure_current_helper_acceptance_retries(
    *,
    conv: Any,
    dossier: ProofDossier,
    proof_state: Optional[ProofSearchState],
) -> List[str]:
    """Rearm exact pending helpers whose acceptance environment changed.

    The scheduler may safely hide cooling work only after this reconciliation:
    a preamble/helper/policy change creates a new verifier identity and must be
    immediately executable, while mere session recreation must retain the old
    cooldown.
    """

    if proof_state is None:
        return []
    rearmed: List[str] = []
    for node in proof_state.nodes.values():
        if node.status != "open":
            continue
        pending = dict(node.pending_helper_acceptance or {})
        helper_block = str(pending.get("helper_block") or "").strip()
        if (
            not helper_block
            or not helper_decl_name(helper_block)
            or str(pending.get("target_hash") or "") != text_hash(node.target)
        ):
            prior_retry_key = str(pending.get("verifier_retry_key") or "").strip()
            node.pending_helper_acceptance = {}
            if prior_retry_key:
                proof_state.clear_verifier_retry_state(node, prior_retry_key)
            continue
        caller_context_hash = str(
            pending.get("caller_context_hash")
            if "caller_context_hash" in pending
            else pending.get("context_hash") or ""
        )
        request_hash, exact_context_hash, retry_key = (
            _helper_acceptance_request_hashes(
                conv=conv,
                dossier=dossier,
                node=node,
                helper_block=helper_block,
                source=str(pending.get("source") or ""),
                context_hash=caller_context_hash,
            )
        )
        if str(pending.get("acceptance_request_hash") or "") == request_hash:
            continue
        prior_retry_key = str(pending.get("verifier_retry_key") or "").strip()
        pending["attempt_count"] = "0"
        pending["acceptance_request_hash"] = request_hash
        pending["context_hash"] = exact_context_hash
        pending["caller_context_hash"] = caller_context_hash
        pending["verifier_retry_key"] = retry_key
        pending.pop("verifier_failure", None)
        node.pending_helper_acceptance = pending
        if prior_retry_key and prior_retry_key != retry_key:
            proof_state.clear_verifier_retry_state(node, prior_retry_key)
        rearmed.append(node.node_id)
    return rearmed


def retain_pending_helper_acceptance_retry(
    *,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    status: Mapping[str, Any],
) -> Dict[str, Any]:
    """Advance retry frequency for a staged helper without losing it."""

    pending = dict(node.pending_helper_acceptance or {})
    retry_key = str(pending.get("verifier_retry_key") or "").strip()
    request_hash = str(
        pending.get("acceptance_request_hash") or ""
    ).strip()
    context_hash = str(pending.get("context_hash") or "").strip()
    attempted = bool(status.get("lean_attempted", True))
    error_kind = str(
        status.get("error_kind") or "acceptance_infrastructure_failure"
    )
    failure_fingerprint = hashlib.sha256(
        json.dumps(
            {"stage": "helper_acceptance", "kind": error_kind},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    retry_record = {}
    if attempted and retry_key and request_hash:
        retry_record = proof_state.record_verifier_retry_failure(
            node,
            retry_key=retry_key,
            stage="helper_acceptance",
            request_hash=request_hash,
            context_hash=context_hash,
            verifier_generation=_HELPER_ACCEPTANCE_VERIFIER_GENERATION,
            failure_kind=error_kind,
            failure_fingerprint=failure_fingerprint,
        )
    pending["attempt_count"] = str(
        _durable_nonnegative_int(pending.get("attempt_count", 0))
        + int(attempted)
    )
    pending["verifier_failure"] = {
        "attempted": attempted,
        "failure_kind": error_kind[:160],
        "failure_fingerprint": failure_fingerprint,
        "retry_after_epoch_s": float(
            retry_record.get("retry_after_epoch_s") or 0.0
        ),
        "consecutive_failure_count": int(
            retry_record.get("consecutive_failure_count") or 0
        ),
    }
    node.pending_helper_acceptance = pending
    return dict(retry_record)


def ensure_current_typed_residual_attestation_retries(
    *,
    conv: Any,
    dossier: Optional[ProofDossier],
    lean: Any,
    proof_state: Optional[ProofSearchState],
) -> List[str]:
    """Materialize verifier-only retries for context-stale residual routes.

    A receipt proves the exact residual batch only in its ordered
    preamble/helper context. When that context changes, preserve the paid
    parent proof stub and schedule a new typed extraction; never expose an old
    delaboration to a provider and never permanently quarantine it merely for
    context drift.
    """

    if proof_state is None or dossier is None:
        return []
    current_preamble = _proof_state_residual_preamble(conv)
    current_lemmas = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    status_getter = getattr(
        proof_state,
        "residual_goal_attestation_status",
        None,
    )
    recorder = getattr(
        proof_state,
        "record_pending_residual_goal_extraction",
        None,
    )
    if not callable(status_getter) or not callable(recorder):
        return []
    route_contexts = proof_state_current_residual_route_context_hashes(
        conv=conv,
        dossier=dossier,
        lean=lean,
        proof_state=proof_state,
    )
    try:
        _required, _authorized, route_validity = (
            proof_state._residual_goal_attestation_validation(  # noqa: SLF001
                route_elaboration_context_hashes=route_contexts,
            )
        )
    except Exception:
        route_validity = {}
    scheduled: List[str] = []
    for parent in list(proof_state.nodes.values()):
        if parent.status in {"proved", "obsolete", "rejected", "failed"}:
            continue
        rejected_requests = set(
            str(item or "")
            for item in list(
                getattr(
                    parent,
                    "residual_attestation_rejected_request_hashes",
                    [],
                )
                or []
            )
        )
        existing_pending = dict(
            getattr(parent, "pending_residual_goal_extraction", {}) or {}
        )
        cooling_pending_request_hash = ""
        if existing_pending:
            pending_action = dict(existing_pending.get("action_metadata") or {})
            pending_retry_key = str(
                existing_pending.get("verifier_retry_key") or ""
            ).strip()
            cooling_reattestation = bool(
                pending_action.get("reattestation")
                and pending_retry_key
                and proof_state.verifier_retry_status(
                    parent,
                    pending_retry_key,
                )
                == "cooling"
            )
            if not cooling_reattestation:
                # The retry executor rematerializes this exact paid frame under
                # the current context. Never overwrite a singular durable slot.
                continue
            cooling_pending_request_hash = str(
                existing_pending.get("request_context_hash") or ""
            )
        deferred_retries = dict(
            getattr(
                parent,
                "residual_attestation_deferred_request_retries",
                {},
            )
            or {}
        )
        last_deferred_request_hash = str(
            getattr(
                parent,
                "residual_attestation_last_deferred_request_hash",
                "",
            )
            or ""
        )
        route_candidates: List[
            Tuple[Any, List[str], str, str, int, str]
        ] = []
        for group in list(parent.assembly_attempt_groups or ()):
            if group.status in {"proved", "obsolete"}:
                continue
            if not proof_state_source_requires_residual_goal_attestation(
                group.source
            ):
                continue
            child_ids = [
                str(child_id or "")
                for child_id in list(group.child_node_ids or ())
                if str(child_id or "") in proof_state.nodes
            ]
            if not str(group.proof_stub or "").strip():
                continue
            route_key = (parent.node_id, group.assembly_id)
            if bool(route_validity.get(route_key, False)):
                continue
            max_goals = _typed_residual_route_goal_cap(
                proof_state=proof_state,
                parent=parent,
                group=group,
                surviving_child_ids=child_ids,
            )
            request_hash, elaboration_context_hash = (
                _typed_residual_request_hashes(
                    lean=lean,
                    proof_state=proof_state,
                    parent_node=parent,
                    parent_proof_stub=group.proof_stub,
                    source=group.source,
                    preamble=current_preamble,
                    lemmas=current_lemmas,
                    max_goals=max_goals,
                )
            )
            if request_hash in rejected_requests:
                continue
            retry_key = _verifier_retry_key(
                stage="typed_residual_extraction",
                request_hash=request_hash,
                context_hash=elaboration_context_hash,
                verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
            )
            route_candidates.append(
                (
                    group,
                    child_ids,
                    request_hash,
                    elaboration_context_hash,
                    max_goals,
                    retry_key,
                )
            )

        current_request_hashes = {
            request_hash
            for (
                _group,
                _child_ids,
                request_hash,
                _context_hash,
                _max_goals,
                _retry_key,
            )
            in route_candidates
        }
        # Drop memory for routes that disappeared or whose exact
        # helper/preamble request changed. Keep the map bounded even when a
        # very long run repeatedly changes context.
        deferred_retries = {
            request_hash: _durable_nonnegative_int(retry_count)
            for request_hash, retry_count in deferred_retries.items()
            if request_hash in current_request_hashes
        }
        parent.residual_attestation_deferred_request_retries = dict(
            list(deferred_retries.items())[-256:]
        )
        if not route_candidates:
            if cooling_pending_request_hash:
                proof_state.clear_pending_residual_goal_extraction(parent)
            parent.residual_attestation_last_deferred_request_hash = ""
            continue
        ready_candidates = [
            candidate
            for candidate in route_candidates
            if proof_state.verifier_retry_status(parent, candidate[5])
            != "cooling"
        ]
        cooling_anchor_only = False
        if ready_candidates:
            route_candidates = ready_candidates
        else:
            # Preserve one singular, non-executable pending frame as the
            # durable checkpoint/wakeup anchor. It must be the earliest route
            # to become eligible: child_closure derives its next wake time
            # from pending frames, while the other route-local cooldowns live
            # only in the retry ledger.
            route_candidates = sorted(
                route_candidates,
                key=lambda candidate: (
                    proof_state.verifier_retry_next_eligible_at(
                        parent,
                        candidate[5],
                    ),
                    candidate[2],
                ),
            )
            earliest_cooling_request_hash = route_candidates[0][2]
            if (
                cooling_pending_request_hash
                and cooling_pending_request_hash
                == earliest_cooling_request_hash
            ):
                continue
            if cooling_pending_request_hash:
                proof_state.clear_pending_residual_goal_extraction(parent)
            route_candidates = [route_candidates[0]]
            cooling_anchor_only = True
        if cooling_pending_request_hash:
            parent.residual_attestation_last_deferred_request_hash = (
                cooling_pending_request_hash
            )
            proof_state.clear_pending_residual_goal_extraction(parent)
        request_order = [candidate[2] for candidate in route_candidates]
        if last_deferred_request_hash in request_order:
            prior_index = request_order.index(last_deferred_request_hash)
            route_candidates = (
                route_candidates[prior_index + 1 :]
                + route_candidates[: prior_index + 1]
            )
        else:
            parent.residual_attestation_last_deferred_request_hash = ""
        (
            group,
            child_ids,
            request_hash,
            elaboration_context_hash,
            max_goals,
            retry_key,
        ) = route_candidates[0]
        if recorder(
                parent_node_id=parent.node_id,
                source=group.source,
                parent_proof_stub=group.proof_stub,
                max_goals=max_goals,
                request_context_hash=request_hash,
                elaboration_context_hash=elaboration_context_hash,
                origin_metadata={
                    "kind": "residual_attestation_context_refresh",
                    "assembly_id": str(group.assembly_id or ""),
                    "child_node_ids": list(child_ids),
                    "residual_goal_slot_count": max_goals,
                },
                action_metadata={
                    "reattestation": True,
                    "prior_assembly_id": str(group.assembly_id or ""),
                },
                retry_count=_durable_nonnegative_int(
                    deferred_retries.get(request_hash, 0)
                ),
                verifier_retry_key=retry_key,
            ):
            if not cooling_anchor_only:
                scheduled.append(parent.node_id)
    return list(dict.fromkeys(scheduled))


async def _extract_and_spawn_typed_residual_goals(
    *,
    lean: LeanRunner,
    proof_state: ProofSearchState,
    parent_node: ProofStateNode,
    parent_proof_stub: str,
    source: str,
    preamble: str,
    lemmas: Sequence[str],
    timeout_s: float,
    max_goals: int,
    deadline_monotonic: float = 0.0,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    origin_metadata: Optional[Mapping[str, Any]] = None,
    action_metadata: Optional[Mapping[str, Any]] = None,
) -> Tuple[List[str], int, str]:
    """Extract and atomically admit Lean-authoritative residual obligations.

    Diagnostic ``remaining_goals`` are intentionally not accepted here. Lean
    captures each residual metavariable's exact type, closes it over its local
    context, reparses it in the same command, and proves the replayed source is
    definitionally equal before proof-state admission can occur.

    The return is ``(spawned_node_ids, typed_goal_count, status)``. Timeout,
    cancellation, unavailable infrastructure, an underfunded outer deadline,
    and a callback that expires before admission all return a ``*_deferred``
    status with no graph mutation. Admission itself is the commit point. When
    an optional outer rollback checkpoint exists, a deadline that wins during
    admission rolls the batch back; without that optional checkpoint, a
    successfully atomic ``spawn_typed_residual_batch`` remains admitted rather
    than stranding durable children behind a false deferred result.
    """

    def callback_expired() -> bool:
        try:
            return bool(deadline_exhausted and deadline_exhausted())
        except Exception:
            return True

    prior_pending = dict(
        getattr(parent_node, "pending_residual_goal_extraction", {}) or {}
    )
    retry_count = _durable_nonnegative_int(prior_pending.get("retry_count"))
    exact_stub = str(parent_proof_stub or "")
    exact_preamble = str(preamble or "")
    exact_lemmas = list(lemmas or ())
    request_context_hash, elaboration_context_hash = (
        _typed_residual_request_hashes(
            lean=lean,
            proof_state=proof_state,
            parent_node=parent_node,
            parent_proof_stub=exact_stub,
            source=str(source or ""),
            preamble=exact_preamble,
            lemmas=exact_lemmas,
            max_goals=max_goals,
        )
    )
    retry_key = _verifier_retry_key(
        stage="typed_residual_extraction",
        request_hash=request_context_hash,
        context_hash=elaboration_context_hash,
        verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
    )

    def remember_deferred(
        status: str,
        goal_count: int = 0,
        *,
        attempted: bool = False,
        failure_kind: str = "",
        failure_fingerprint: str = "",
        diagnostic_preview: str = "",
    ) -> Tuple[List[str], int, str]:
        next_retry_count = retry_count + int(bool(attempted))
        retry_record: Dict[str, Any] = {}
        if attempted:
            retry_record = proof_state.record_verifier_retry_failure(
                parent_node,
                retry_key=retry_key,
                stage="typed_residual_extraction",
                request_hash=request_context_hash,
                context_hash=elaboration_context_hash,
                verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
                failure_kind=str(failure_kind or status),
                failure_fingerprint=str(failure_fingerprint or ""),
            )
        recorder = getattr(proof_state, "record_pending_residual_goal_extraction", None)
        if callable(recorder):
            recorder(
                parent_node_id=str(parent_node.node_id or ""),
                source=str(source or ""),
                parent_proof_stub=exact_stub,
                max_goals=max_goals,
                request_context_hash=request_context_hash,
                elaboration_context_hash=elaboration_context_hash,
                origin_metadata=dict(origin_metadata or {}),
                action_metadata=dict(action_metadata or {}),
                retry_count=next_retry_count,
                verifier_retry_key=retry_key,
                verifier_failure={
                    "attempted": bool(attempted),
                    "failure_kind": str(failure_kind or "")[:160],
                    "failure_fingerprint": str(failure_fingerprint or ""),
                    "diagnostic_preview": str(diagnostic_preview or "")[:480],
                    "retry_after_epoch_s": float(
                        retry_record.get("retry_after_epoch_s") or 0.0
                    ),
                    "consecutive_failure_count": int(
                        retry_record.get("consecutive_failure_count") or 0
                    ),
                },
            )
        return [], int(goal_count or 0), status

    def clear_pending() -> None:
        clearer = getattr(proof_state, "clear_pending_residual_goal_extraction", None)
        if callable(clearer):
            clearer(str(parent_node.node_id or ""))

    if callback_expired():
        return remember_deferred("residual_attestation_deadline_deferred")
    extractor = getattr(lean, "extract_typed_residual_batch", None)
    admission = getattr(proof_state, "spawn_typed_residual_batch", None)
    if not callable(extractor) or not callable(admission):
        return remember_deferred("residual_attestation_infrastructure_deferred")

    if proof_state.verifier_retry_status(parent_node, retry_key) == "cooling":
        return remember_deferred("residual_attestation_cooldown_deferred")

    timeout = _typed_residual_operation_timeout(lean, timeout_s)
    admitted = _fully_funded_operation_timeout(timeout, deadline_monotonic)
    if admitted <= 0.0:
        return remember_deferred("residual_attestation_deadline_deferred")

    extraction_attempted = False

    async def run_extraction() -> Any:
        nonlocal extraction_attempted
        extraction_attempted = True
        return await extractor(
            str(parent_node.target or ""),
            str(parent_proof_stub or ""),
            list(lemmas or ()),
            preamble_override=str(preamble or ""),
            timeout_s=admitted,
        )

    try:
        result = await _await_serialized_lean_operation(
            lean,
            run_extraction,
            timeout_s=admitted,
            deadline_monotonic=deadline_monotonic,
            operation_label="proof_state_typed_residual_receipt",
        )
    except asyncio.CancelledError as exc:
        # Cancellation controls the caller, but it has no authority to erase
        # the already-paid producer batch. Persist the exact parent stub and
        # ordered suffix before propagating cancellation to the session.
        remember_deferred(
            "residual_attestation_cancelled_deferred",
            attempted=extraction_attempted,
            failure_kind=type(exc).__name__,
            failure_fingerprint=hashlib.sha256(
                b"typed_residual_extraction:cancelled:CancelledError"
            ).hexdigest(),
        )
        raise
    except (_LeanOperationDeadline, asyncio.TimeoutError) as exc:
        return remember_deferred(
            "residual_attestation_timeout_deferred",
            attempted=extraction_attempted,
            failure_kind=type(exc).__name__,
            failure_fingerprint=hashlib.sha256(
                f"typed_residual_extraction:timeout:{type(exc).__name__}".encode(
                    "utf-8"
                )
            ).hexdigest(),
        )
    except Exception as exc:
        return remember_deferred(
            "residual_attestation_infrastructure_deferred",
            attempted=extraction_attempted,
            failure_kind=type(exc).__name__,
            failure_fingerprint=hashlib.sha256(
                (
                    "typed_residual_extraction:exception:"
                    + type(exc).__name__
                ).encode("utf-8")
            ).hexdigest(),
            diagnostic_preview=str(exc)[:480],
        )

    if callback_expired() or (
        float(deadline_monotonic or 0.0) > 0.0
        and time.monotonic() >= float(deadline_monotonic)
    ):
        return remember_deferred("residual_attestation_deadline_deferred")
    receipt = getattr(result, "receipt", None)
    if not bool(getattr(result, "ok", False)) or receipt is None:
        error = str(getattr(result, "error", "") or "").strip().lower()
        failure_phase = str(
            getattr(result, "failure_phase", "") or ""
        ).strip().lower()
        if error == "residual_lean_rejected":
            proof_state.clear_verifier_retry_state(parent_node, retry_key)
            clear_pending()
            return [], 0, "residual_attestation_lean_rejected"
        if failure_phase == "input":
            # Missing/admitted parent or proof text is a deterministic invalid
            # request, not verifier availability. Retaining it would create a
            # permanent zero-attempt replay loop.
            proof_state.clear_verifier_retry_state(parent_node, retry_key)
            clear_pending()
            return [], 0, "residual_attestation_input_rejected"
        # A missing/duplicate nonce marker, malformed JSON, invalid schema,
        # open Expr, identity mismatch, environment outage, or timeout is a
        # receipt/infrastructure failure. None is evidence against the proof.
        return remember_deferred(
            "residual_attestation_infrastructure_deferred",
            attempted=bool(getattr(result, "attempted", True)),
            failure_kind=str(
                getattr(result, "failure_kind", "") or error or "unknown"
            ),
            failure_fingerprint=str(
                getattr(result, "failure_fingerprint", "") or ""
            ),
            diagnostic_preview=str(
                getattr(result, "diagnostic_preview", "") or ""
            ),
        )

    receipt_goals = tuple(getattr(receipt, "goals", ()) or ())
    goal_count = len(receipt_goals)
    if goal_count == 0:
        proof_state.clear_verifier_retry_state(parent_node, retry_key)
        clear_pending()
        return [], 0, "residual_attestation_closed_goal"
    goal_limit = max(0, int(max_goals or 0))
    if goal_count > goal_limit:
        proof_state.clear_verifier_retry_state(parent_node, retry_key)
        clear_pending()
        return [], goal_count, "residual_attestation_goal_cap_exceeded"
    for goal in receipt_goals:
        statement = str(getattr(goal, "statement", "") or "")
        rejection = proof_state._remaining_goal_item_rejection(  # noqa: SLF001
            {"target": statement, "hypotheses": []},
            parent_proof_stub=str(parent_proof_stub or ""),
            source=str(source or ""),
        )
        if rejection:
            proof_state.clear_verifier_retry_state(parent_node, retry_key)
            clear_pending()
            return [], goal_count, f"residual_attestation_policy_rejected:{rejection}"
        signature = proof_state._goal_signature(  # noqa: SLF001
            statement,
            [],
            source_failure=str(source or ""),
        )
        target_key = proof_state._target_environment_index_key(  # noqa: SLF001
            signature.normalized_statement_hash,
            proof_state.statement_environment_hash,
        )
        existing_id = proof_state._node_by_target.get(target_key)  # noqa: SLF001
        existing = proof_state.nodes.get(existing_id) if existing_id else None
        if existing is not None and existing.status in {
            "obsolete",
            "failed",
            "rejected",
        }:
            proof_state.clear_verifier_retry_state(parent_node, retry_key)
            clear_pending()
            return [], goal_count, (
                "residual_attestation_policy_rejected:"
                "terminal_existing_residual_goal"
            )
        if existing is not None and proof_state._would_create_cycle(  # noqa: SLF001
            parent_node.node_id,
            existing.node_id,
        ):
            proof_state.clear_verifier_retry_state(parent_node, retry_key)
            clear_pending()
            return [], goal_count, (
                "residual_attestation_policy_rejected:cyclic_residual_goal"
            )

    if callback_expired() or (
        float(deadline_monotonic or 0.0) > 0.0
        and time.monotonic() >= float(deadline_monotonic)
    ):
        return remember_deferred(
            "residual_attestation_deadline_deferred", goal_count
        )
    checkpoint_id = ""
    checkpoint = getattr(proof_state, "checkpoint", None)
    commit = getattr(proof_state, "commit", None)
    rollback = getattr(proof_state, "rollback", None)
    if callable(checkpoint) and callable(commit) and callable(rollback):
        try:
            checkpoint_id = str(
                checkpoint(label="typed_residual_batch_admission") or ""
            )
        except Exception:
            checkpoint_id = ""
    try:
        spawned = admission(
            receipt,
            source=str(source or ""),
            parent_node_id=str(parent_node.node_id or ""),
            parent_proof_stub=str(parent_proof_stub or ""),
            max_goals=goal_limit,
        )
    except Exception:
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return remember_deferred(
            "residual_attestation_admission_deferred", goal_count
        )
    spawned_ids = [str(item) for item in list(spawned or ()) if str(item or "")]
    admission_status = str(getattr(spawned, "status", "") or "")
    admission_reason = str(getattr(spawned, "reason", "") or "")
    if spawned_ids and admission_status in {"", "admitted"}:
        pass
    elif admission_status == "terminal_rejected":
        # Spawn owns its inner checkpoint. Rolling the outer snapshot back
        # here would restore pending extraction and drop frontier telemetry
        # that the admission result already settled.
        if checkpoint_id and callable(commit):
            try:
                commit(checkpoint_id)
            except Exception:
                pass
        proof_state.clear_verifier_retry_state(parent_node, retry_key)
        clear_pending()
        mapped = {
            "attested_residual_goal_cap_exceeded": (
                "residual_attestation_goal_cap_exceeded"
            ),
        }.get(
            admission_reason,
            (
                f"residual_attestation_{admission_reason}"
                if admission_reason
                else "residual_attestation_admission_rejected"
            ),
        )
        return [], goal_count, mapped
    elif not spawned_ids:
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
        return remember_deferred(
            "residual_attestation_admission_deferred", goal_count
        )
    if callback_expired() or (
        float(deadline_monotonic or 0.0) > 0.0
        and time.monotonic() >= float(deadline_monotonic)
    ):
        if checkpoint_id and callable(rollback):
            try:
                rollback(checkpoint_id)
            except Exception:
                pass
            return remember_deferred(
                "residual_attestation_deadline_deferred", goal_count
            )
        # ``spawn_typed_residual_batch`` owns its own atomic admission
        # boundary. If an optional outer rollback checkpoint is unavailable,
        # a completed admission is the commit point: never strand durable
        # children while reporting that the route was merely deferred.
    if checkpoint_id and callable(commit):
        try:
            commit(checkpoint_id)
        except Exception:
            # The in-memory mutation remains coherent; failure to discard a
            # rollback snapshot is cleanup telemetry, not mathematical proof.
            pass
    proof_state.clear_verifier_retry_state(parent_node, retry_key)
    clear_pending()
    return spawned_ids, goal_count, "residual_attestation_admitted"


async def _retry_pending_typed_residual_extractions(
    *,
    conv: Any,
    dossier: ProofDossier,
    lean: LeanRunner,
    proof_state: ProofSearchState,
    deadline_monotonic: float,
    max_nodes: int,
    turn: int,
    target_node_ids: Optional[Sequence[str]] = None,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    trace_prefix: str = "",
) -> List[Dict[str, Any]]:
    """Retry verifier-only residual extraction before any tactic/provider work."""

    def retire_prior_route(parent: ProofStateNode, assembly_id: str) -> None:
        """Retire exactly one stale route and orphaned residual children."""

        exact_id = str(assembly_id or "")
        if not exact_id:
            return
        stale_child_ids: List[str] = []
        for group in parent.assembly_attempt_groups:
            if group.assembly_id != exact_id:
                continue
            stale_child_ids = list(group.child_node_ids or ())
            group.status = "obsolete"
            break
        for child_id in stale_child_ids:
            child = proof_state.nodes.get(child_id)
            if child is None or child.status in {"proved", "obsolete"}:
                continue
            still_live = any(
                other_parent.status
                not in {"proved", "obsolete", "failed", "rejected"}
                and any(
                    other_group.status not in {"proved", "obsolete", "blocked"}
                    and child_id in other_group.child_node_ids
                    for other_group in other_parent.assembly_attempt_groups
                )
                for other_parent in proof_state.nodes.values()
            )
            if not still_live:
                child.status = "obsolete"
                child.action = "residual_route_replaced"
                child.blocker = "typed residual route replaced under current context"
                child.priority = 0.0

    records: List[Dict[str, Any]] = []

    async def resume_lemma_dag_parent_stub_batch(
        *,
        parent: ProofStateNode,
        pending_record: Mapping[str, Any],
        spawned_node_ids: Sequence[str] = (),
        residual_goal_count: int = 0,
        rejected_reason: str = "",
        accepted_helper_name: str = "",
        status_out: Optional[Dict[str, Any]] = None,
    ) -> List[str]:
        origin = dict(pending_record.get("origin_metadata") or {})
        continuation = dict(origin.get("producer_continuation") or {})
        if str(continuation.get("kind") or "") != (
            "lemma_dag_parent_stub_batch"
        ):
            return []
        task_id = str(continuation.get("task_id") or "")
        task = proof_state.nodes.get(task_id)
        if task is None or task.kind != "decomposition_task":
            return []
        parent_stub_result_recorded = False
        if accepted_helper_name:
            _close_lemma_dag_task_with_parent_helper(
                proof_state=proof_state,
                task_id=task_id,
                parent_node_id=parent.node_id,
                helper_name=accepted_helper_name,
                source=str(continuation.get("source") or ""),
                phase=str(
                    continuation.get("phase")
                    or "proof_state_lemma_dag_helper"
                ),
                turn_index=_durable_nonnegative_int(
                    continuation.get("turn_index")
                ),
            )
            return []
        remaining_validation_variants = [
            str(item or "").strip()
            for item in list(
                continuation.get(
                    "remaining_parent_stub_validation_variants"
                )
                or ()
            )
            if str(item or "").strip()
        ]
        if rejected_reason and remaining_validation_variants:
            retry_continuation = dict(continuation)
            retry_continuation[
                "remaining_parent_stub_validation_variants"
            ] = []
            retried_nodes, retried_reason = (
                await _try_spawn_lemma_dag_parent_stub(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    task=task,
                    helper_name=str(continuation.get("helper_name") or ""),
                    statement=str(continuation.get("statement") or task.target),
                    proof_stub=remaining_validation_variants[0],
                    source=str(continuation.get("source") or ""),
                    phase=str(
                        continuation.get("phase")
                        or "proof_state_lemma_dag_helper"
                    ),
                    turn_index=_durable_nonnegative_int(
                        continuation.get("turn_index")
                    ),
                    timeout_s=_fully_funded_operation_timeout(
                        _typed_residual_operation_timeout(lean, 0.0),
                        deadline_monotonic,
                    ),
                    max_goals=max(
                        1,
                        _durable_nonnegative_int(
                            continuation.get("max_parent_stub_goals")
                        ),
                    ),
                    deadline_monotonic=deadline_monotonic,
                    producer_continuation=retry_continuation,
                    validation_variants=remaining_validation_variants,
                )
            )
            if str(retried_reason or "").endswith("_deferred"):
                # The next exact validation variant owns the parent's durable
                # verifier frame. Do not settle the paid helper batch.
                if status_out is not None:
                    deferred_reason = str(retried_reason or "")
                    status_out.update(
                        {
                            "retryable_infrastructure": True,
                            "retryable_timeout": bool(
                                "timeout" in deferred_reason
                                or "deadline" in deferred_reason
                            ),
                            "deadline_deferred": bool(
                                "deadline" in deferred_reason
                            ),
                            "error_kind": deferred_reason,
                            "verdict": deferred_reason,
                        }
                    )
                return []
            if retried_reason == "parent_stub_closed_goal":
                helper_block = str(
                    continuation.get("helper_block") or ""
                ).strip()
                if helper_block:
                    closed_continuation = dict(continuation)
                    closed_continuation.update(
                        {
                            "kind": "lemma_dag_parent_stub_closed",
                            "task_id": task_id,
                            "parent_node_id": parent.node_id,
                        }
                    )
                    closed_continuation.pop(
                        "remaining_parent_stub_validation_variants",
                        None,
                    )
                    stage_pending_helper_acceptance(
                        conv=conv,
                        dossier=dossier,
                        node=task,
                        helper_block=helper_block,
                        source=(
                            "lemma_dag:"
                            + str(continuation.get("source") or "")
                        ),
                        continuation=closed_continuation,
                    )
                return []
            spawned_node_ids = list(retried_nodes)
            residual_goal_count = len(spawned_node_ids)
            rejected_reason = "" if spawned_node_ids else str(retried_reason)
            parent_stub_result_recorded = True
        if spawned_node_ids:
            if not parent_stub_result_recorded:
                proof_state.record_lemma_dag_parent_stub_spawned(
                    task_id=task_id,
                    parent_node_id=parent.node_id,
                    helper_name=str(continuation.get("helper_name") or ""),
                    proof_stub=str(
                        pending_record.get("parent_proof_stub") or ""
                    ),
                    spawned_node_ids=list(spawned_node_ids),
                    residual_goal_count=int(residual_goal_count or 0),
                    phase=str(
                        continuation.get("phase")
                        or "proof_state_lemma_dag_helper"
                    ),
                    turn_index=_durable_nonnegative_int(
                        continuation.get("turn_index")
                    ),
                    source=str(continuation.get("source") or ""),
                )
        elif rejected_reason and not parent_stub_result_recorded:
            proof_state.record_lemma_dag_parent_stub_rejection(
                task_id=task_id,
                parent_node_id=parent.node_id,
                helper_name=str(continuation.get("helper_name") or ""),
                proof_stub=str(
                    pending_record.get("parent_proof_stub") or ""
                ),
                phase=str(
                    continuation.get("phase")
                    or "proof_state_lemma_dag_helper"
                ),
                turn_index=_durable_nonnegative_int(
                    continuation.get("turn_index")
                ),
                source=str(continuation.get("source") or ""),
                reason=str(rejected_reason),
            )
        proposed_count = (
            _durable_nonnegative_int(continuation.get("proposed_count"))
            + len(list(spawned_node_ids or ()))
        )
        accepted_count = _durable_nonnegative_int(
            continuation.get("accepted_count")
        )
        candidate_node_ids = [
            str(item)
            for item in list(
                continuation.get("candidate_node_ids") or ()
            )
            if str(item or "").strip()
        ]
        candidate_node_ids.extend(
            str(item)
            for item in list(spawned_node_ids or ())
            if str(item or "").strip()
        )
        remaining = [
            str(item or "").strip()
            for item in list(
                continuation.get("remaining_helper_blocks") or ()
            )
            if str(item or "").strip()
        ]
        if not remaining:
            proof_state.close_decomposition_task_from_lemma_dag(
                task_id=task_id,
                proposed_count=proposed_count,
                accepted_count=accepted_count,
                node_ids=candidate_node_ids,
            )
            return []
        suffix_status: Dict[str, Any] = {}
        suffix_records: List[Dict[str, Any]] = []
        accepted_helpers = await _try_proof_state_lemma_dag_helpers(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helpers=remaining,
            recorder=None,
            trace_prefix=trace_prefix,
            turn=turn,
            timeout_s=_fully_funded_operation_timeout(
                _typed_residual_operation_timeout(lean, 0.0),
                deadline_monotonic,
            ),
            deadline_monotonic=deadline_monotonic,
            proof_cache=proof_cache,
            target_task_id=task_id,
            max_parent_stub_goals=max(
                1,
                _durable_nonnegative_int(
                    continuation.get("max_parent_stub_goals")
                ),
            ),
            initial_proposed_count=proposed_count,
            initial_accepted_count=accepted_count,
            initial_candidate_node_ids=candidate_node_ids,
            initial_renamed_collisions=dict(
                continuation.get("renamed_collisions") or {}
            ),
            status_out=suffix_status,
            records_out=suffix_records,
        )
        records.extend(suffix_records)
        return accepted_helpers

    def settle_residual_producer(
        parent: ProofStateNode,
        pending_record: Mapping[str, Any],
        *,
        receipt_status: str,
    ) -> None:
        """Settle the paid producer that created a residual verifier WAL."""

        origin = dict(pending_record.get("origin_metadata") or {})
        kind = str(origin.get("kind") or "")
        if kind == "decl_application":
            decl_name = str(origin.get("decl_name") or "").strip()
            if decl_name:
                tried = list(parent.decl_application_tried_decl_names or [])
                if decl_name not in tried:
                    tried.append(decl_name)
                    del tried[:-256]
                    parent.decl_application_tried_decl_names = tried
                prefix = f"{decl_name}\n"
                parent.decl_application_retry_keys = [
                    key
                    for key in list(parent.decl_application_retry_keys or ())
                    if not str(key or "").startswith(prefix)
                ]
                parent.decl_application_signature = str(
                    origin.get("decl_application_signature") or ""
                )
                parent.decl_application_attempts += 1
                parent.close_attempts += 1
            return
        if kind == "tactic_residual":
            proof_state.record_tactic_result(
                node_id=parent.node_id,
                ok=False,
                attempt_count=max(
                    1,
                    _durable_nonnegative_int(origin.get("attempt_count")),
                ),
                exit_reason=str(receipt_status or "typed_residual_settled"),
                terminal_context_key=str(
                    origin.get("terminal_context_key") or ""
                ),
                terminal_for_context=False,
            )
    retry_limit = max(1, int(max_nodes or 1))
    exact_target_ids = {
        str(item or "").strip()
        for item in list(target_node_ids or ())
        if str(item or "").strip()
    }
    candidate_nodes = [
        node
        for node in proof_state.nodes.values()
        if not exact_target_ids or node.node_id in exact_target_ids
    ]
    for node in candidate_nodes:
        pending = dict(
            getattr(node, "pending_residual_goal_extraction", {}) or {}
        )
        if not pending:
            continue
        pending_stub = str(pending.get("parent_proof_stub") or "")
        pending_status = proof_state.pending_residual_goal_extraction_status(node)
        if pending_status not in {"pending", "rematerialize"}:
            proof_state.clear_pending_residual_goal_extraction(node)
            proof_state.record_transition(
                node_id=node.node_id,
                source="typed_residual_retry",
                error_type="residual_extraction_context_stale",
                action=node.action,
                blocker="pending residual extraction context changed",
                phase="proof_state_typed_residual_retry",
                turn_index=turn,
                payload={
                    "request_context_hash": str(
                        pending.get("request_context_hash") or ""
                    )
                },
            )
            records.append(
                {
                    "phase": "proof_state_typed_residual_retry",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "verdict": "residual_extraction_record_invalid",
                }
            )
            continue
        current_preamble = _proof_state_residual_preamble(conv)
        current_lemmas = _proof_state_residual_lemmas(
            conv,
            _proof_state_verified_helper_blocks(dossier),
        )
        current_request_hash, current_context_hash = (
            _typed_residual_request_hashes(
                lean=lean,
                proof_state=proof_state,
                parent_node=node,
                parent_proof_stub=pending_stub,
                source=str(pending.get("source") or ""),
                preamble=current_preamble,
                lemmas=current_lemmas,
                max_goals=int(pending.get("max_goals") or 0),
            )
        )

        def forget_deferred_request() -> None:
            deferred_retries = dict(
                getattr(
                    node,
                    "residual_attestation_deferred_request_retries",
                    {},
                )
                or {}
            )
            deferred_retries.pop(current_request_hash, None)
            node.residual_attestation_deferred_request_retries = (
                deferred_retries
            )
            if (
                str(
                    getattr(
                        node,
                        "residual_attestation_last_deferred_request_hash",
                        "",
                    )
                    or ""
                )
                == current_request_hash
            ):
                node.residual_attestation_last_deferred_request_hash = ""

        if (
            str(pending.get("request_context_hash") or "")
            != current_request_hash
            or str(pending.get("elaboration_context_hash") or "")
            != current_context_hash
            or str(pending.get("statement_environment_hash") or "")
            != proof_state.statement_environment_hash
        ):
            prior_retry_key = str(pending.get("verifier_retry_key") or "").strip()
            # The proof route remains valuable, but its replay environment is
            # no longer the one assembly will use. Rematerialize its exact
            # extraction context without classifying or charging a failure.
            rematerialized_action_metadata = dict(
                pending.get("action_metadata") or {}
            )
            rematerialized_action_metadata.pop(
                "typed_residual_closed_pending_acceptance",
                None,
            )
            rematerialized_action_metadata.pop(
                "acceptance_attempt_count",
                None,
            )
            proof_state.record_pending_residual_goal_extraction(
                parent_node_id=node.node_id,
                source=str(pending.get("source") or ""),
                parent_proof_stub=pending_stub,
                max_goals=int(pending.get("max_goals") or 0),
                request_context_hash=current_request_hash,
                elaboration_context_hash=current_context_hash,
                origin_metadata=dict(pending.get("origin_metadata") or {}),
                action_metadata=rematerialized_action_metadata,
                # A changed exact request/context gets a fresh immediate
                # verifier replay. Backoff belongs to the prior identity.
                retry_count=0,
                verifier_retry_key=_verifier_retry_key(
                    stage="typed_residual_extraction",
                    request_hash=current_request_hash,
                    context_hash=current_context_hash,
                    verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
                ),
            )
            pending = dict(node.pending_residual_goal_extraction)
            if prior_retry_key and prior_retry_key != str(
                pending.get("verifier_retry_key") or ""
            ):
                proof_state.clear_verifier_retry_state(node, prior_retry_key)
            records.append(
                {
                    "phase": "proof_state_typed_residual_retry",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "verdict": "residual_extraction_context_rematerialized",
                }
            )
        action_metadata = dict(pending.get("action_metadata") or {})
        active_retry_key = str(
            pending.get("verifier_retry_key") or ""
        ).strip()
        if (
            not bool(
                action_metadata.get("typed_residual_closed_pending_acceptance")
            )
            and active_retry_key
            and proof_state.verifier_retry_status(node, active_retry_key)
            == "cooling"
        ):
            # A cooldown is a scheduler wakeup condition, not an executor
            # outcome. In particular, do not let a child-closure dispatch for
            # unrelated work repeatedly manufacture cooldown/infrastructure
            # deferrals for this already durable verifier frame.
            continue
        continuation_helpers: List[str] = []
        continuation_status: Dict[str, Any] = {}
        reattestation = bool(action_metadata.get("reattestation"))
        prior_assembly_id = str(
            action_metadata.get("prior_assembly_id") or ""
        )
        if bool(
            action_metadata.get("typed_residual_closed_pending_acceptance")
        ):
            acceptance_retry_key = _verifier_retry_key(
                stage="typed_residual_helper_acceptance",
                request_hash=current_request_hash,
                context_hash=current_context_hash,
                verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
            )
            if (
                proof_state.verifier_retry_status(node, acceptance_retry_key)
                == "cooling"
            ):
                records.append(
                    {
                        "phase": "proof_state_typed_residual_retry",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "typed_residual_goal_count": 0,
                        "spawned_child_nodes": [],
                        "retryable_infrastructure": True,
                        "verdict": "residual_closed_helper_acceptance_cooling",
                    }
                )
                continue
            helper_name = proof_state.helper_name_for_node(node, dossier)
            proof_code = _proof_from_closed_typed_residual_stub(pending_stub)
            if not proof_code:
                forget_deferred_request()
                proof_state.clear_pending_residual_goal_extraction(node)
                records.append(
                    {
                        "phase": "proof_state_typed_residual_retry",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "typed_residual_goal_count": 0,
                        "spawned_child_nodes": [],
                        "error_kind": "empty_closed_residual_proof",
                        "verdict": "residual_closed_helper_rejected",
                    }
                )
                continue
            helper_block = _proof_state_helper_block(
                helper_name,
                node.target,
                proof_code,
            )
            acceptance_status: Dict[str, Any] = {}
            operation_timeout = _fully_funded_operation_timeout(
                _typed_residual_operation_timeout(lean, 0.0),
                deadline_monotonic,
            )
            accepted = False
            if operation_timeout > 0.0:
                try:
                    accepted = await _accept_proof_state_helper(
                        lean=lean,
                        conv=conv,
                        dossier=dossier,
                        helper_block=helper_block,
                        phase="proof_state_typed_residual_closed_acceptance",
                        turn_index=turn,
                        timeout_s=operation_timeout,
                        proof_state=proof_state,
                        status_out=acceptance_status,
                        target_statement=node.target,
                        deadline_monotonic=deadline_monotonic,
                    )
                except asyncio.CancelledError:
                    raise
                except Exception as exc:
                    acceptance_status.update(
                        {
                            "status": "retryable_error",
                            "error_kind": type(exc).__name__,
                            "error": str(exc)[:240],
                        }
                    )
            else:
                acceptance_status.update(
                    {
                        "status": "retryable_error",
                        "error_kind": "enclosing_deadline_deferred",
                    }
                )
            accepted_helper_name = str(
                acceptance_status.get("accepted_helper_name")
                or helper_name
            ).strip()
            if accepted:
                proof_state.clear_verifier_retry_state(
                    node,
                    acceptance_retry_key,
                )
                forget_deferred_request()
                proof_state.clear_pending_residual_goal_extraction(node)
                if reattestation:
                    retire_prior_route(node, prior_assembly_id)
                if node.node_id == proof_state.root_node_id:
                    node.action = "prove_or_assemble"
                    node.blocker = (
                        "closed residual stub accepted as an exact root helper; "
                        "root finalization pending"
                    )
                    node.priority = proof_state._priority(node)
                else:
                    proof_state.record_tactic_result(
                        node_id=node.node_id,
                        ok=True,
                        attempt_count=0,
                        exit_reason="closed_residual_stub_accepted",
                        helper_name=accepted_helper_name,
                    )
                continuation_helpers = (
                    await resume_lemma_dag_parent_stub_batch(
                        parent=node,
                        pending_record=pending,
                        accepted_helper_name=accepted_helper_name,
                    )
                )
                settle_residual_producer(
                    node,
                    pending,
                    receipt_status="residual_attestation_closed_goal",
                )
                records.append(
                    {
                        "phase": "proof_state_typed_residual_retry",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "typed_residual_goal_count": 0,
                        "spawned_child_nodes": [],
                        "helper_name": accepted_helper_name,
                        "accepted_helpers": list(continuation_helpers),
                        "verdict": "residual_closed_helper_accepted",
                    }
                )
                if len(records) >= retry_limit:
                    break
                continue
            error_kind = str(
                acceptance_status.get("error_kind") or ""
            ).strip()
            retryable_acceptance = bool(
                str(acceptance_status.get("status") or "")
                in {"retryable_error", "cancelled"}
                or _decl_application_failure_is_retryable(error_kind)
            )
            if retryable_acceptance:
                attempted = bool(acceptance_status.get("lean_attempted", False))
                failure_fingerprint = hashlib.sha256(
                    json.dumps(
                        {
                            "stage": "typed_residual_helper_acceptance",
                            "kind": error_kind or "retryable_error",
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest()
                retry_record = (
                    proof_state.record_verifier_retry_failure(
                        node,
                        retry_key=acceptance_retry_key,
                        stage="typed_residual_helper_acceptance",
                        request_hash=current_request_hash,
                        context_hash=current_context_hash,
                        verifier_generation=LEAN_RESIDUAL_VERIFIER_GENERATION,
                        failure_kind=error_kind or "retryable_error",
                        failure_fingerprint=failure_fingerprint,
                    )
                    if attempted
                    else {}
                )
                retained = dict(node.pending_residual_goal_extraction or {})
                retained_action = dict(retained.get("action_metadata") or {})
                retained_action["typed_residual_closed_pending_acceptance"] = True
                retained_action["acceptance_attempt_count"] = max(
                    0,
                    _durable_nonnegative_int(
                        retained_action.get("acceptance_attempt_count", 0)
                    ),
                ) + int(attempted)
                retained["action_metadata"] = retained_action
                retained["retry_count"] = max(
                    0,
                    _durable_nonnegative_int(retained.get("retry_count", 0)),
                ) + int(attempted)
                retained["verifier_retry_key"] = acceptance_retry_key
                retained["verifier_failure"] = {
                    "attempted": attempted,
                    "failure_kind": error_kind[:160],
                    "failure_fingerprint": failure_fingerprint,
                    "retry_after_epoch_s": float(
                        retry_record.get("retry_after_epoch_s") or 0.0
                    ),
                    "consecutive_failure_count": int(
                        retry_record.get("consecutive_failure_count") or 0
                    ),
                }
                node.pending_residual_goal_extraction = retained
                records.append(
                    {
                        "phase": "proof_state_typed_residual_retry",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "typed_residual_goal_count": 0,
                        "spawned_child_nodes": [],
                        "retryable_infrastructure": True,
                        "error_kind": error_kind,
                        "verdict": (
                            "residual_closed_helper_acceptance_deferred"
                        ),
                    }
                )
                break
            forget_deferred_request()
            proof_state.clear_verifier_retry_state(node, acceptance_retry_key)
            proof_state.clear_pending_residual_goal_extraction(node)
            if reattestation:
                retire_prior_route(node, prior_assembly_id)
            node.action = "prove"
            node.blocker = (
                "closed residual stub failed normal answer-safe helper acceptance"
            )
            node.priority = proof_state._priority(node)
            settle_residual_producer(
                node,
                pending,
                receipt_status="residual_closed_helper_rejected",
            )
            records.append(
                {
                    "phase": "proof_state_typed_residual_retry",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "typed_residual_goal_count": 0,
                    "spawned_child_nodes": [],
                    "error_kind": error_kind,
                    "verdict": "residual_closed_helper_rejected",
                }
            )
            if len(records) >= retry_limit:
                break
            continue
        continuation_helpers = []
        spawned, goal_count, status = await _extract_and_spawn_typed_residual_goals(
            lean=lean,
            proof_state=proof_state,
            parent_node=node,
            parent_proof_stub=pending_stub,
            source=str(pending.get("source") or ""),
            preamble=current_preamble,
            lemmas=current_lemmas,
            timeout_s=0.0,
            max_goals=int(pending.get("max_goals") or 0),
            deadline_monotonic=deadline_monotonic,
            origin_metadata=dict(pending.get("origin_metadata") or {}),
            action_metadata=dict(pending.get("action_metadata") or {}),
        )
        node = proof_state.nodes.get(node.node_id, node)
        if status == "residual_attestation_admitted" and spawned:
            forget_deferred_request()
            if reattestation:
                retire_prior_route(node, prior_assembly_id)
            node.action = "assemble_from_children"
            node.blocker = f"typed residual retry admitted {goal_count} subgoal(s)"
            node.priority = proof_state._priority(node)
            node.residual_attestation_rejected_request_hashes = [
                item
                for item in node.residual_attestation_rejected_request_hashes
                if item != current_request_hash
            ]
            continuation_helpers = await resume_lemma_dag_parent_stub_batch(
                parent=node,
                pending_record=pending,
                spawned_node_ids=spawned,
                residual_goal_count=goal_count,
            )
            settle_residual_producer(
                node,
                pending,
                receipt_status=status,
            )
        elif status == "residual_attestation_closed_goal":
            forget_deferred_request()
            staged = stage_closed_typed_residual_acceptance(
                conv=conv,
                dossier=dossier,
                lean=lean,
                proof_state=proof_state,
                parent_node=node,
                source=str(pending.get("source") or ""),
                parent_proof_stub=pending_stub,
                max_goals=int(pending.get("max_goals") or 0),
                origin_metadata=dict(pending.get("origin_metadata") or {}),
                action_metadata=action_metadata,
            )
            if staged:
                node.action = "prove"
                node.blocker = (
                    "closed residual stub awaiting normal answer-safe acceptance"
                )
                node.priority = proof_state._priority(node)
        elif not status.endswith("_deferred"):
            forget_deferred_request()
            # Definitive rejection retires only this exact helper/preamble
            # context. A later context change can schedule re-attestation
            # again, while an unchanged context cannot spin forever.
            if reattestation:
                rejected = list(
                    getattr(
                        node,
                        "residual_attestation_rejected_request_hashes",
                        [],
                    )
                    or []
                )
                if current_request_hash not in rejected:
                    rejected.append(current_request_hash)
                node.residual_attestation_rejected_request_hashes = rejected[-256:]
                for group in node.assembly_attempt_groups:
                    if group.assembly_id == prior_assembly_id:
                        group.status = "blocked"
                        break
            settle_residual_producer(
                node,
                pending,
                receipt_status=status,
            )
            continuation_helpers = await resume_lemma_dag_parent_stub_batch(
                parent=node,
                pending_record=pending,
                rejected_reason=status,
                status_out=continuation_status,
            )
        elif status.endswith("_deferred") and reattestation:
            # Preserve retry accounting for this exact request, then yield the
            # parent's singular durable frame to the next stale route. This is
            # a fair verifier rotation, not a mathematical rejection. The
            # durable last-request cursor resumes at the following live route
            # and wraps only after every other route receives a turn.
            deferred_pending = dict(
                getattr(node, "pending_residual_goal_extraction", {}) or {}
            )
            deferred_retries = dict(
                getattr(
                    node,
                    "residual_attestation_deferred_request_retries",
                    {},
                )
                or {}
            )
            deferred_retries[current_request_hash] = max(
                _durable_nonnegative_int(
                    deferred_retries.get(current_request_hash, 0)
                ),
                _durable_nonnegative_int(deferred_pending.get("retry_count", 0)),
                1,
            )
            node.residual_attestation_deferred_request_retries = dict(
                list(deferred_retries.items())[-256:]
            )
            node.residual_attestation_last_deferred_request_hash = (
                current_request_hash
            )
            # An attempted verifier failure may have just made this exact
            # route the last cooling route. Keep its paid frame until the
            # scheduler either installs a ready alternative or leaves it as
            # the durable checkpoint/wakeup anchor. Non-cooling deferrals
            # (for example an unfunded deadline) still yield the slot so fair
            # rotation can proceed.
            deferred_retry_key = str(
                deferred_pending.get("verifier_retry_key") or ""
            ).strip()
            if (
                not deferred_retry_key
                or proof_state.verifier_retry_status(
                    node,
                    deferred_retry_key,
                )
                != "cooling"
            ):
                proof_state.clear_pending_residual_goal_extraction(node)
            ensure_current_typed_residual_attestation_retries(
                conv=conv,
                dossier=dossier,
                lean=lean,
                proof_state=proof_state,
            )
        effective_status = str(continuation_status.get("verdict") or status)
        continuation_retryable = bool(
            continuation_status.get("retryable_infrastructure", False)
        )
        retryable_timeout = bool(
            continuation_status.get("retryable_timeout", False)
            or (
                effective_status.endswith("_deferred")
                and (
                    "timeout" in effective_status
                    or "deadline" in effective_status
                )
            )
        )
        deadline_deferred = bool(
            continuation_status.get("deadline_deferred", False)
            or (
                effective_status.endswith("_deferred")
                and "deadline" in effective_status
            )
        )
        records.append(
            {
                "phase": "proof_state_typed_residual_retry",
                "turn_in_phase": turn,
                "node_id": node.node_id,
                "typed_residual_goal_count": goal_count,
                "spawned_child_nodes": list(spawned),
                "retryable_infrastructure": bool(
                    status.endswith("_deferred") or continuation_retryable
                ),
                "retryable_timeout": retryable_timeout,
                "deadline_deferred": deadline_deferred,
                "error_kind": str(
                    continuation_status.get("error_kind")
                    or (
                        effective_status
                        if effective_status.endswith("_deferred")
                        else ""
                    )
                ),
                "accepted_helpers": list(continuation_helpers),
                "verdict": effective_status,
            }
        )
        if status.endswith("_deferred") or continuation_retryable:
            break
        if len(records) >= retry_limit:
            break
    return records


def proof_state_decl_application_context_hash(
    conv: Any,
    dossier: ProofDossier,
) -> str:
    """Hash the exact preamble and helpers used by declaration application."""

    hasher = hashlib.sha256()
    hasher.update(
        str(_proof_state_residual_preamble(conv) or "").encode(
            "utf-8", "replace"
        )
    )
    for block in _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    ):
        hasher.update(b"\0")
        hasher.update(str(block or "").encode("utf-8", "replace"))
    return hasher.hexdigest()


def _proof_state_remaining_goals_from_parsed(parsed: Any) -> List[Dict[str, Any]]:
    goals: List[Dict[str, Any]] = []
    for goal in list(getattr(parsed, "remaining_goals", []) or []):
        target = str(getattr(goal, "target", "") or "").strip()
        if not target:
            continue
        hypotheses = [
            str(item)
            for item in list(getattr(goal, "hypotheses", []) or [])
            if str(item or "").strip()
        ]
        goals.append({"target": target, "hypotheses": hypotheses})
    return goals


def _proof_state_goal_hash(
    proof_state: ProofSearchState,
    goal: Any,
) -> str:
    if not isinstance(goal, dict):
        return ""
    target = proof_state._normalize_goal_text(goal.get("target"))
    raw_context = (
        goal.get("hypotheses")
        or goal.get("context")
        or goal.get("local_context")
        or []
    )
    if isinstance(raw_context, str):
        raw_context = [line for line in raw_context.splitlines() if line.strip()]
    context = [
        proof_state._normalize_hypothesis(item)
        for item in list(raw_context or [])
        if str(item or "").strip()
    ]
    if not target:
        return ""
    return proof_state._goal_signature(
        target,
        context,
        source_failure="residual_stub_validation",
    ).normalized_statement_hash


def _lemma_dag_parent_stub_candidate_sources(
    proof_state: Optional[ProofSearchState],
    helpers: Sequence[str],
) -> List[str]:
    """Return helper declarations shaped like parent/root partial stubs."""

    if proof_state is None:
        return []
    root_node_id = str(getattr(proof_state, "root_node_id", "") or "").strip()
    nodes = getattr(proof_state, "nodes", None)
    if not root_node_id or not hasattr(nodes, "get"):
        return []
    root = nodes.get(root_node_id)
    if root is None:
        return []
    root_key = canonicalize_lean_statement_for_identity(root.target)
    if not root_key:
        return []
    out: List[str] = []
    seen: Set[str] = set()
    for helper in helpers or ():
        source = str(helper or "").strip()
        if not source or source in seen:
            continue
        statement = helper_decl_statement(source)
        body = helper_decl_body(source)
        if not statement or not body:
            continue
        if _is_sorry_stub_body(source):
            continue
        if canonicalize_lean_statement_for_identity(statement) != root_key:
            continue
        seen.add(source)
        out.append(source)
    return out


def _helper_dependency_closure_sources(
    seeds: Sequence[str],
    helpers: Sequence[str],
) -> List[str]:
    helper_list = [
        str(helper or "").strip()
        for helper in helpers or ()
        if str(helper or "").strip()
    ]
    selected: List[str] = []
    for source in list(seeds or ()):
        text = str(source or "").strip()
        if text and text not in selected:
            selected.append(text)
    if not selected:
        return []
    names = [
        name
        for name in (helper_decl_name(helper) for helper in helper_list)
        if name
    ]
    changed = True
    while changed:
        changed = False
        needed: Set[str] = set()
        for source in selected:
            name = helper_decl_name(source)
            needed.update(_helper_referenced_names(source, names, skip=name))
        for helper in helper_list:
            name = helper_decl_name(helper)
            if not name or name not in needed:
                continue
            providers = [
                candidate
                for candidate in helper_list
                if helper_decl_name(candidate) == name
            ]
            for provider in reversed(providers or [helper]):
                if provider in selected:
                    continue
                selected.append(provider)
                changed = True
    return _order_helper_sources_dependency_first(selected)


def _order_helper_sources_dependency_first(sources: Sequence[str]) -> List[str]:
    source_list: List[str] = []
    for source in sources or ():
        text = str(source or "").strip()
        if text and text not in source_list:
            source_list.append(text)
    names = [
        name
        for name in (helper_decl_name(source) for source in source_list)
        if name
    ]
    name_to_sources: Dict[str, List[str]] = {}
    for source in source_list:
        name = helper_decl_name(source)
        if not name:
            continue
        name_to_sources.setdefault(name, []).append(source)
    ordered: List[str] = []
    emitted: Set[str] = set()
    visiting: Set[str] = set()

    def emit(source: str) -> None:
        if source in emitted:
            return
        if source in visiting:
            if source not in emitted:
                emitted.add(source)
                ordered.append(source)
            return
        visiting.add(source)
        name = helper_decl_name(source)
        deps = _helper_referenced_names(source, names, skip=name)
        for dep in sorted(deps):
            for provider in name_to_sources.get(dep, []):
                emit(provider)
        visiting.remove(source)
        if source not in emitted:
            emitted.add(source)
            ordered.append(source)

    for source in source_list:
        emit(source)
    return ordered


def _closed_false_residual_goal(goal: Dict[str, Any]) -> bool:
    target = " ".join(str(goal.get("target") or "").split()).strip()
    for _ in range(8):
        if len(target) >= 2 and target[0] == "(" and target[-1] == ")":
            target = target[1:-1].strip()
            continue
        break
    hypotheses = (
        goal.get("hypotheses")
        or goal.get("context")
        or goal.get("local_context")
        or []
    )
    if isinstance(hypotheses, str):
        hypotheses = [line for line in hypotheses.splitlines() if line.strip()]
    return target in {"False", "false"} and not [
        item for item in list(hypotheses or []) if str(item or "").strip()
    ]


def _parent_stub_validation_variants(statement: str, proof_stub: str) -> List[str]:
    stub = str(proof_stub or "").strip()
    if not stub:
        return []
    variants: List[str] = [stub]
    bound_names = [
        name
        for name in lean_statement_bound_names(statement)
        if name and re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*$", name)
    ]
    if not bound_names:
        return variants
    lines = [line.rstrip() for line in stub.splitlines()]
    if lines and lines[0].strip() == "by":
        body_lines = lines[1:]
    elif stub.startswith("by "):
        body_lines = [stub[3:].strip()]
    else:
        body_lines = lines
    prefixed_lines = ["by"]
    prefixed_lines.extend(f"  intro {name}" for name in bound_names)
    prefixed_lines.extend(
        ("  " + line.strip()) if line.strip() else ""
        for line in body_lines
    )
    prefixed = "\n".join(prefixed_lines).strip()
    if prefixed and prefixed not in variants:
        variants.append(prefixed)
    return variants


def _verified_helper_replacement_context(
    dossier: ProofDossier,
    replacing_name: str,
) -> Tuple[List[str], Set[str]]:
    replacement_name = str(replacing_name or "").strip()
    helpers = [
        (name, str(getattr(helper, "source", "") or "").strip())
        for name, helper in getattr(dossier, "verified_helpers", {}).items()
        if str(name or "").strip()
        and str(getattr(helper, "source", "") or "").strip()
    ]
    helper_names = [name for name, _source in helpers if name]
    stale_dependents: Set[str] = set()
    changed = True
    while changed:
        changed = False
        blocked_names = {replacement_name, *stale_dependents}
        for name, source in helpers:
            if not name or name in blocked_names:
                continue
            refs = _helper_referenced_names(source, helper_names, skip=name)
            if refs.intersection(blocked_names):
                stale_dependents.add(name)
                changed = True
    context = [
        source
        for name, source in helpers
        if name != replacement_name and name not in stale_dependents
    ]
    return context, stale_dependents


async def _validate_proof_state_tactic_residual_stub(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    partial_stub: str,
    claimed_goals: Sequence[Any],
    timeout_s: float,
    max_goals: int,
    deadline_monotonic: float = 0.0,
) -> Tuple[bool, List[Dict[str, Any]], str]:
    """Freshly verify that a tactic prefix leaves exactly the claimed goals."""

    stub = str(partial_stub or "").strip()
    if not stub:
        return False, [], "empty_partial_stub"
    claimed = [goal for goal in list(claimed_goals or []) if isinstance(goal, dict)]
    if not claimed:
        return False, [], "missing_claimed_goals"
    if len(claimed) > max(0, int(max_goals or 0)):
        return False, [], "too_many_residual_goals"
    timeout = _fully_funded_operation_timeout(timeout_s, deadline_monotonic)
    if timeout <= 0.0:
        return False, [], (
            "residual_stub_deadline_deferred"
            if float(timeout_s or 0.0) > 0.0
            and float(deadline_monotonic or 0.0) > 0.0
            else "residual_stub_budget_disabled"
        )
    async def run_check() -> Any:
        try:
            return await lean.check(
                node.target,
                stub,
                _proof_state_residual_lemmas(
                    conv, _proof_state_verified_helper_blocks(dossier)
                ),
                preamble_override=_proof_state_residual_preamble(conv),
                timeout_s=timeout,
                check_kind="proof_state_residual_stub",
            )
        except TypeError:
            try:
                return await lean.check(
                    node.target,
                    stub,
                    _proof_state_residual_lemmas(conv, _proof_state_verified_helper_blocks(dossier)),
                    preamble_override=_proof_state_residual_preamble(conv),
                    timeout_s=timeout,
                )
            except TypeError:
                return await lean.check(
                    node.target,
                    stub,
                    _proof_state_residual_lemmas(conv, _proof_state_verified_helper_blocks(dossier)),
                    preamble_override=_proof_state_residual_preamble(conv),
                )
    try:
        result = await _await_serialized_lean_operation(
            lean,
            run_check,
            timeout_s=timeout,
            deadline_monotonic=deadline_monotonic,
            operation_label="proof_state_residual_stub",
        )
    except _LeanOperationDeadline:
        return False, [], (
            "residual_stub_deadline_exhausted"
            if deadline_monotonic > 0.0
            and time.monotonic() >= float(deadline_monotonic)
            else "residual_stub_timeout"
        )
    except Exception as exc:
        return False, [], f"{type(exc).__name__}: {exc}"

    parsed = getattr(result, "parsed", None)
    if bool(getattr(result, "ok", False)):
        return False, [], "partial_stub_closed_goal"
    if canonical_error_type(parsed) != "unsolved_goals":
        return False, [], canonical_error_type(parsed) or "not_unsolved_goals"
    actual = _proof_state_remaining_goals_from_parsed(parsed)
    if len(actual) != len(claimed):
        return False, actual, "residual_goal_count_mismatch"
    actual_hashes = [_proof_state_goal_hash(proof_state, goal) for goal in actual]
    claimed_hashes = [_proof_state_goal_hash(proof_state, goal) for goal in claimed]
    if actual_hashes != claimed_hashes or any(not item for item in actual_hashes):
        return False, actual, "residual_goal_shape_mismatch"
    return True, actual, "validated"


async def _try_spawn_lemma_dag_parent_stub(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    task: ProofStateNode,
    helper_name: str,
    statement: str,
    proof_stub: str,
    source: str,
    phase: str,
    turn_index: int,
    timeout_s: float,
    max_goals: int,
    deadline_monotonic: float = 0.0,
    producer_continuation: Optional[Mapping[str, Any]] = None,
    validation_variants: Optional[Sequence[str]] = None,
) -> Tuple[List[str], str]:
    """Turn a parent-shaped lemma-DAG theorem body into assembly residuals.

    This is the safe bridge from LLM decomposition text to executable DAG
    state: Lean must confirm the body reduces the parent/root statement to
    residual goals, and only then do we call ``spawn_remaining_goals``.
    """

    parent = proof_state.nodes.get(task.parent_node_id) or proof_state.nodes.get(
        proof_state.root_node_id
    )
    if parent is None:
        return [], "missing_parent_node"
    parent_key = canonicalize_lean_statement_for_identity(parent.target)
    task_key = canonicalize_lean_statement_for_identity(task.target)
    statement_key = canonicalize_lean_statement_for_identity(statement)
    if not statement_key or statement_key not in {parent_key, task_key}:
        return [], "not_parent_target"

    stub = str(proof_stub or "").strip()
    if not stub:
        return [], "missing_parent_stub"
    if _is_sorry_stub_body(f"theorem __mini_parent_stub__ : {statement} := {stub}"):
        return [], "sorry_stub_parent"

    residual_source = f"lemma_dag_parent_stub:{helper_name or task.node_id}"
    last_reason = "parent_stub_residual_lean_rejected"
    last_stub = stub
    helper_blocks = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    variants = [
        str(item or "").strip()
        for item in (
            list(validation_variants)
            if validation_variants is not None
            else _parent_stub_validation_variants(statement, stub)
        )
        if str(item or "").strip()
    ]
    variants = list(dict.fromkeys(variants))
    for variant_index, candidate_stub in enumerate(variants):
        last_stub = candidate_stub
        origin_metadata: Dict[str, Any] = {
            "kind": "lemma_dag_parent_stub",
            "task_id": task.node_id,
            "helper_name": helper_name,
            "phase": phase,
            "turn_index": turn_index,
            "source": source,
        }
        if producer_continuation:
            exact_continuation = dict(producer_continuation)
            exact_continuation[
                "remaining_parent_stub_validation_variants"
            ] = list(variants[variant_index + 1 :])
            origin_metadata["producer_continuation"] = exact_continuation
        spawned, goal_count, receipt_status = (
            await _extract_and_spawn_typed_residual_goals(
                lean=lean,
                proof_state=proof_state,
                parent_node=parent,
                parent_proof_stub=candidate_stub,
                source=residual_source,
                preamble=_proof_state_residual_preamble(conv),
                lemmas=helper_blocks,
                timeout_s=timeout_s,
                max_goals=max_goals,
                deadline_monotonic=deadline_monotonic,
                origin_metadata=origin_metadata,
            )
        )
        parent = proof_state.nodes.get(parent.node_id, parent)
        if receipt_status == "residual_attestation_closed_goal":
            return [], "parent_stub_closed_goal"
        if receipt_status.endswith("_deferred"):
            # A timeout or unavailable Lean environment says nothing about the
            # mathematics. Preserve the route without banking a rejection.
            return [], f"parent_stub_{receipt_status}"
        if receipt_status == "residual_attestation_goal_cap_exceeded":
            last_reason = "parent_stub_residual_goal_cap_exceeded"
            continue
        if receipt_status == "residual_attestation_admitted" and spawned:
            spawned_unique = list(dict.fromkeys(spawned))
            proof_state.record_lemma_dag_parent_stub_spawned(
                task_id=task.node_id,
                parent_node_id=parent.node_id,
                helper_name=helper_name,
                proof_stub=candidate_stub,
                spawned_node_ids=spawned_unique,
                residual_goal_count=goal_count,
                phase=phase,
                turn_index=turn_index,
                source=source,
            )
            return spawned_unique, "spawned"
        last_reason = f"parent_stub_{receipt_status}"

    proof_state.record_lemma_dag_parent_stub_rejection(
        task_id=task.node_id,
        parent_node_id=parent.node_id,
        helper_name=helper_name,
        proof_stub=last_stub,
        phase=phase,
        turn_index=turn_index,
        source=source,
        reason=last_reason,
    )
    return [], last_reason


def _close_lemma_dag_task_with_parent_helper(
    *,
    proof_state: ProofSearchState,
    task_id: str,
    parent_node_id: str,
    helper_name: str,
    source: str,
    phase: str,
    turn_index: int,
) -> bool:
    """Close a decomposition whose parent stub was verified outright."""

    task = proof_state.nodes.get(str(task_id or ""))
    if task is None or task.kind != "decomposition_task":
        return False
    if task.status not in {"open", "blocked"}:
        return task.status == "proved"
    clean_helper_name = str(helper_name or "").strip()
    task.status = "proved"
    task.action = "llm_lemma_dag_parent_stub_closed"
    task.blocker = (
        "Lean verified a lemma-DAG parent proof without residual obligations"
    )
    task.proved_helper_name = clean_helper_name
    task.successful_family = "llm_lemma_dag"
    task.priority = 0.0
    proof_state._clear_terminal_node_verifier_work(task)  # noqa: SLF001
    proof_state.record_transition(
        node_id=task.node_id,
        source="llm_lemma_dag",
        error_type="llm_lemma_dag_parent_stub_closed",
        action=task.action,
        blocker=task.blocker,
        phase=phase,
        turn_index=turn_index,
        payload={
            "helper_name": clean_helper_name,
            "parent_node_id": str(parent_node_id or ""),
            "source": str(source or ""),
        },
    )
    proof_state._refresh_priorities_for_neighbors(task.node_id)  # noqa: SLF001
    return True


def _cache_seed_helper_registry_identity(
    dossier: ProofDossier,
) -> Tuple[Tuple[str, str], ...]:
    """Bind exact authoritative helper names and sources, independent of rendering."""

    return tuple(
        sorted(
            (
                str(name or "").strip(),
                str(getattr(helper, "source_hash", "") or "").strip(),
            )
            for name, helper in dict(
                getattr(dossier, "verified_helpers", {}) or {}
            ).items()
            if str(name or "").strip()
        )
    )


def _cache_seed_visible_base_identity(
    dossier: ProofDossier,
    *,
    excluded_helper_names: Iterable[str] = (),
) -> Tuple[Tuple[str, str], ...]:
    """Normalize raw/alias rendering while retaining visibility changes."""

    excluded = {
        str(name or "").strip()
        for name in excluded_helper_names
        if str(name or "").strip()
    }
    identity: List[Tuple[str, str]] = []
    verified_helpers = dict(getattr(dossier, "verified_helpers", {}) or {})
    for block in _proof_state_verified_helper_blocks(
        dossier,
        refresh_quality=False,
    ):
        name = str(helper_decl_name(block) or "").strip()
        helper = verified_helpers.get(name)
        rendered_statement_key = canonicalize_lean_statement_for_identity(
            helper_decl_statement(block)
        )
        stored_statement_key = (
            canonicalize_lean_statement_for_identity(
                helper_decl_statement(str(getattr(helper, "source", "") or ""))
            )
            if helper is not None
            else ""
        )
        if helper is not None and rendered_statement_key == stored_statement_key:
            if name in excluded:
                continue
            identity.append(
                (
                    f"verified:{name}",
                    str(getattr(helper, "source_hash", "") or "").strip(),
                )
            )
            continue
        identity.append((f"block:{name}", text_hash(block)))
    return tuple(identity)


@dataclass(frozen=True)
class _CacheSeedBatchReceipt:
    """Exact Lean certificate for ordered same-problem cache prefixes."""

    primary_preamble: str
    answer_safe_preamble: str
    base_context: Tuple[str, ...]
    covered_contexts: Tuple[Tuple[str, Tuple[str, ...]], ...]
    baseline_helper_identities: Tuple[Tuple[str, str], ...]
    baseline_visible_context_identity: Tuple[Tuple[str, str], ...]
    candidate_identities: Tuple[Tuple[str, str], ...]
    verification_environment_hash: str

    def _preambles_match(self, conv: Any) -> bool:
        if self.primary_preamble != _proof_state_check_preamble(conv):
            return False
        if _needs_answer_safe_feedback_check(conv):
            return self.answer_safe_preamble == str(
                getattr(conv, "preamble", "") or ""
            )
        return not self.answer_safe_preamble

    def certifies_exact_context(
        self,
        *,
        conv: Any,
        helper_block: str,
        certified_context: Sequence[str],
    ) -> bool:
        exact_context = tuple(certified_context)
        return bool(
            exact_context
            and self._preambles_match(conv)
            and any(
                certified_helper == helper_block
                and covered_context == exact_context
                for certified_helper, covered_context in self.covered_contexts
            )
        )

    def admission(
        self,
        *,
        conv: Any,
        dossier: ProofDossier,
        helper_block: str,
    ) -> Optional["_CacheSeedBatchAdmission"]:
        if not self._preambles_match(conv):
            return None
        helper_name = str(helper_decl_name(helper_block) or "").strip()
        helper_identity = (helper_name, text_hash(helper_block))
        for index, (certified_helper, certified_context) in enumerate(
            self.covered_contexts
        ):
            if (
                certified_helper == helper_block
                and index < len(self.candidate_identities)
                and self.candidate_identities[index] == helper_identity
            ):
                exact_context = (
                    self.base_context
                    if index == 0
                    else self.covered_contexts[index - 1][1]
                )
                admission = _CacheSeedBatchAdmission(
                    receipt=self,
                    helper_block=helper_block,
                    context=exact_context,
                    certified_context=certified_context,
                    candidate_index=index,
                )
                return (
                    admission
                    if self.authorizes(dossier=dossier, admission=admission)
                    else None
                )
        return None

    def authorizes(
        self,
        *,
        dossier: ProofDossier,
        admission: "_CacheSeedBatchAdmission",
    ) -> bool:
        index = int(admission.candidate_index)
        if (
            index < 0
            or index >= len(self.candidate_identities)
            or index >= len(self.covered_contexts)
        ):
            return False
        expected_helper_identity = self.candidate_identities[index]
        expected_helper_block, expected_certified_context = self.covered_contexts[
            index
        ]
        expected_prior_context = (
            self.base_context
            if index == 0
            else self.covered_contexts[index - 1][1]
        )
        if (
            expected_helper_identity
            != (
                str(helper_decl_name(admission.helper_block) or "").strip(),
                text_hash(admission.helper_block),
            )
            or admission.helper_block != expected_helper_block
            or expected_helper_block not in expected_certified_context
            or admission.context != expected_prior_context
            or admission.certified_context != expected_certified_context
        ):
            return False
        if str(getattr(dossier, "current_lean_environment_hash", "") or "") != (
            self.verification_environment_hash
        ):
            return False
        candidate_names = [name for name, _source_hash in self.candidate_identities]
        expected_registry = tuple(
            sorted(
                [
                    *self.baseline_helper_identities,
                    *self.candidate_identities[:index],
                ]
            )
        )
        visible_prefix = all(
            (helper := getattr(dossier, "verified_helpers", {}).get(name))
            is not None
            and dossier._verified_helper_context_visible(helper)  # noqa: SLF001
            for name, _source_hash in self.candidate_identities[:index]
        )
        return bool(
            visible_prefix
            and _cache_seed_helper_registry_identity(dossier) == expected_registry
            and _cache_seed_visible_base_identity(
                dossier,
                excluded_helper_names=candidate_names,
            )
            == self.baseline_visible_context_identity
        )

@dataclass(frozen=True)
class _CacheSeedBatchAdmission:
    """Exact context capability minted by one live batch receipt."""

    receipt: _CacheSeedBatchReceipt
    helper_block: str
    context: Tuple[str, ...]
    certified_context: Tuple[str, ...]
    candidate_index: int


@dataclass
class _CacheSeedDerivedRefresh:
    """Publish global helper-derived state once per certified cache tranche."""

    dossier: ProofDossier
    proof_state: Optional[ProofSearchState]
    dirty: bool = False

    def mark_dirty(self) -> None:
        self.dirty = True

    def flush(self) -> None:
        if not self.dirty:
            return
        self.dossier._refresh_verified_helper_quality()  # noqa: SLF001
        self.dossier._refresh_verified_helper_statement_aliases(  # noqa: SLF001
            record_metric=True,
        )
        self.dossier.reconcile_verified_facts(
            trigger="cache_seed_batch_finalize",
        )
        if self.proof_state is not None and not bool(
            getattr(self.dossier, "_mini_skip_proof_state_reconcile", False)
        ):
            self.proof_state.reconcile_with_dossier(self.dossier)
        reconcile_promotions = _registered_verified_helper_reconcile_callback(
            self.dossier
        )
        if callable(reconcile_promotions):
            try:
                reconcile_promotions()
            except Exception:
                # Theory persistence is advisory to the already kernel-checked
                # helper set and is retried at the next action boundary.
                pass
        self.dirty = False


_CACHE_SEED_BATCH_RECEIPT_REGISTRY_ATTR = "_cache_seed_batch_receipts"
_CACHE_SEED_BATCH_RECEIPT_REGISTRY_LIMIT = 8


def _cache_seed_batch_receipt_key(receipt: _CacheSeedBatchReceipt) -> str:
    """Return a compact identity for one process-local Lean receipt."""

    payload = {
        "schema_version": 1,
        "primary_preamble_hash": text_hash(receipt.primary_preamble),
        "answer_safe_preamble_hash": (
            text_hash(receipt.answer_safe_preamble)
            if receipt.answer_safe_preamble
            else ""
        ),
        "base_context_hash": text_hash("\n".join(receipt.base_context)),
        "baseline_helper_identities": list(receipt.baseline_helper_identities),
        "baseline_visible_context_identity": list(
            receipt.baseline_visible_context_identity
        ),
        "candidate_identities": list(receipt.candidate_identities),
        "verification_environment_hash": receipt.verification_environment_hash,
        "coverage": [
            [
                text_hash(helper_block),
                text_hash("\n".join(context)),
            ]
            for helper_block, context in receipt.covered_contexts
        ],
    }
    return "cache-seed-batch-v1:" + text_hash(
        json.dumps(payload, sort_keys=True, separators=(",", ":"))
    )


def _remember_cache_seed_batch_receipt(
    proof_state: Optional[ProofSearchState],
    receipt: Optional[_CacheSeedBatchReceipt],
) -> str:
    """Keep paid batch authority process-local across action continuations."""

    if proof_state is None or receipt is None:
        return ""
    registry = getattr(
        proof_state,
        _CACHE_SEED_BATCH_RECEIPT_REGISTRY_ATTR,
        None,
    )
    if not isinstance(registry, dict):
        registry = {}
        setattr(
            proof_state,
            _CACHE_SEED_BATCH_RECEIPT_REGISTRY_ATTR,
            registry,
        )
    key = _cache_seed_batch_receipt_key(receipt)
    registry[key] = receipt
    while len(registry) > _CACHE_SEED_BATCH_RECEIPT_REGISTRY_LIMIT:
        registry.pop(next(iter(registry)))
    return key


def _cached_seed_batch_receipt(
    proof_state: Optional[ProofSearchState],
    key: str,
) -> Optional[_CacheSeedBatchReceipt]:
    """Resolve only live process authority; restored keys recheck with Lean."""

    if proof_state is None or not str(key or "").strip():
        return None
    registry = getattr(
        proof_state,
        _CACHE_SEED_BATCH_RECEIPT_REGISTRY_ATTR,
        None,
    )
    if not isinstance(registry, dict):
        return None
    receipt = registry.get(str(key))
    return receipt if isinstance(receipt, _CacheSeedBatchReceipt) else None


async def _accept_proof_state_helper(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    helper_block: str,
    phase: str,
    turn_index: int,
    timeout_s: float,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    proof_state: Optional[ProofSearchState] = None,
    status_out: Optional[Dict[str, Any]] = None,
    target_statement: str = "",
    require_relevance_gate: bool = False,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
    lean_attempt_observer: Optional[LeanAttemptObserver] = None,
    verified_helper_accept_callback: Optional[Callable[[Any, Any], Any]] = None,
    cache_seed_batch_receipt: Optional["_CacheSeedBatchReceipt"] = None,
    cache_seed_batch_context: Optional[Sequence[str]] = None,
    cache_seed_batch_admission: Optional["_CacheSeedBatchAdmission"] = None,
    defer_cache_seed_derived_refresh: bool = False,
    cache_seed_derived_refresh: Optional["_CacheSeedDerivedRefresh"] = None,
) -> bool:
    """Verify and record a proof-state helper in the authoritative context."""

    observer_started = False
    observer_finished = False
    lean_attempted = False

    def _status(
        status: str,
        *,
        error_kind: str = "",
        error: str = "",
        accepted_name: str = "",
        accepted_source_hash: str = "",
    ) -> None:
        nonlocal observer_finished
        if status_out is None:
            pass
        else:
            status_out.clear()
            status_out.update(
                {
                    "status": str(status or ""),
                    "error_kind": str(error_kind or ""),
                    "error": str(error or "")[:240],
                    "lean_attempted": bool(lean_attempted),
                    "accepted_helper_name": str(accepted_name or ""),
                    "accepted_source_hash": str(accepted_source_hash or ""),
                }
            )
        if observer_started and not observer_finished:
            observer_finished = True
            clean_status = str(status or "")
            clean_error = str(error_kind or "")
            if clean_status == "accepted":
                notify_lean_attempt_observer(
                    lean_attempt_observer,
                    "certificate_accepted",
                    {"helper_name": name, "phase": phase},
                )
            notify_lean_attempt_observer(
                lean_attempt_observer,
                "finished",
                {
                    "ok": clean_status == "accepted",
                    "error_type": clean_error or (
                        "" if clean_status == "accepted" else "lean_rejected"
                    ),
                    "diagnostic": str(error or "")[:240],
                    "exception": (
                        clean_error
                        if clean_status in {"retryable_error", "cancelled"}
                        else ""
                    ),
                    "cancelled": clean_status == "cancelled",
                },
            )

    def deadline_elapsed() -> bool:
        try:
            return bool(
                float(timeout_s or 0.0) <= 0.0
                or (deadline_exhausted and deadline_exhausted())
                or (
                    float(deadline_monotonic or 0.0) > 0.0
                    and time.monotonic() >= float(deadline_monotonic)
                )
            )
        except Exception:
            return True

    def remaining_timeout() -> float:
        # The callback is the programmatic/cancellation analogue of the
        # absolute monotonic boundary.  Re-check it before every expensive
        # acceptance operation (and again after waiting for the shared Lean
        # lock) so a completed primary check cannot launch an answer-safe,
        # relevance, or replacement scan after its enclosing action has
        # already yielded.  The completed check remains durable input for the
        # caller's retry frame; this only defers the next atomic operation.
        if deadline_elapsed():
            return 0.0
        return _fully_funded_operation_timeout(timeout, deadline_monotonic)

    def acceptance_error_kind(exc: BaseException) -> str:
        if isinstance(exc, _LeanOperationDeadline) or (
            deadline_elapsed() and isinstance(exc, asyncio.TimeoutError)
        ):
            return "llm_turn_elapsed_budget_exhausted"
        return type(exc).__name__

    async def await_acceptance_operation(
        awaitable: Any,
        operation_timeout: float,
    ) -> Any:
        # One serializer with formal search: acquire, full-fund recheck,
        # then a result-only watchdog. Intra-search does not force-release a
        # still-running adapter; a timeout detaches, marks the late tail, and
        # keeps the lease so the next acceptance cannot overlap. The Lean
        # call itself still owns kill/reap via ``timeout_s=operation_timeout``;
        # the outer guard only catches an adapter that never returns.
        started = False

        async def operation() -> Any:
            nonlocal started, lean_attempted
            if deadline_elapsed():
                raise _LeanOperationDeadline(
                    "proof-state helper acceptance deadline elapsed"
                )
            started = True
            lean_attempted = True
            return await awaitable

        try:
            return await _await_serialized_lean_operation(
                lean,
                operation,
                timeout_s=operation_timeout,
                deadline_monotonic=deadline_monotonic,
                operation_label="proof_state_helper_acceptance",
                deadline_elapsed=deadline_elapsed,
                release_unrecyclable_tail=False,
            )
        except BaseException:
            if not started:
                close = getattr(awaitable, "close", None)
                if callable(close):
                    close()
            raise

    if deadline_elapsed():
        _status("retryable_error", error_kind="llm_turn_elapsed_budget_exhausted")
        return False

    name = helper_decl_name(helper_block)
    if not name:
        _status("rejected", error_kind="invalid_helper_name")
        return False
    existing_name = (
        dossier.resolve_verified_helper_name(name)
        if dossier.has_helper(name)
        else name
    )
    existing = dossier.verified_helpers.get(existing_name)
    helper_statement = helper_decl_statement(helper_block)
    existing_statement = (
        helper_decl_statement(str(getattr(existing, "source", "") or ""))
        if existing is not None
        else ""
    )
    existing_key = canonicalize_lean_statement_for_identity(existing_statement)
    helper_key = canonicalize_lean_statement_for_identity(helper_statement)
    if existing is not None:
        if existing_key != helper_key:
            old_name = name
            reserved_names = set(dossier.verified_helpers)
            reserved_names.update(getattr(dossier, "proposed_helpers", {}) or {})
            proof_graph = getattr(dossier, "proof_graph", None)
            reserved_names.update(
                getattr(proof_graph, "helper_name_to_node_id", {}) or {}
            )
            name = _fresh_helper_collision_name(
                old_name,
                reserved_names=reserved_names,
            )
            helper_block = _rename_helper_identifier(helper_block, old_name, name)
            helper_statement = helper_decl_statement(helper_block)
            existing = None
            existing_statement = ""
            existing_key = ""
        # Same-statement crash replay deliberately falls through the complete
        # current policy, primary, answer-safe, relevance, and replacement
        # checks. Proposition equality alone is not a current-context receipt.
    if _proof_state_helper_policy_rejection(helper_block):
        _status("rejected", error_kind="proof_state_helper_policy_rejection")
        return False
    timeout = float(timeout_s or 0.0)
    if timeout <= 0.0:
        _status("retryable_error", error_kind="nonpositive_timeout_deferred")
        return False
    observer_started = True
    notify_lean_attempt_observer(
        lean_attempt_observer,
        "started",
        {
            "helper_name": name,
            "phase": phase,
            "target_statement": target_statement,
        },
    )
    stale_dependents: Set[str] = set()
    batch_admission = cache_seed_batch_admission
    recomputed_certified_context = (
        tuple(
            merge_context_helpers(
                list(batch_admission.context),
                [helper_block],
            )
        )
        if batch_admission is not None
        else ()
    )
    batch_admission_authorized = bool(
        existing is None
        and cache_seed_batch_receipt is not None
        and batch_admission is not None
        and batch_admission.receipt is cache_seed_batch_receipt
        and batch_admission.helper_block == helper_block
        and batch_admission.certified_context == recomputed_certified_context
        and cache_seed_batch_receipt.authorizes(
            dossier=dossier,
            admission=batch_admission,
        )
        and cache_seed_batch_receipt.certifies_exact_context(
            conv=conv,
            helper_block=helper_block,
            certified_context=batch_admission.certified_context,
        )
    )
    try:
        if existing is not None:
            operation_timeout = remaining_timeout()
            if operation_timeout <= 0.0:
                _status(
                    "retryable_error",
                    error_kind="llm_turn_elapsed_budget_exhausted",
                )
                return False
            context, _ = await await_acceptance_operation(
                lean_valid_helper_context_excluding_name(
                    lean,
                    list(_proof_state_verified_helper_blocks(dossier)),
                    name,
                    preamble=_proof_state_check_preamble(conv),
                    timeout_s=operation_timeout,
                    # Aggregate cap for the whole revalidation sweep. These are
                    # `while pending:` over `for block in pending:` loops, so
                    # they can run O(N^2) sequential Lean checks each funded
                    # with the full per-check timeout. The outer strict-deadline
                    # guard used to be the only thing bounding them, and it
                    # bounded them by discarding the verdict.
                    deadline_monotonic=time.monotonic() + float(operation_timeout),
                    true_statement="True",
                    true_proof="by\n  trivial",
                ),
                operation_timeout,
            )
        elif batch_admission_authorized and cache_seed_batch_context is not None:
            context = list(cache_seed_batch_context)
        else:
            context = list(_proof_state_verified_helper_blocks(dossier))
    except asyncio.CancelledError:
        _status("cancelled", error_kind="cancelled")
        raise
    except Exception as exc:
        _status(
            "retryable_error",
            error_kind=acceptance_error_kind(exc),
            error=str(exc),
        )
        return False
    if existing is None:
        # A forced/base declaration with the candidate's name must not stand
        # in for the cached source being admitted. Verify the candidate body
        # itself, then let normal publication own that contextual name.
        context = [
            block
            for block in context
            if str(helper_decl_name(block) or "").strip() != name
        ]
    batch_prevalidated = bool(
        batch_admission_authorized
        and batch_admission is not None
        and batch_admission.context == tuple(context)
    )
    if not batch_prevalidated:
        try:
            operation_timeout = remaining_timeout()
            if operation_timeout <= 0.0:
                _status(
                    "retryable_error",
                    error_kind="llm_turn_elapsed_budget_exhausted",
                )
                return False
            try:
                result = await await_acceptance_operation(
                    lean.check(
                        "True",
                        "by\n  trivial",
                        merge_context_helpers(context, [helper_block]),
                        preamble_override=_proof_state_check_preamble(conv),
                        timeout_s=operation_timeout,
                        check_kind="proof_state_helper",
                    ),
                    operation_timeout,
                )
            except TypeError:
                try:
                    result = await await_acceptance_operation(
                        lean.check(
                            "True",
                            "by\n  trivial",
                            merge_context_helpers(context, [helper_block]),
                            preamble_override=_proof_state_check_preamble(conv),
                            timeout_s=operation_timeout,
                        ),
                        operation_timeout,
                    )
                except TypeError:
                    result = await await_acceptance_operation(
                        lean.check(
                            "True",
                            "by\n  trivial",
                            merge_context_helpers(context, [helper_block]),
                            preamble_override=_proof_state_check_preamble(conv),
                        ),
                        operation_timeout,
                    )
        except Exception as exc:
            _status(
                "retryable_error",
                error_kind=acceptance_error_kind(exc),
                error=str(exc),
            )
            return False
        if not bool(getattr(result, "ok", False)):
            error_kind = (
                canonical_error_type(getattr(result, "parsed", None))
                or "proof_state_helper_check_failed"
            )
            _status(
                (
                    "retryable_error"
                    if _decl_application_failure_is_retryable(error_kind)
                    else "rejected"
                ),
                error_kind=error_kind,
            )
            return False
    if _needs_answer_safe_feedback_check(conv) and not batch_prevalidated:
        operation_timeout = remaining_timeout()
        if operation_timeout <= 0.0:
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        try:
            safe_result = await await_acceptance_operation(
                lean.check(
                    "True",
                    "by\n  trivial",
                    merge_context_helpers(context, [helper_block]),
                    preamble_override=str(getattr(conv, "preamble", "") or ""),
                    timeout_s=operation_timeout,
                    check_kind="proof_state_helper_answer_safe",
                ),
                operation_timeout,
            )
        except TypeError:
            try:
                safe_result = await await_acceptance_operation(
                    lean.check(
                        "True",
                        "by\n  trivial",
                        merge_context_helpers(context, [helper_block]),
                        preamble_override=str(getattr(conv, "preamble", "") or ""),
                        timeout_s=operation_timeout,
                    ),
                    operation_timeout,
                )
            except TypeError:
                try:
                    safe_result = await await_acceptance_operation(
                        lean.check(
                            "True",
                            "by\n  trivial",
                            merge_context_helpers(context, [helper_block]),
                            preamble_override=str(getattr(conv, "preamble", "") or ""),
                        ),
                        operation_timeout,
                    )
                except Exception as exc:
                    _status(
                        "retryable_error",
                        error_kind=acceptance_error_kind(exc),
                        error=str(exc),
                    )
                    return False
            except Exception as exc:
                _status(
                    "retryable_error",
                    error_kind=acceptance_error_kind(exc),
                    error=str(exc),
                )
                return False
        except Exception as exc:
            _status(
                "retryable_error",
                error_kind=acceptance_error_kind(exc),
                error=str(exc),
            )
            return False
        if not bool(getattr(safe_result, "ok", False)):
            error_kind = (
                canonical_error_type(getattr(safe_result, "parsed", None))
                or "proof_state_helper_answer_safe_check_failed"
            )
            _status(
                (
                    "retryable_error"
                    if _decl_application_failure_is_retryable(error_kind)
                    else "rejected"
                ),
                error_kind=error_kind,
            )
            return False
    if require_relevance_gate:
        check_lemmas = merge_context_helpers(context, [helper_block])
        operation_timeout = remaining_timeout()
        if operation_timeout <= 0.0:
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        try:
            relevance_ok, relevance_rejection = await await_acceptance_operation(
                _proof_state_helper_passes_relevance_gate(
                    lean=lean,
                    conv=conv,
                    dossier=dossier,
                    proof_state=proof_state,
                    helper_block=helper_block,
                    check_lemmas=check_lemmas,
                    timeout_s=operation_timeout,
                    target_statement=target_statement,
                ),
                operation_timeout,
            )
        except asyncio.TimeoutError:
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        except Exception as exc:
            _status(
                "retryable_error",
                error_kind=acceptance_error_kind(exc),
                error=str(exc),
            )
            return False
        if not relevance_ok:
            if relevance_rejection == "relevance_probe_inconclusive":
                _status(
                    "retryable_error",
                    error_kind="relevance_probe_inconclusive",
                )
            else:
                _status("rejected", error_kind=relevance_rejection or "off_topic")
            return False
    if existing is not None:
        operation_timeout = remaining_timeout()
        if operation_timeout <= 0.0:
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        try:
            stale_dependents = await await_acceptance_operation(
                lean_invalid_helpers_after_replacement(
                    lean,
                    list(_proof_state_verified_helper_blocks(dossier)),
                    name,
                    helper_block,
                    context,
                    preamble=_proof_state_check_preamble(conv),
                    timeout_s=operation_timeout,
                    # Aggregate cap for the whole revalidation sweep. These are
                    # `while pending:` over `for block in pending:` loops, so
                    # they can run O(N^2) sequential Lean checks each funded
                    # with the full per-check timeout. The outer strict-deadline
                    # guard used to be the only thing bounding them, and it
                    # bounded them by discarding the verdict.
                    deadline_monotonic=time.monotonic() + float(operation_timeout),
                    true_statement="True",
                    true_proof="by\n  trivial",
                ),
                operation_timeout,
            )
        except asyncio.TimeoutError:
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        except Exception as exc:
            _status(
                "retryable_error",
                error_kind=acceptance_error_kind(exc),
                error=str(exc),
            )
            return False
    # The monotonic deadline is an admission boundary between atomic checks.
    # Once every required check was fully admitted and completed, publication
    # must not discard that valid certificate merely because the clock crossed
    # during the operation. An explicit cancellation callback remains
    # authoritative and keeps teardown transactional.
    combined_deadline_exhausted = deadline_exhausted
    transaction = DeadlineMutationTransaction(
        deadline_exhausted=combined_deadline_exhausted,
        dossier=dossier,
        proof_state=proof_state,
        label="proof_state_helper_acceptance",
    )
    with transaction:
        if not transaction.can_mutate():
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
        for dependent_name in sorted(stale_dependents):
            dossier.remove_verified_helper(dependent_name)
        defer_derived_refresh = bool(
            defer_cache_seed_derived_refresh and batch_prevalidated
        )
        try:
            item = dossier.record_verified_helper(
                helper_block,
                phase=phase,
                turn_index=turn_index,
                replay_context_names=[
                    helper_decl_name(block) or ""
                    for block in context
                    if helper_decl_name(block)
                ],
                _defer_global_derived_refresh=defer_derived_refresh,
            )
        finally:
            if defer_derived_refresh and cache_seed_derived_refresh is not None:
                recorded = getattr(dossier, "verified_helpers", {}).get(name)
                if str(getattr(recorded, "source_hash", "") or "") == text_hash(
                    helper_block
                ):
                    cache_seed_derived_refresh.mark_dirty()
        if item is None:
            _status("rejected", error_kind="record_verified_helper_rejected")
            return False
        if existing is not None:
            refresh_revalidated_dependent_support_hashes(dossier, name)
        if proof_state is not None:
            invalidated_helper_names = (
                {name, *stale_dependents} if existing is not None else set()
            )
            if not bool(getattr(dossier, "_mini_skip_proof_state_reconcile", False)):
                proof_state.reconcile_with_dossier(dossier)
            proof_state.invalidate_assembly_contracts_for_helpers(
                invalidated_helper_names,
                phase=phase,
                turn_index=turn_index,
                conservative=True,
            )
        if proof_cache is not None and transaction.enabled:
            publication = stage_verified_helper_for_dossier(
                proof_cache,
                helper_block,
                preamble=_proof_state_check_preamble(conv),
                dossier=dossier,
                phase=phase,
                deadline_exhausted=transaction.deadline_elapsed,
            )
            if publication is not None:
                transaction.add_participant(publication)
        if not transaction.can_mutate():
            _status(
                "retryable_error",
                error_kind="llm_turn_elapsed_budget_exhausted",
            )
            return False
    if transaction.enabled and not transaction.committed:
        _status(
            "retryable_error",
            error_kind=(
                "llm_turn_elapsed_budget_exhausted"
                if transaction.deadline_won
                else "deadline_mutation_commit_failed"
            ),
        )
        return False
    if proof_cache is not None and not transaction.enabled:
        store_verified_helper_for_dossier(
            proof_cache,
            helper_block,
            preamble=_proof_state_check_preamble(conv),
            dossier=dossier,
            phase=phase,
        )
    callback = verified_helper_accept_callback
    if not callable(callback):
        callback = _registered_verified_helper_accept_callback(dossier)
    if callable(callback):
        try:
            callback(item, dossier)
        except Exception:
            # Durable theory staging is advisory and must never roll back a
            # helper whose verification transaction already committed.
            pass
    _status(
        "accepted",
        accepted_name=str(getattr(item, "name", "") or name),
        accepted_source_hash=str(
            getattr(item, "source_hash", "") or text_hash(helper_block)
        ),
    )
    return True


def _dependency_order_cache_seed_records(
    records: Sequence[Mapping[str, Any]],
) -> List[Dict[str, Any]]:
    indexed: List[Tuple[int, Dict[str, Any], str, str]] = []
    for index, raw in enumerate(records):
        record = dict(raw or {})
        source = str(record.get("source") or "").strip()
        source_hash = str(record.get("source_hash") or "").strip() or (
            text_hash(source) if source else ""
        )
        indexed.append((index, record, source, source_hash))
    if not indexed:
        return []
    ordered_sources = order_helpers_for_incremental_validation(
        [source for _index, _record, source, _source_hash in indexed if source]
    )
    order_by_hash: Dict[str, int] = {}
    for order, source in enumerate(ordered_sources):
        source_hash = text_hash(source)
        order_by_hash.setdefault(source_hash, order)
    base_order = [
        record
        for original_index, record, _source, source_hash in sorted(
            indexed,
            key=lambda item: (
                order_by_hash.get(item[3], len(indexed) + item[0]),
                item[0],
            ),
        )
    ]
    candidate_names = {
        helper_decl_name(str(record.get("source") or ""))
        or str(record.get("name") or "").strip()
        for record in base_order
    }
    candidate_names.discard("")
    pending = list(base_order)
    ordered: List[Dict[str, Any]] = []
    emitted_names: Set[str] = set()
    while pending:
        progressed = False
        next_pending: List[Dict[str, Any]] = []
        for record in pending:
            dependencies = {
                str(name or "").strip()
                for name in list(record.get("replay_context_names") or [])
                if str(name or "").strip() in candidate_names
            }
            if dependencies <= emitted_names:
                ordered.append(record)
                name = helper_decl_name(str(record.get("source") or "")) or str(
                    record.get("name") or ""
                ).strip()
                if name:
                    emitted_names.add(name)
                progressed = True
            else:
                next_pending.append(record)
        if not progressed:
            ordered.extend(next_pending)
            break
        pending = next_pending
    return ordered


def _cache_seed_batch_validation_input(
    records: Sequence[Mapping[str, Any]],
    *,
    dossier: ProofDossier,
) -> Tuple[
    Tuple[str, ...],
    Tuple[str, ...],
    Tuple[Tuple[str, Tuple[str, ...]], ...],
]:
    """Build an exact ordered closure only when every batch guard is known."""

    available_hashes = {
        str(name or "").strip(): str(getattr(helper, "source_hash", "") or "")
        for name, helper in dict(getattr(dossier, "verified_helpers", {}) or {}).items()
        if str(name or "").strip()
    }
    context = list(_proof_state_verified_helper_blocks(dossier))
    base_context = tuple(context)
    base_context_names = {
        str(helper_decl_name(block) or "").strip()
        for block in base_context
        if str(helper_decl_name(block) or "").strip()
    }
    helper_blocks: List[str] = []
    covered_contexts: List[Tuple[str, Tuple[str, ...]]] = []
    seen_source_hashes: Set[str] = set()
    for record in records:
        helper_block = str(record.get("source") or "").strip()
        helper_name = helper_decl_name(helper_block) or str(
            record.get("name") or ""
        ).strip()
        actual_source_hash = text_hash(helper_block) if helper_block else ""
        recorded_source_hash = str(record.get("source_hash") or "").strip()
        if (
            not helper_block
            or not helper_name
            or helper_name in available_hashes
            or helper_name in base_context_names
            or actual_source_hash in seen_source_hashes
            or (
                recorded_source_hash
                and recorded_source_hash != actual_source_hash
            )
            or _proof_state_helper_policy_rejection(helper_block)
        ):
            return (), (), ()
        replay_names = {
            str(name or "").strip()
            for name in list(record.get("replay_context_names") or [])
            if str(name or "").strip() and str(name or "").strip() != helper_name
        }
        if not replay_names.issubset(available_hashes):
            return (), (), ()
        expected_hashes = {
            str(name or "").strip(): str(source_hash or "").strip()
            for name, source_hash in dict(
                record.get("replay_context_source_hashes") or {}
            ).items()
            if str(name or "").strip() and str(source_hash or "").strip()
        }
        if any(
            name not in available_hashes
            or available_hashes[name] != expected_hash
            for name, expected_hash in expected_hashes.items()
        ):
            return (), (), ()
        context = merge_context_helpers(context, [helper_block])
        if helper_block not in context:
            return (), (), ()
        covered_contexts.append((helper_block, tuple(context)))
        helper_blocks.append(helper_block)
        available_hashes[helper_name] = actual_source_hash
        seen_source_hashes.add(actual_source_hash)
    if len(helper_blocks) <= 1:
        return (), (), ()
    final_context = covered_contexts[-1][1]
    if any(
        final_context[: len(certified_context)] != certified_context
        for _helper_block, certified_context in covered_contexts
    ):
        # One full Lean file certifies each earlier admission only when its
        # exact acceptance context is a declaration prefix of that file.
        return (), (), ()
    return tuple(helper_blocks), base_context, tuple(covered_contexts)


async def _validate_same_problem_cache_batch(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    records: Sequence[Mapping[str, Any]],
    timeout_s: float,
) -> Tuple[Optional[_CacheSeedBatchReceipt], Dict[str, Any]]:
    """Certify one valid cache closure in one Lean compilation.

    A failed or unavailable batch is advisory: the caller retains the full
    per-helper verifier path, so batching can improve latency without reducing
    which cached helpers the search can recover.
    """

    helper_blocks, base_context, covered_contexts = _cache_seed_batch_validation_input(
        records,
        dossier=dossier,
    )
    telemetry: Dict[str, Any] = {
        "batch_validation_attempted": False,
        "batch_validation_succeeded": False,
        "batch_validation_certified_count": 0,
        "batch_validation_check_count": 0,
        "batch_validation_elapsed_s": 0.0,
        "batch_validation_verdict": "batch_validation_ineligible",
    }
    if not helper_blocks:
        return None, telemetry
    batch_timeout_s = max(
        float(timeout_s or 0.0),
        min(
            60.0,
            max(
                2.0 * float(timeout_s or 0.0),
                float(timeout_s or 0.0) + 0.5 * len(helper_blocks),
            ),
        ),
    )
    if batch_timeout_s <= 0.0:
        return None, telemetry
    telemetry["batch_validation_attempted"] = True
    started = time.monotonic()

    def signature_rejects_keyword(exc: TypeError, keyword: str) -> bool:
        message = str(exc or "").lower()
        return "unexpected keyword argument" in message and keyword.lower() in message

    async def check(
        preamble: str,
        check_kind: str,
        lemmas: Sequence[str],
    ) -> Any:
        async def operation() -> Any:
            optional_kwargs: Dict[str, Any] = {
                "timeout_s": batch_timeout_s,
                "check_kind": check_kind,
            }
            for _attempt in range(3):
                try:
                    return await lean.check(
                        "True",
                        "by\n  trivial",
                        list(lemmas),
                        preamble_override=preamble,
                        **optional_kwargs,
                    )
                except TypeError as exc:
                    rejected_keyword = next(
                        (
                            keyword
                            for keyword in ("check_kind", "timeout_s")
                            if keyword in optional_kwargs
                            and signature_rejects_keyword(exc, keyword)
                        ),
                        "",
                    )
                    if not rejected_keyword:
                        raise
                    optional_kwargs.pop(rejected_keyword, None)
            return await lean.check(
                    "True",
                    "by\n  trivial",
                    list(lemmas),
                    preamble_override=preamble,
                )

        return await _await_serialized_lean_operation(
            lean,
            operation,
            timeout_s=batch_timeout_s,
            operation_label=check_kind,
        )

    primary_preamble = _proof_state_check_preamble(conv)
    answer_safe_preamble = (
        str(getattr(conv, "preamble", "") or "")
        if _needs_answer_safe_feedback_check(conv)
        else ""
    )
    candidate_sizes = [len(helper_blocks)]
    if len(helper_blocks) >= 4:
        candidate_sizes.append(len(helper_blocks) // 2)
    last_failure_kind = ""
    batch_exception = False
    try:
        for candidate_size in candidate_sizes:
            candidate_contexts = covered_contexts[:candidate_size]
            lemmas = candidate_contexts[-1][1]
            telemetry["batch_validation_check_count"] = int(
                telemetry["batch_validation_check_count"]
            ) + 1
            primary_result = await check(
                primary_preamble,
                "proof_state_cache_seed_batch",
                lemmas,
            )
            if not bool(getattr(primary_result, "ok", False)):
                last_failure_kind = (
                    canonical_error_type(getattr(primary_result, "parsed", None))
                    or "proof_state_cache_seed_batch_check_failed"
                )
                if _decl_application_failure_is_retryable(last_failure_kind):
                    break
                continue
            if answer_safe_preamble:
                telemetry["batch_validation_check_count"] = int(
                    telemetry["batch_validation_check_count"]
                ) + 1
                answer_safe_result = await check(
                    answer_safe_preamble,
                    "proof_state_cache_seed_batch_answer_safe",
                    lemmas,
                )
                if not bool(getattr(answer_safe_result, "ok", False)):
                    last_failure_kind = (
                        canonical_error_type(
                            getattr(answer_safe_result, "parsed", None)
                        )
                        or "proof_state_cache_seed_batch_answer_safe_check_failed"
                    )
                    if _decl_application_failure_is_retryable(last_failure_kind):
                        break
                    continue
            receipt = _CacheSeedBatchReceipt(
                primary_preamble=primary_preamble,
                answer_safe_preamble=answer_safe_preamble,
                base_context=base_context,
                covered_contexts=candidate_contexts,
                baseline_helper_identities=(
                    _cache_seed_helper_registry_identity(dossier)
                ),
                baseline_visible_context_identity=(
                    _cache_seed_visible_base_identity(dossier)
                ),
                candidate_identities=tuple(
                    (
                        str(helper_decl_name(block) or "").strip(),
                        text_hash(block),
                    )
                    for block in helper_blocks[:candidate_size]
                ),
                verification_environment_hash=str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ),
            )
            telemetry.update(
                {
                    "batch_validation_succeeded": True,
                    "batch_validation_certified_count": candidate_size,
                    "batch_validation_verdict": (
                        "batch_validation_succeeded"
                        if candidate_size == len(helper_blocks)
                        else "batch_validation_prefix_succeeded"
                    ),
                }
            )
            return receipt, telemetry
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        batch_exception = True
        telemetry["batch_validation_failure_kind"] = type(exc).__name__
        telemetry["batch_validation_failure"] = str(exc)[:240]
        telemetry["batch_validation_verdict"] = "batch_validation_exception"
    finally:
        telemetry["batch_validation_elapsed_s"] = round(
            time.monotonic() - started,
            6,
        )
    if last_failure_kind and not batch_exception:
        telemetry["batch_validation_failure_kind"] = last_failure_kind
        telemetry["batch_validation_verdict"] = "batch_validation_rejected"
    return None, telemetry


async def seed_verified_helpers_from_same_problem_cache(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    proof_state: Optional[ProofSearchState],
    proof_cache: Optional[MiniVerifiedLemmaCache],
    theorem_name: str,
    timeout_s: float = 12.0,
    max_helpers: int = 64,
    max_passes: int = 3,
    _candidate_records: Optional[Sequence[Mapping[str, Any]]] = None,
    _batch_receipt_key: str = "",
) -> Dict[str, Any]:
    """Seed cached helpers and finalize every certified admission tranche."""

    derived_refresh = _CacheSeedDerivedRefresh(
        dossier=dossier,
        proof_state=proof_state,
    )
    try:
        return await _seed_verified_helpers_from_same_problem_cache_impl(
            lean=lean,
            conv=conv,
            dossier=dossier,
            proof_state=proof_state,
            proof_cache=proof_cache,
            theorem_name=theorem_name,
            timeout_s=timeout_s,
            max_helpers=max_helpers,
            max_passes=max_passes,
            _candidate_records=_candidate_records,
            _batch_receipt_key=_batch_receipt_key,
            _derived_refresh=derived_refresh,
        )
    finally:
        derived_refresh.flush()


async def _seed_verified_helpers_from_same_problem_cache_impl(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    proof_state: Optional[ProofSearchState],
    proof_cache: Optional[MiniVerifiedLemmaCache],
    theorem_name: str,
    timeout_s: float = 12.0,
    max_helpers: int = 64,
    max_passes: int = 3,
    _candidate_records: Optional[Sequence[Mapping[str, Any]]] = None,
    _batch_receipt_key: str = "",
    _derived_refresh: _CacheSeedDerivedRefresh,
) -> Dict[str, Any]:
    """Re-kernel-check and import same-problem cached helpers at run start.

    The cache is not proof authority. Each helper is accepted only after
    ``_accept_proof_state_helper`` compiles it in the current Lean preamble.
    The relevance gate is deliberately skipped: these helpers are the prior
    local toolbox for this exact problem, not claims that must close the
    current root/frontier target directly.
    """

    summary: Dict[str, Any] = {
        "phase": "proof_state_cache_seed",
        "verdict": "cache_seed_skipped",
        "theorem_name": str(theorem_name or "").strip(),
        "candidate_count": 0,
        "accepted_count": 0,
        "accepted_helper_names": [],
        "rejected_count": 0,
        "duplicate_count": 0,
        "name_collision_count": 0,
        "retryable_error_count": 0,
        "records": [],
    }
    if (
        (proof_cache is None and _candidate_records is None)
        or lean is None
        or conv is None
        or dossier is None
        or not summary["theorem_name"]
        or float(timeout_s or 0.0) <= 0.0
        or int(max_helpers or 0) <= 0
    ):
        return summary

    if _candidate_records is not None:
        candidates = [dict(item) for item in _candidate_records]
    else:
        records_for_theorem = getattr(proof_cache, "records_for_theorem", None)
        if not callable(records_for_theorem):
            return summary
        try:
            candidates = list(
                records_for_theorem(
                    summary["theorem_name"],
                    max_records=max(0, int(max_helpers or 0)),
                    preamble=_proof_state_check_preamble(conv),
                )
                or []
            )
        except Exception as exc:
            summary["verdict"] = "cache_seed_lookup_failed"
            summary["error_kind"] = type(exc).__name__
            summary["error"] = str(exc)[:240]
            return summary

    summary["candidate_count"] = len(candidates)
    if not candidates:
        summary["verdict"] = "cache_seed_empty"
        return summary

    increment = getattr(dossier, "increment_tool_metric", None)

    def inc(key: str, amount: int = 1) -> None:
        if callable(increment):
            try:
                increment(key, amount)
                return
            except Exception:
                pass
        metrics = getattr(dossier, "tool_metrics", None)
        if isinstance(metrics, dict):
            metrics[key] = int(metrics.get(key, 0) or 0) + int(amount or 0)

    inc("mini_proof_state_cache_seed_candidates", len(candidates))
    pending = _dependency_order_cache_seed_records(candidates)
    batch_receipt = _cached_seed_batch_receipt(
        proof_state,
        _batch_receipt_key,
    )
    if batch_receipt is not None and pending:
        first_helper_block = str(pending[0].get("source") or "").strip()
        if (
            not first_helper_block
            or batch_receipt.admission(
                conv=conv,
                dossier=dossier,
                helper_block=first_helper_block,
            )
            is None
        ):
            # The process-local capability belongs to an older preamble,
            # helper prefix, or certified subset. Fall back to the ordinary
            # batch/per-helper verifier path; never treat a stale receipt as
            # rejection evidence.
            batch_receipt = None
    if batch_receipt is None:
        batch_receipt, batch_validation_telemetry = (
            await _validate_same_problem_cache_batch(
                lean=lean,
                conv=conv,
                dossier=dossier,
                records=pending,
                timeout_s=float(timeout_s or 0.0),
            )
        )
    else:
        batch_validation_telemetry = {
            "batch_validation_attempted": False,
            "batch_validation_succeeded": True,
            "batch_validation_certified_count": 0,
            "batch_validation_check_count": 0,
            "batch_validation_elapsed_s": 0.0,
            "batch_validation_verdict": "batch_validation_receipt_resumed",
        }
    batch_receipt_key = _remember_cache_seed_batch_receipt(
        proof_state,
        batch_receipt,
    )
    summary["batch_candidate_count"] = len(pending)
    summary.update(batch_validation_telemetry)
    batch_validation_attempted = bool(
        batch_validation_telemetry.get("batch_validation_attempted")
    )
    if batch_validation_attempted:
        inc(
            "mini_proof_state_cache_seed_batch_checks",
            int(
                batch_validation_telemetry.get(
                    "batch_validation_check_count",
                    0,
                )
                or 0
            ),
        )
    if batch_receipt is not None:
        inc(
            "mini_proof_state_cache_seed_batch_helpers_certified",
            int(
                batch_validation_telemetry.get(
                    "batch_validation_certified_count",
                    0,
                )
                or 0
            ),
        )
    accepted_source_hashes: Set[str] = set()
    terminal_source_hashes: Set[str] = set()
    passes = max(1, int(max_passes or 1))

    for pass_index in range(passes):
        if not pending:
            break
        progressed = False
        next_pending: List[Dict[str, Any]] = []
        for pending_index, record in enumerate(pending):
            helper_block = str(record.get("source") or "").strip()
            helper_name = helper_decl_name(helper_block) or str(
                record.get("name") or ""
            ).strip()
            source_hash = str(record.get("source_hash") or "") or (
                text_hash(helper_block) if helper_block else ""
            )
            record_summary: Dict[str, Any] = {
                "helper_name": helper_name,
                "cache_source_hash": source_hash,
                "cache_lookup_tier": str(record.get("_lookup_tier") or "same_theorem"),
                "pass_index": pass_index,
                "accepted": False,
            }
            if not helper_block or not helper_name:
                record_summary["rejection"] = "malformed_cache_record"
                terminal_source_hashes.add(source_hash)
                summary["records"].append(record_summary)
                continue
            if source_hash in accepted_source_hashes or source_hash in terminal_source_hashes:
                continue
            replay_context_names = [
                str(name or "").strip()
                for name in list(record.get("replay_context_names") or [])
                if str(name or "").strip() and str(name or "").strip() != helper_name
            ]
            missing_replay_context = [
                name
                for name in replay_context_names
                if name not in getattr(dossier, "verified_helpers", {})
            ]
            if missing_replay_context:
                record_summary["rejection"] = "cache_seed_replay_context_pending"
                record_summary["missing_replay_context_names"] = missing_replay_context
                next_pending.append(record)
                continue
            expected_replay_hashes = {
                str(name or "").strip(): str(context_hash or "").strip()
                for name, context_hash in dict(
                    record.get("replay_context_source_hashes") or {}
                ).items()
                if str(name or "").strip() and str(context_hash or "").strip()
            }
            stale_replay_context = [
                name
                for name, expected_hash in expected_replay_hashes.items()
                if name in getattr(dossier, "verified_helpers", {})
                and str(
                    getattr(dossier.verified_helpers[name], "source_hash", "") or ""
                ).strip()
                != expected_hash
            ]
            if stale_replay_context:
                record_summary["rejection"] = "cache_seed_replay_context_stale"
                record_summary["stale_replay_context_names"] = stale_replay_context
                terminal_source_hashes.add(source_hash)
                summary["records"].append(record_summary)
                continue
            existing = getattr(dossier, "verified_helpers", {}).get(helper_name)
            reused_existing_helper = False
            if existing is not None:
                existing_statement = helper_decl_statement(
                    str(getattr(existing, "source", "") or "")
                )
                helper_statement = helper_decl_statement(helper_block)
                if (
                    canonicalize_lean_statement_for_identity(existing_statement)
                    == canonicalize_lean_statement_for_identity(helper_statement)
                ):
                    # A proposition/name match is not a current-policy or
                    # answer-safe receipt. Re-attest the exact source through
                    # the same authoritative acceptance path used for a fresh
                    # cache record; only then count it as reusable.
                    reused_existing_helper = True
                else:
                    record_summary["rejection"] = (
                        "cache_seed_helper_name_collision"
                    )
                    terminal_source_hashes.add(source_hash)
                    summary["name_collision_count"] = (
                        int(summary["name_collision_count"]) + 1
                    )
                    summary["records"].append(record_summary)
                    continue
            rejection = _proof_state_helper_policy_rejection(helper_block)
            if rejection:
                record_summary["rejection"] = rejection
                terminal_source_hashes.add(source_hash)
                summary["records"].append(record_summary)
                continue

            batch_context: Optional[List[str]] = None
            batch_admission: Optional[_CacheSeedBatchAdmission] = None
            if batch_receipt is not None and existing is None:
                batch_admission = batch_receipt.admission(
                    conv=conv,
                    dossier=dossier,
                    helper_block=helper_block,
                )
                if batch_admission is not None:
                    batch_context = list(batch_admission.context)
            if batch_admission is None and _derived_refresh.dirty:
                # Receipt coverage ended. Publish the certified prefix before
                # an ordinary verifier observes or hashes its helper context.
                _derived_refresh.flush()
                if batch_receipt is not None and existing is None:
                    batch_admission = batch_receipt.admission(
                        conv=conv,
                        dossier=dossier,
                        helper_block=helper_block,
                    )
                    if batch_admission is not None:
                        batch_context = list(batch_admission.context)
            if batch_admission is None:
                batch_context = None

            root_node = (
                proof_state.nodes.get(proof_state.root_node_id)
                if proof_state is not None
                else None
            )
            remaining_cache_records = [
                dict(item)
                for item in (
                    list(pending[pending_index + 1 :]) + list(next_pending)
                )
            ]
            if root_node is not None:
                staged = stage_pending_helper_acceptance(
                    conv=conv,
                    dossier=dossier,
                    node=root_node,
                    helper_block=helper_block,
                    source=f"cache_seed:{source_hash}",
                    continuation={
                        "kind": "cache_seed_batch",
                        "theorem_name": summary["theorem_name"],
                        "remaining_cache_records": remaining_cache_records,
                        "timeout_s": float(timeout_s or 0.0),
                        "batch_receipt_key": batch_receipt_key,
                    },
                    refresh_quality=batch_admission is None,
                )
                if not staged:
                    summary["retryable_error_count"] = (
                        int(summary["retryable_error_count"]) + 1
                    )
                    summary["verdict"] = "cache_seed_pending_owner_busy"
                    return summary
            if batch_admission is not None:
                # The batch removed the per-helper Lean await. Yield only
                # after the current candidate and its suffix are represented
                # in the helper-acceptance WAL, so cancellation remains prompt
                # without losing already-paid cache work.
                await asyncio.sleep(0)

            status: Dict[str, Any] = {}
            accepted = await _accept_proof_state_helper(
                lean=lean,
                conv=conv,
                dossier=dossier,
                helper_block=helper_block,
                phase="proof_state_cache_seed",
                turn_index=0,
                timeout_s=float(timeout_s or 0.0),
                proof_cache=None,
                proof_state=proof_state,
                status_out=status,
                target_statement="",
                require_relevance_gate=False,
                cache_seed_batch_receipt=(
                    batch_receipt if batch_admission is not None else None
                ),
                cache_seed_batch_context=batch_context,
                cache_seed_batch_admission=batch_admission,
                defer_cache_seed_derived_refresh=batch_admission is not None,
                cache_seed_derived_refresh=_derived_refresh,
            )
            record_summary["accepted"] = bool(accepted)
            if accepted:
                if root_node is not None:
                    root_node.pending_helper_acceptance = {}
                accepted_source_hashes.add(source_hash)
                progressed = True
                summary["accepted_count"] = int(summary["accepted_count"]) + 1
                if helper_name not in summary["accepted_helper_names"]:
                    summary["accepted_helper_names"].append(helper_name)
                if reused_existing_helper:
                    record_summary["reused_existing_helper"] = True
                    summary["duplicate_count"] = (
                        int(summary["duplicate_count"]) + 1
                    )
                inc("mini_proof_state_cache_seed_accepted", 1)
                summary["records"].append(record_summary)
                continue

            error_kind = str(status.get("error_kind") or "cache_seed_rejected")
            record_summary["rejection"] = error_kind
            if str(status.get("status") or "") == "retryable_error":
                summary["retryable_error_count"] = (
                    int(summary["retryable_error_count"]) + 1
                )
                if root_node is not None:
                    retain_pending_helper_acceptance_retry(
                        proof_state=proof_state,
                        node=root_node,
                        status=status,
                    )
                summary["records"].append(record_summary)
                summary["verdict"] = "cache_seed_acceptance_deferred"
                # The current candidate and its ordered, already-paid suffix
                # now live in the root helper-acceptance WAL. Never translate
                # verifier unavailability into cache rejection.
                return summary
            else:
                if root_node is not None:
                    root_node.pending_helper_acceptance = {}
                terminal_source_hashes.add(source_hash)
                summary["records"].append(record_summary)
        if not progressed:
            for record in next_pending:
                source_hash = str(record.get("source_hash") or "") or text_hash(
                    str(record.get("source") or "")
                )
                if source_hash in terminal_source_hashes:
                    continue
                terminal_source_hashes.add(source_hash)
                summary["records"].append(
                    {
                        "helper_name": str(record.get("name") or ""),
                        "cache_source_hash": source_hash,
                        "cache_lookup_tier": str(
                            record.get("_lookup_tier") or "same_theorem"
                        ),
                        "accepted": False,
                        "rejection": "cache_seed_retryable_not_resolved",
                    }
                )
            break
        pending = next_pending

    for record in pending:
        source_hash = str(record.get("source_hash") or "") or text_hash(
            str(record.get("source") or "")
        )
        if source_hash in accepted_source_hashes or source_hash in terminal_source_hashes:
            continue
        terminal_source_hashes.add(source_hash)
        summary["records"].append(
            {
                "helper_name": str(record.get("name") or ""),
                "cache_source_hash": source_hash,
                "cache_lookup_tier": str(record.get("_lookup_tier") or "same_theorem"),
                "accepted": False,
                "rejection": "cache_seed_passes_exhausted",
            }
        )

    rejected = max(
        0,
        len(candidates)
        - int(summary["accepted_count"])
        - int(summary["duplicate_count"]),
    )
    summary["rejected_count"] = rejected
    if rejected:
        inc("mini_proof_state_cache_seed_rejected", rejected)
    if int(summary["duplicate_count"]):
        inc("mini_proof_state_cache_seed_duplicates", int(summary["duplicate_count"]))
    if int(summary["name_collision_count"]):
        inc(
            "mini_proof_state_cache_seed_name_collisions",
            int(summary["name_collision_count"]),
        )
    summary["verdict"] = (
        "cache_seed_imported"
        if int(summary["accepted_count"]) > 0
        else "cache_seed_no_imports"
    )
    return summary


def _proof_state_helper_block(helper_name: str, target: str, proof: str) -> str:
    """Format a generated helper as one safe top-level Lean declaration."""

    proof_text = str(proof or "").strip()
    if (
        proof_text == "by"
        or proof_text.startswith("by ")
        or proof_text.startswith("by\n")
    ):
        return f"theorem {helper_name} : {target} := {proof_text}"
    return f"theorem {helper_name} : {target} :=\n{proof_text}"


def _with_turn_budget_footer(
    feedback: str,
    *,
    role: str,
    turn: int,
    max_turns: int,
) -> str:
    """Attach remaining-turn context to model-facing retry feedback."""
    try:
        turn_i = int(turn)
        max_i = int(max_turns)
    except Exception:
        return feedback
    if max_i <= 0:
        return feedback
    remaining = max(0, max_i - turn_i)
    return (
        feedback.rstrip()
        + "\n\n"
        + f"Turn budget: {role} turn {turn_i}/{max_i} was used; "
        + f"{remaining} turn(s) remain in this phase. Keep solving the "
        + "mathematics first, then repair the Lean code."
    )


def _decl_application_failure_is_retryable(error_kind: str) -> bool:
    """Whether a decl probe failure should keep the declaration pending."""

    normalized = str(error_kind or "").strip().lower()
    if not normalized:
        return False
    if normalized == "decl_application_ping_deferred":
        return True
    if (
        "timeout" in normalized
        or "elapsed_budget_exhausted" in normalized
        or "deadline_deferred" in normalized
        or "enclosing_deadline" in normalized
    ):
        return True
    return normalized in {
        "infra_failure",
        "runner_exception",
        "infrastructure_error",
        "lean_infra_error",
    }


def _decl_application_failure_is_context_sensitive(
    error_kind: str,
    error_text: str,
) -> bool:
    """Whether a semantic miss may change after helpers/preamble change."""

    normalized = str(error_kind or "").strip().lower()
    diagnostic = str(error_text or "").strip().lower()
    return normalized == "unknown_identifier" or any(
        token in normalized or token in diagnostic
        for token in (
            "instance",
            "synthes",
            "typeclass",
            "unification",
            "metavariable",
        )
    )


async def _try_proof_state_decl_closure(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    turn: int,
    timeout_s: float,
    max_decls: int,
    max_residual_goals: int = 4,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    deadline_monotonic: float = 0.0,
) -> Tuple[str, List[Dict[str, Any]]]:
    """Probe retrieved declarations directly against a scheduled child node."""

    max_decl_count = max(0, int(max_decls or 0))
    all_decl_names = proof_state_decl_application_candidate_names(node)
    # Boundary-exact context identity FIRST — before tried/pending selection
    # and every early return. Hash the EXACT preamble + final helper blocks
    # this batch would hand to apply_decl_to_goal (residual preamble,
    # verified helpers, forced-context merge); a mismatch with the node's
    # recorded hash means the tried memory belongs to a different Lean
    # context, so clear it and let pending selection see the retriable set.
    batch_context_hash = proof_state_decl_application_context_hash(conv, dossier)
    if proof_state_begin_decl_application_batch(
        node, batch_context_hash
    ):
        record_dossier_lean_attempt_event(
            dossier,
            lane="proof_state_decl_application",
            event="context_changed_retry_granted",
            attempt={"node_id": getattr(node, "node_id", "")},
        )
    tried_decl_names = {
        str(item or "").strip()
        for item in list(getattr(node, "decl_application_tried_decl_names", []) or [])
        if str(item or "").strip()
    }
    pending_decl_names = proof_state_decl_application_pending_names(node)
    context_replay_names = {
        str(item or "").strip()
        for item in list(
            getattr(node, "decl_application_context_replay_decl_names", []) or []
        )
        if str(item or "").strip()
    }
    raw_last_replay_turn = getattr(
        node, "decl_application_last_context_replay_turn", -1
    )
    try:
        last_context_replay_turn = int(raw_last_replay_turn)
    except (TypeError, ValueError):
        last_context_replay_turn = -1
    fresh_candidates = [
        name
        for name in pending_decl_names
        if name not in context_replay_names
    ]
    replay_candidates = []
    if last_context_replay_turn != int(turn):
        replay_candidates = [
            name
            for name in pending_decl_names
            if name in context_replay_names
        ][:1]
    candidate_pool = [*fresh_candidates, *replay_candidates]
    decl_names = candidate_pool[:max_decl_count]
    if not decl_names:
        return "", []
    timeout = float(timeout_s or 0.0)
    if timeout <= 0.0:
        return "", []
    residual_goal_limit = max(0, int(max_residual_goals or 0))
    full_decl_application_signature = text_hash(
        "\n".join(
            [
                *all_decl_names,
                f"residual_goal_limit={residual_goal_limit}",
            ]
        )
    )
    batch_decl_application_signature = text_hash(
        "\n".join(
            [
                *decl_names,
                f"residual_goal_limit={residual_goal_limit}",
            ]
        )
    )

    def _decl_application_record_signature() -> str:
        attempted = set(tried_decl_names)
        attempted.update(decl_names)
        if all(name in attempted for name in all_decl_names):
            return full_decl_application_signature
        return batch_decl_application_signature

    def _mark_decl_application_tried(decl_name: str) -> None:
        name = str(decl_name or "").strip()
        if not name:
            return
        tried = getattr(node, "decl_application_tried_decl_names", None)
        if not isinstance(tried, list):
            tried = []
            node.decl_application_tried_decl_names = tried
        if name not in tried:
            tried.append(name)
        tried_decl_names.add(name)
        replay_names = getattr(
            node, "decl_application_context_replay_decl_names", None
        )
        if isinstance(replay_names, list):
            replay_names[:] = [
                item for item in replay_names if str(item or "").strip() != name
            ]
        _clear_decl_application_retry(name)

    def _mark_decl_application_structural_miss(decl_name: str) -> None:
        name = str(decl_name or "").strip()
        if not name:
            return
        structural = getattr(
            node, "decl_application_structural_miss_decl_names", None
        )
        if not isinstance(structural, list):
            structural = []
            node.decl_application_structural_miss_decl_names = structural
        if name not in structural:
            structural.append(name)
            del structural[:-48]
        tried = getattr(node, "decl_application_tried_decl_names", None)
        if isinstance(tried, list):
            tried[:] = [
                item for item in tried if str(item or "").strip() != name
            ]
        replay_names = getattr(
            node, "decl_application_context_replay_decl_names", None
        )
        if isinstance(replay_names, list):
            replay_names[:] = [
                item for item in replay_names if str(item or "").strip() != name
            ]
        tried_decl_names.discard(name)
        _clear_decl_application_retry(name)

    def _decl_application_retry_key(decl_name: str) -> str:
        return "\n".join(
            [
                str(decl_name or "").strip(),
                f"residual_goal_limit={residual_goal_limit}",
            ]
        )

    def _retry_keys() -> List[str]:
        retry_keys = getattr(node, "decl_application_retry_keys", None)
        if not isinstance(retry_keys, list):
            retry_keys = []
            node.decl_application_retry_keys = retry_keys
        return retry_keys

    def _mark_decl_application_retry(decl_name: str) -> None:
        key = _decl_application_retry_key(decl_name)
        if not key.strip():
            return
        retry_keys = _retry_keys()
        if key not in retry_keys:
            retry_keys.append(key)
            del retry_keys[:-24]

    def _clear_decl_application_retry(decl_name: str) -> None:
        name = str(decl_name or "").strip()
        if not name:
            return
        retry_keys = _retry_keys()
        prefix = f"{name}\n"
        retry_keys[:] = [
            key
            for key in retry_keys
            if str(key or "").strip() and not str(key or "").startswith(prefix)
        ]

    def _decl_application_already_retried(decl_name: str) -> bool:
        return _decl_application_retry_key(decl_name) in set(_retry_keys())

    attempts: List[Dict[str, Any]] = []
    record_dossier_lean_attempt_event(
        dossier,
        lane="proof_state_decl_application",
        event="portfolio",
        attempt={"candidate_count": len(decl_names)},
    )
    for index, decl_name in enumerate(decl_names, 1):
        operation_timeout = _fully_funded_operation_timeout(
            timeout,
            deadline_monotonic,
        )
        if operation_timeout <= 0.0:
            if float(deadline_monotonic or 0.0) > 0.0:
                attempts.append(
                    {
                        "decl_name": decl_name,
                        "applicable": False,
                        "closed": False,
                        "remaining_goal_count": 0,
                        "proof_stub": "",
                        "error_kind": "enclosing_deadline_deferred",
                        "deferred_before_launch": True,
                    }
                )
            break
        is_context_replay = decl_name in context_replay_names
        if is_context_replay:
            node.decl_application_last_context_replay_turn = int(turn)
        record_dossier_lean_attempt_event(
            dossier,
            lane="proof_state_decl_application",
            event="started",
            attempt={"decl_name": decl_name, "index": index},
        )
        full_portfolio_probe = _decl_application_already_retried(decl_name)
        decl_probe_events: List[Dict[str, Any]] = []

        def observe_decl_probe(raw_event: Dict[str, Any]) -> None:
            if len(decl_probe_events) >= 32 or not isinstance(raw_event, Mapping):
                return
            event = str(raw_event.get("event", "") or "").strip().lower()
            probe_stage = str(
                raw_event.get("probe_stage", "") or ""
            ).strip().lower()
            if event not in {"started", "finished"}:
                return
            if probe_stage not in {"baseline", "stub", "type_lookup"}:
                return

            def finite_nonnegative_float(key: str) -> Optional[float]:
                try:
                    value = float(raw_event.get(key))
                except (TypeError, ValueError):
                    return None
                if not math.isfinite(value):
                    return None
                return max(0.0, value)

            try:
                stub_index = max(0, int(raw_event.get("stub_index", 0) or 0))
            except (TypeError, ValueError):
                stub_index = 0
            normalized: Dict[str, Any] = {
                "event": event,
                "probe_stage": probe_stage,
                "stub_index": stub_index,
                "proof_stub": str(raw_event.get("proof_stub", "") or "")[:240],
            }
            for key in (
                "hard_timeout_s",
                "fast_fail_timeout_s",
                "elapsed_s",
            ):
                value = finite_nonnegative_float(key)
                if value is not None:
                    normalized[key] = value
            if event == "finished":
                normalized["error_kind"] = str(
                    raw_event.get("error_kind", "") or ""
                )[:80]
                normalized["applicable"] = bool(
                    raw_event.get("applicable", False)
                )
                try:
                    normalized["remaining_goal_count"] = max(
                        0,
                        int(raw_event.get("remaining_goal_count", 0) or 0),
                    )
                except (TypeError, ValueError):
                    normalized["remaining_goal_count"] = 0
            decl_probe_events.append(normalized)

        def decl_probe_telemetry() -> Dict[str, Any]:
            active: Dict[Tuple[str, int], Dict[str, Any]] = {}
            finished: List[Dict[str, Any]] = []
            for event in decl_probe_events:
                key = (
                    str(event.get("probe_stage", "") or ""),
                    int(event.get("stub_index", 0) or 0),
                )
                if event.get("event") == "started":
                    active[key] = event
                elif event.get("event") == "finished":
                    active.pop(key, None)
                    finished.append(event)
            lease_event = next(reversed(active.values()), None)
            if lease_event is None and finished:
                lease_event = max(
                    finished,
                    key=lambda item: float(item.get("elapsed_s", 0.0) or 0.0),
                )
            lease_summary: Dict[str, Any] = {}
            if lease_event is not None:
                for key in (
                    "probe_stage",
                    "stub_index",
                    "proof_stub",
                    "hard_timeout_s",
                    "fast_fail_timeout_s",
                ):
                    if key in lease_event:
                        lease_summary[key] = lease_event[key]
            slowest_elapsed_s = max(
                (
                    float(event.get("elapsed_s", 0.0) or 0.0)
                    for event in finished
                ),
                default=0.0,
            )
            return {
                "full_portfolio_probe": full_portfolio_probe,
                "probe_event_count": len(decl_probe_events),
                "lease_consuming_probe_stub": lease_summary,
                "slowest_probe_elapsed_s": slowest_elapsed_s,
            }

        async def run_decl_application() -> Any:
            apply_decl = lean.apply_decl_to_goal
            try:
                apply_decl_parameters = inspect.signature(apply_decl).parameters
                supports_probe_observer = (
                    "probe_observer" in apply_decl_parameters
                    or any(
                        parameter.kind is inspect.Parameter.VAR_KEYWORD
                        for parameter in apply_decl_parameters.values()
                    )
                )
            except (TypeError, ValueError):
                # Opaque/extension callables keep the legacy contract. Do not
                # risk breaking proof search merely to attach telemetry.
                supports_probe_observer = False
            apply_kwargs: Dict[str, Any] = {
                "preamble_override": _proof_state_residual_preamble(conv),
                "lemmas": _proof_state_residual_lemmas(
                    conv,
                    _proof_state_verified_helper_blocks(dossier),
                ),
                "timeout_s": operation_timeout,
                "ping_only": not full_portfolio_probe,
                "ping_timeout_s": (
                    min(8.0, operation_timeout)
                    if not full_portfolio_probe
                    else 0.0
                ),
            }
            if supports_probe_observer:
                apply_kwargs["probe_observer"] = observe_decl_probe
            return await apply_decl(
                node.target,
                decl_name,
                **apply_kwargs,
            )

        try:
            result = await _await_serialized_lean_operation(
                lean,
                run_decl_application,
                timeout_s=operation_timeout,
                deadline_monotonic=deadline_monotonic,
                operation_label="proof_state_decl_application",
            )
        except asyncio.CancelledError:
            telemetry = decl_probe_telemetry()
            record_dossier_lean_attempt_event(
                dossier,
                lane="proof_state_decl_application",
                event="finished",
                attempt={
                    "ok": False,
                    "decl_name": decl_name,
                    "index": index,
                    "error_type": "cancelled",
                    "exception": "CancelledError",
                    "cancelled": True,
                    **telemetry,
                },
            )
            raise
        except _LeanOperationDeadline as exc:
            result = {
                "decl_name": decl_name,
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": "timeout",
                "error": str(exc) or "strict Lean deadline exhausted",
                "decl_type": "",
            }
        except Exception as exc:
            result = {
                "decl_name": decl_name,
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": type(exc).__name__,
                "error": str(exc),
                "decl_type": "",
            }
        # A Lean adapter may ignore its timeout or suppress cancellation.
        telemetry = decl_probe_telemetry()
        record_dossier_lean_attempt_event(
            dossier,
            lane="proof_state_decl_application",
            event="finished",
            attempt={
                "ok": bool(result.get("applicable", False)),
                "decl_name": decl_name,
                "index": index,
                "error_type": str(result.get("error_kind", "") or ""),
                "diagnostic": str(result.get("error", "") or ""),
                "exception": (
                    str(result.get("error_kind", "") or "")
                    if str(result.get("error_kind", "") or "").endswith("Error")
                    else ""
                ),
                **telemetry,
            },
        )

        applicable = bool(result.get("applicable", False))
        proof_stub = str(result.get("proof_stub", "") or "").strip()
        remaining_goals = list(result.get("remaining_goals", []) or [])
        error_kind = str(result.get("error_kind", "") or "")
        error_text = str(result.get("error", "") or "")
        ping_error_kind = str(result.get("ping_error_kind", "") or "")
        decl_type = str(result.get("decl_type", "") or "").strip()
        if applicable and proof_stub and is_answer_unsafe_statement_text(
            proof_stub,
            suppress_solution_placeholders=bool(
                getattr(conv, "suppress_solution_placeholders", True)
            ),
        ):
            applicable = False
            proof_stub = ""
            remaining_goals = []
            error_kind = "answer_unsafe_proof_stub"
            error_text = (
                "Lean suggested a proof stub that references a `_solution` "
                "placeholder, so the deterministic decl probe was rejected."
            )
        error_text_is_lean_diagnostic = _decl_application_error_is_lean_diagnostic(
            error_kind,
            error_text,
        )
        retryable_failure = _decl_application_failure_is_retryable(error_kind)
        if (
            str(ping_error_kind or "").strip().lower()
            in {
                "invalid_decl_name",
                "type_mismatch",
                "no_applicable_probe",
                "no_residual_goals",
                "no_residuals",
            }
            and not _decl_application_failure_is_context_sensitive(
                ping_error_kind,
                error_text,
            )
        ):
            retryable_failure = False
        already_retried_decl_application = bool(
            retryable_failure
            and _decl_application_already_retried(decl_name)
        )
        dossier.record_decl_application(
            turn_index=turn,
            tool_call_index=1000 + index,
            statement=node.target,
            decl_name=decl_name,
            applicable=applicable,
            proof_stub=proof_stub,
            remaining_goals=remaining_goals,
            error_kind=error_kind,
            error_text=error_text,
            error_text_is_lean_diagnostic=error_text_is_lean_diagnostic,
            decl_type=decl_type,
        )
        attempt_record = {
            "decl_name": decl_name,
            "applicable": applicable,
            "closed": bool(applicable and proof_stub and not remaining_goals),
            "remaining_goal_count": len(remaining_goals),
            "proof_stub": proof_stub[:240],
            "error_kind": error_kind,
            "retryable_failure": retryable_failure,
            "retry_exhausted": already_retried_decl_application,
            "context_replay": is_context_replay,
            **telemetry,
        }
        definitive_kind = str(ping_error_kind or error_kind).strip().lower()
        structural_miss = bool(
            not applicable
            and not proof_stub
            and not remaining_goals
            and not retryable_failure
            and not _decl_application_failure_is_context_sensitive(
                error_kind,
                error_text,
            )
            and (
                definitive_kind
                in {
                    "invalid_decl_name",
                    "type_mismatch",
                    "no_applicable_probe",
                    "no_residual_goals",
                    "no_residuals",
                }
            )
        )
        attempt_record["structural_miss"] = structural_miss
        if structural_miss:
            _mark_decl_application_structural_miss(decl_name)
            attempts.append(attempt_record)
            continue
        if applicable and proof_stub and remaining_goals:
            residual_goal_limit = max(0, int(max_residual_goals or 0))
            residual_source = f"decl_application:{decl_name}"
            spawned, residual_goal_count, receipt_status = (
                await _extract_and_spawn_typed_residual_goals(
                    lean=lean,
                    proof_state=proof_state,
                    parent_node=node,
                    parent_proof_stub=proof_stub,
                    source=residual_source,
                    preamble=_proof_state_residual_preamble(conv),
                    lemmas=_proof_state_residual_lemmas(
                        conv,
                        _proof_state_verified_helper_blocks(dossier),
                    ),
                    timeout_s=timeout,
                    max_goals=residual_goal_limit,
                    deadline_monotonic=deadline_monotonic,
                    origin_metadata={
                        "kind": "decl_application",
                        "decl_name": decl_name,
                        "turn_index": turn,
                        "decl_application_signature": batch_context_hash,
                    },
                )
            )
            node = proof_state.nodes.get(node.node_id, node)
            attempt_record["remaining_goal_count"] = residual_goal_count
            if receipt_status.endswith("_deferred"):
                attempt_record.update(
                    {
                        "closed": False,
                        "error_kind": receipt_status,
                        "retryable_failure": True,
                        "retry_exhausted": False,
                    }
                )
                _mark_decl_application_retry(decl_name)
                attempts.append(attempt_record)
                continue
            if receipt_status == "residual_attestation_goal_cap_exceeded":
                reason = "decl_application_residual_goal_cap_exceeded"
                attempt_record.update(
                    {
                        "closed": False,
                        "error_kind": reason,
                        "residual_goal_count": residual_goal_count,
                        "residual_goal_limit": residual_goal_limit,
                    }
                )
                proof_state.record_graph_frontier_error(
                    {
                        "source": f"decl_application:{decl_name}",
                        "parent_node_id": node.node_id,
                        "error_type": reason,
                        "residual_goal_count": residual_goal_count,
                        "residual_goal_limit": residual_goal_limit,
                    }
                )
                proof_state.record_transition(
                    node_id=node.node_id,
                    source=f"decl_application:{decl_name}",
                    error_type=reason,
                    action=node.action,
                    blocker=(
                        f"{decl_name} left {residual_goal_count} residual "
                        f"goal(s), exceeding configured limit {residual_goal_limit}"
                    ),
                    phase="proof_state_decl_application",
                    turn_index=turn,
                    payload={
                        "decl_name": decl_name,
                        "residual_goal_count": residual_goal_count,
                        "residual_goal_limit": residual_goal_limit,
                        },
                    )
                if _decl_application_already_retried(decl_name):
                    _mark_decl_application_tried(decl_name)
                else:
                    _mark_decl_application_retry(decl_name)
                attempts.append(attempt_record)
                continue
            if receipt_status == "residual_attestation_closed_goal":
                # The typed replay is authoritative if a human diagnostic
                # parser claimed stale residuals for an actually closed stub.
                remaining_goals = []
                attempt_record.update(
                    {"closed": True, "remaining_goal_count": 0, "error_kind": ""}
                )
            elif receipt_status != "residual_attestation_admitted" or not spawned:
                reason = f"decl_application_{receipt_status}"
                attempt_record.update({"closed": False, "error_kind": reason})
                proof_state.record_graph_frontier_error(
                    {
                        "source": residual_source,
                        "parent_node_id": node.node_id,
                        "error_type": reason,
                        "residual_goal_count": residual_goal_count,
                    }
                )
                _mark_decl_application_tried(decl_name)
                attempts.append(attempt_record)
                continue
            else:
                attempt_record["spawned_child_nodes"] = spawned
                node.action = "assemble_from_children"
                node.blocker = f"{decl_name} left {residual_goal_count} subgoal(s)"
                node.priority = proof_state._priority(node)
                _mark_decl_application_tried(decl_name)
        attempts.append(attempt_record)
        if not applicable or not proof_stub or remaining_goals:
            if retryable_failure and not already_retried_decl_application:
                _mark_decl_application_retry(decl_name)
            else:
                _mark_decl_application_tried(decl_name)
            continue

        helper_name = proof_state.helper_name_for_node(node, dossier)
        proof_code = _proof_from_decl_application_stub(proof_stub)
        if not proof_code:
            _mark_decl_application_tried(decl_name)
            continue
        helper_block = _proof_state_helper_block(
            helper_name,
            node.target,
            proof_code,
        )
        # Applying a declaration and certifying the resulting helper are two
        # separately bounded Lean operations. Preserve the successful first
        # operation before testing admission for the second, so a one-operation
        # action quantum advances to acceptance instead of replaying the same
        # declaration forever.
        staged_acceptance = stage_pending_helper_acceptance(
            conv=conv,
            dossier=dossier,
            node=node,
            helper_block=helper_block,
            source=f"decl_application:{decl_name}",
            context_hash=batch_context_hash,
            continuation={
                "kind": "decl_application",
                "decl_name": decl_name,
                "decl_application_signature": batch_context_hash,
            },
        )
        if not staged_acceptance:
            attempt_record.update(
                {
                    "closed": False,
                    "error_kind": "pending_helper_acceptance_owned",
                    "deferred_before_launch": True,
                    "retryable_failure": True,
                    "retry_exhausted": False,
                }
            )
            break
        _mark_decl_application_tried(decl_name)
        accept_status: Dict[str, Any] = {}
        acceptance_timeout = _fully_funded_operation_timeout(
            timeout,
            deadline_monotonic,
        )
        if acceptance_timeout <= 0.0:
            if float(deadline_monotonic or 0.0) > 0.0:
                attempt_record.update(
                    {
                        "closed": False,
                        "error_kind": "enclosing_deadline_deferred",
                        "deferred_before_launch": True,
                        "retryable_failure": True,
                        "retry_exhausted": False,
                    }
                )
            break
        accepted = await _accept_proof_state_helper(
            lean=lean,
            conv=conv,
            dossier=dossier,
            helper_block=helper_block,
            phase="proof_state_decl_application",
            turn_index=turn,
            timeout_s=acceptance_timeout,
            proof_cache=proof_cache,
            proof_state=proof_state,
            status_out=accept_status,
            target_statement=node.target,
            deadline_monotonic=deadline_monotonic,
        )
        if accepted:
            node.pending_helper_acceptance = {}
            record_dossier_lean_attempt_event(
                dossier,
                lane="proof_state_decl_application",
                event="certificate_accepted",
                attempt={"decl_name": decl_name, "helper_name": helper_name},
            )
            _mark_decl_application_tried(decl_name)
            proof_state.record_decl_application_result(
                node_id=node.node_id,
                ok=True,
                attempt_count=len(attempts),
                exit_reason=f"closed_by:{decl_name}",
                helper_name=helper_name,
                decl_application_signature=_decl_application_record_signature(),
            )
            return helper_name, attempts
        accept_error_kind = str(accept_status.get("error_kind") or "")
        accept_retryable = bool(
            str(accept_status.get("status") or "")
            in {"retryable_error", "cancelled"}
            or _decl_application_failure_is_retryable(accept_error_kind)
        )
        if accept_status:
            attempt_record["acceptance_status"] = dict(accept_status)
            attempt_record["closed"] = False
            attempt_record["error_kind"] = (
                accept_error_kind
                or str(accept_status.get("status") or "")
                or "proof_state_helper_rejected"
            )
            attempt_record["retryable_failure"] = accept_retryable
            attempt_record["retry_exhausted"] = False
        if accept_retryable:
            retain_pending_helper_acceptance_retry(
                proof_state=proof_state,
                node=node,
                status=accept_status,
            )
            _mark_decl_application_retry(decl_name)
            # One paid candidate owns the singular durable acceptance frame.
            # Rotate only after its verifier retry yields; a later declaration
            # in this batch must never overwrite it.
            break
        else:
            node.pending_helper_acceptance = {}
            _mark_decl_application_tried(decl_name)

    if attempts:
        spawned_child_nodes = [
            child_id
            for attempt in attempts
            for child_id in list(attempt.get("spawned_child_nodes") or [])
            if str(child_id or "").strip()
        ]
        if spawned_child_nodes:
            decl_application_signature = _decl_application_record_signature()
            if str(decl_application_signature or "").strip():
                node.decl_application_signature = decl_application_signature
            attempt_count = max(0, int(len(attempts) or 0))
            node.decl_application_attempts += attempt_count
            node.close_attempts += attempt_count
            node.action = "assemble_from_children"
            node.priority = proof_state._priority(node)
            return "", attempts
        last = attempts[-1]
        reason = str(last.get("error_kind") or "decl_application_not_closed")
        if bool(last.get("deferred_before_launch")) or any(
            bool(attempt.get("retryable_failure"))
            and not bool(attempt.get("retry_exhausted"))
            for attempt in attempts
        ):
            # Infrastructure/deadline outcomes are observations, not
            # mathematical failures. Keep every affected declaration pending
            # and leave mathematical failure counters untouched.
            node.blocker = reason
            retry_signature = _decl_application_record_signature()
            if str(retry_signature or "").strip():
                # Version the frontier receipt once so a first retryable
                # infrastructure result is distinguishable from the request
                # that produced it. This is not a consumed/failed attempt;
                # subsequent retention is explicit in ChildClosureAction.
                node.decl_application_signature = retry_signature
            return "", attempts
        proof_state.record_decl_application_result(
            node_id=node.node_id,
            ok=False,
            attempt_count=len(attempts),
            exit_reason=reason,
            decl_application_signature=_decl_application_record_signature(),
        )
    return "", attempts


def _proof_state_child_applications(child: ProofStateNode) -> List[str]:
    helper = str(child.proved_helper_name or "").strip()
    if not helper:
        return []
    args: List[str] = []
    if child.goal is not None:
        for hyp in child.goal.local_hypotheses:
            name = str(hyp.get("name") or "").strip()
            if name and _LEAN_LOCAL_IDENT_RE.fullmatch(name):
                term = str(child.local_argument_terms.get(name) or name).strip()
                args.append(term if term else name)
    if not args:
        return [helper]
    candidates = [f"({helper} {' '.join(args)})"]
    fallback_args = ["(by assumption)" if arg == "_" else arg for arg in args]
    if fallback_args != args:
        candidates.append(f"({helper} {' '.join(fallback_args)})")
    candidates.append(f"({helper} {' '.join('(by assumption)' for _ in args)})")
    out: List[str] = []
    seen: Set[str] = set()
    for candidate in candidates:
        if candidate and candidate not in seen:
            seen.add(candidate)
            out.append(candidate)
    return out


def _assembly_proof_candidates(
    proof_stub: str,
    children: Sequence[ProofStateNode],
    *,
    source: str = "",
) -> List[str]:
    raw_stub = str(proof_stub or "").strip()
    typed_residual_route = proof_state_source_requires_residual_goal_attestation(
        source
    )
    if (
        raw_stub
        and not raw_stub.startswith("by")
        and typed_residual_route
    ):
        # Typed extraction interprets non-tactic terms as
        # ``refine (<term>)`` so holes become residual goals. Assembly must
        # replay that exact semantics; treating the term as a tactic changes
        # the certified parent route.
        stub = f"by\n  refine ({raw_stub})"
    else:
        stub = _proof_from_decl_application_stub(raw_stub)
    if not stub:
        return []
    stub_lines = [line.rstrip() for line in stub.splitlines()]
    if stub_lines and stub_lines[0].strip() == "by":
        body_lines = stub_lines[1:]
    else:
        body_lines = stub_lines
    child_app_variants = [
        _proof_state_child_applications(child)
        for child in children
        if child.proved_helper_name
    ]
    child_app_variants = [variants for variants in child_app_variants if variants]
    if not child_app_variants:
        return []

    indented_body = [
        ("  " + line.strip()) if line.strip() else ""
        for line in body_lines
    ]
    app_sets: List[List[str]] = []
    for variant_index in (0, 1):
        apps = [
            variants[min(variant_index, len(variants) - 1)]
            for variants in child_app_variants
        ]
        if apps not in app_sets:
            app_sets.append(apps)
    candidates: List[str] = []
    for child_apps in app_sets:
        bullet_lines = [f"  · exact {app}" for app in child_apps]
        simpa_bullet_lines = [f"  · simpa using {app}" for app in child_apps]
        apply_bullet_lines = [f"  · apply {app}" for app in child_apps]
        apply_assumption_lines = [
            f"  · apply {app} <;> assumption" for app in child_apps
        ]
        exact_candidates = [
            "by\n" + "\n".join(indented_body + bullet_lines),
            "by\n" + "\n".join(indented_body + simpa_bullet_lines),
        ]
        apply_candidates = [
            "by\n" + "\n".join(indented_body + apply_assumption_lines),
            "by\n" + "\n".join(indented_body + apply_bullet_lines),
        ]
        # Closed residual helpers quantify the complete local context,
        # including variables irrelevant to the target. ``apply``
        # reinstantiates those binders and ``assumption`` discharges the
        # original local terms without guessing an application arity from
        # pretty-printed target text. Preserve the established cheaper exact
        # ordering for legacy, non-attested assembly routes.
        candidates.extend(
            apply_candidates + exact_candidates
            if typed_residual_route
            else exact_candidates + apply_candidates
        )
    return [candidate for candidate in candidates if candidate.strip() != "by"]


async def _try_proof_state_parent_assembly(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    turn: int,
    timeout_s: float,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    target_assembly_ids: Optional[Sequence[str]] = None,
    required_child_node_ids: Optional[Sequence[str]] = None,
    deadline_monotonic: float = 0.0,
) -> Tuple[str, List[Dict[str, Any]]]:
    """Compose a parent node from a verified decl/tactic stub plus child helpers."""

    if bool(getattr(node, "falsified", False)):
        proof_state.positive_close_blocked_by_falsification(
            node,
            source="assembly_entry",
            phase="proof_state_parent_assembly",
            turn_index=turn,
        )
        return "", []
    if not node.assembly_attempt_groups:
        return "", []
    timeout = _fully_funded_operation_timeout(timeout_s, deadline_monotonic)
    if timeout <= 0.0:
        return "", []
    attempts: List[Dict[str, Any]] = []
    allowed_assembly_ids = {
        str(item or "").strip()
        for item in list(target_assembly_ids or ())
        if str(item or "").strip()
    }
    required_child_ids = {
        str(item or "").strip()
        for item in list(required_child_node_ids or ())
        if str(item or "").strip()
    }
    for group in node.assembly_attempt_groups:
        if allowed_assembly_ids and group.assembly_id not in allowed_assembly_ids:
            continue
        readiness_records = []
        readiness_getter = getattr(proof_state, "assembly_group_readiness", None)
        if callable(readiness_getter):
            try:
                readiness_records = readiness_getter(
                    node,
                    assembly_id=group.assembly_id,
                )
            except Exception:
                readiness_records = []
        readiness = readiness_records[0] if readiness_records else {}
        if readiness and not bool(readiness.get("ready")):
            if allowed_assembly_ids:
                try:
                    proof_state.assembly_selected_stale += 1
                except Exception:
                    pass
                attempts.append(
                    {
                        "assembly_id": group.assembly_id,
                        "candidate_index": 0,
                        "child_helpers": [],
                        "proof_preview": "",
                        "accepted": False,
                        "verdict": "selected_assembly_not_executable",
                        "reason": str(readiness.get("reason") or "not_ready"),
                        "unproved_child_node_ids": list(
                            readiness.get("unproved_child_node_ids") or []
                        ),
                        "missing_child_node_ids": list(
                            readiness.get("missing_child_node_ids") or []
                        ),
                    }
                )
            continue
        elif not readiness:
            # E4 (2026-05-09): try open groups OR previously-failed groups
            # whose child witnesses have changed since the last attempt.
            tryable = getattr(proof_state, "_group_tryable_for_attempt", None)
            if callable(tryable):
                if not tryable(group):
                    continue
            else:
                if group.status != "open" or group.attempt_count > 0:
                    continue
        if required_child_ids and not required_child_ids.intersection(group.child_node_ids):
            continue
        children = [
            proof_state.nodes[child_id]
            for child_id in group.child_node_ids
            if child_id in proof_state.nodes
        ]
        if not children or any(child.status != "proved" for child in children):
            continue
        # E4: capture the witness BEFORE attempting so a partial
        # interrupt still records what we tried with. After the loop,
        # ``last_attempt_witness`` reflects the configuration this
        # attempt observed; future tryable() calls compare against it.
        attempt_witness: Tuple[str, ...] = ()
        witness_getter = getattr(proof_state, "assembly_witness", None)
        if callable(witness_getter):
            try:
                attempt_witness = witness_getter(group)
            except Exception as exc:
                attempt_witness = ()
                proof_state.record_transition(
                    node_id=node.node_id,
                    source="assembler",
                    error_type="assembly_witness_failed",
                    action=node.action,
                    blocker=f"{type(exc).__name__}: {exc}",
                    phase="proof_state_parent_assembly",
                    turn_index=turn,
                    payload={"assembly_id": group.assembly_id},
                )
        # E4: re-open the group if it was previously failed but a
        # witness change made it tryable again. Status moves back to
        # "open" so the loop's normal terminal-status updates apply.
        # Track whether we re-opened so we can revert correctly if
        # ``_assembly_proof_candidates`` returns nothing actionable
        # (E4 F1 fix, adversarial review 2026-05-09). Reset
        # ``attempt_count`` to 0 so downstream budget consumers see a
        # fresh attempt counter for this witness (E4 F5 fix).
        was_previously_failed = group.status == "failed"
        previous_attempt_count = max(0, int(group.attempt_count or 0))
        if was_previously_failed:
            group.status = "open"
            group.attempt_count = 0
        candidates = _assembly_proof_candidates(
            group.proof_stub,
            children,
            source=group.source,
        )
        record_dossier_lean_attempt_event(
            dossier,
            lane="proof_state_assembly",
            event="portfolio",
            attempt={
                "candidate_count": len(candidates),
                "assembly_id": group.assembly_id,
            },
        )
        for index, proof in enumerate(candidates, 1):
            operation_timeout = _fully_funded_operation_timeout(
                timeout,
                deadline_monotonic,
            )
            if operation_timeout <= 0.0:
                break
            helper_name = proof_state.helper_name_for_node(node, dossier)
            helper_block = _proof_state_helper_block(
                helper_name,
                node.target,
                proof,
            )
            assembly_observer = dossier_lean_attempt_observer(
                dossier,
                "proof_state_assembly",
            )
            staged_acceptance = stage_pending_helper_acceptance(
                conv=conv,
                dossier=dossier,
                node=node,
                helper_block=helper_block,
                source=f"assembly:{group.assembly_id}",
                continuation={
                    "kind": "assembly",
                    "assembly_id": group.assembly_id,
                    "candidate_index": index,
                    "attempt_witness": list(attempt_witness),
                },
            )
            if not staged_acceptance:
                attempts.append(
                    {
                        "assembly_id": group.assembly_id,
                        "candidate_index": index,
                        "child_helpers": [
                            child.proved_helper_name for child in children
                        ],
                        "proof_preview": proof[:400],
                        "accepted": False,
                        "deferred_before_launch": True,
                        "retryable_infrastructure": True,
                        "verdict": "pending_helper_acceptance_owned",
                    }
                )
                return "", attempts
            acceptance_status: Dict[str, Any] = {}
            try:
                accepted = await _accept_proof_state_helper(
                    lean=lean,
                    conv=conv,
                    dossier=dossier,
                    helper_block=helper_block,
                    phase="proof_state_parent_assembly",
                    turn_index=turn,
                    timeout_s=operation_timeout,
                    proof_cache=proof_cache,
                    proof_state=proof_state,
                    target_statement=node.target,
                    status_out=acceptance_status,
                    deadline_monotonic=deadline_monotonic,
                    lean_attempt_observer=assembly_observer,
                )
            except asyncio.CancelledError:
                if not acceptance_status.get("status"):
                    notify_lean_attempt_observer(
                        assembly_observer,
                        "finished",
                        {
                            "ok": False,
                            "assembly_id": group.assembly_id,
                            "candidate_index": index,
                            "error_type": "cancelled",
                            "exception": "CancelledError",
                            "cancelled": True,
                        },
                    )
                raise
            except Exception as exc:
                if not acceptance_status.get("status"):
                    notify_lean_attempt_observer(
                        assembly_observer,
                        "finished",
                        {
                            "ok": False,
                            "assembly_id": group.assembly_id,
                            "candidate_index": index,
                            "error_type": "exception",
                            "diagnostic": str(exc),
                            "exception": type(exc).__name__,
                        },
                    )
                raise
            attempts.append(
                {
                    "assembly_id": group.assembly_id,
                    "candidate_index": index,
                    "child_helpers": [child.proved_helper_name for child in children],
                    "proof_preview": proof[:400],
                    "accepted": bool(accepted),
                    "acceptance_status": dict(acceptance_status),
                }
            )
            if accepted:
                node.pending_helper_acceptance = {}
                if proof_state.positive_close_blocked_by_falsification(
                    node,
                    source="assembly",
                    phase="proof_state_parent_assembly",
                    turn_index=turn,
                    helper_name=helper_name,
                ):
                    attempts[-1]["accepted"] = False
                    attempts[-1]["verdict"] = (
                        "assembly_acceptance_discarded_after_falsification"
                    )
                    return "", attempts
                group.status = "proved"
                group.attempt_count += index
                group.last_attempt_witness = attempt_witness
                proof_state.record_assembly_result(
                    node_id=node.node_id,
                    ok=True,
                    attempt_count=index,
                    exit_reason="assembled_from_children",
                    helper_name=helper_name,
                )
                return helper_name, attempts
            acceptance_error_kind = str(
                acceptance_status.get("error_kind") or ""
            )
            if bool(
                str(acceptance_status.get("status") or "")
                in {"retryable_error", "cancelled"}
                or _decl_application_failure_is_retryable(
                    acceptance_error_kind
                )
            ):
                # Preserve the exact assembly candidate and continuation. A
                # verifier outage cannot fail the mathematical assembly group.
                retain_pending_helper_acceptance_retry(
                    proof_state=proof_state,
                    node=node,
                    status=acceptance_status,
                )
                return "", attempts
            node.pending_helper_acceptance = {}
        if candidates:
            group.status = "failed"
            group.attempt_count += len(candidates)
            group.last_attempt_witness = attempt_witness
            proof_state.record_assembly_result(
                node_id=node.node_id,
                ok=False,
                attempt_count=len(candidates),
                exit_reason="parent assembly failed after child helpers proved",
            )
        else:
            # E4 follow-up (adversarial review 2026-05-09): no proof
            # candidates is still an observable assembler result. This
            # can happen after rehydration when children are marked
            # proved but lack helper names. Mark the group failed against
            # the current witness so it does not spin as ready forever;
            # a later helper-name change makes it retryable again.
            group.status = "failed"
            group.attempt_count = max(1, previous_attempt_count)
            group.last_attempt_witness = attempt_witness
            error_type = (
                "assembly_retry_no_candidates"
                if was_previously_failed or previous_attempt_count > 0
                else "assembly_no_candidates"
            )
            node.failed_attempts += 1
            node.close_attempts += 1
            node.assembly_attempts += 1
            node.action = (
                "assemble_from_children" if node.child_node_ids else "needs_llm_or_split"
            )
            node.blocker = (
                "assembly produced no proof candidates from the current "
                "proved-child witnesses"
            )
            attempts.append(
                {
                    "assembly_id": group.assembly_id,
                    "candidate_index": 0,
                    "child_helpers": [
                        str(child.proved_helper_name or "") for child in children
                    ],
                    "proof_preview": "",
                    "accepted": False,
                    "verdict": error_type,
                }
            )
            proof_state.record_transition(
                node_id=node.node_id,
                source="assembler",
                error_type=error_type,
                action=node.action,
                blocker=node.blocker,
                phase="proof_state_parent_assembly",
                turn_index=turn,
                payload={
                    "assembly_id": group.assembly_id,
                    "last_attempt_witness": list(attempt_witness),
                    "previous_attempt_count": previous_attempt_count,
                    "was_previously_failed": was_previously_failed,
                },
            )
            node.priority = proof_state._priority(node)
            proof_state._refresh_priorities_for_neighbors(node.node_id)
    return "", attempts


async def _try_proof_state_root_exact_helper(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    helper_name: str,
    turn: int,
    timeout_s: float,
    deadline_monotonic: float = 0.0,
) -> Tuple[bool, str, Dict[str, Any]]:
    """Certify the final root proof from a root-shaped helper theorem."""

    name = str(helper_name or "").strip()
    if not name:
        return False, "", {}
    proof = f"by\n  exact {name}"
    helper_source = str(
        getattr(getattr(dossier, "verified_helpers", {}).get(name), "source", "")
        or ""
    )
    record: Dict[str, Any] = {
        "phase": "proof_state_root_exact_helper",
        "turn_in_phase": turn,
        "helper_name": name,
        "helper_source_hash": text_hash(helper_source),
        "proof": proof,
        "accepted": False,
        "verdict": "tactic_rejected",
    }
    timeout = _fully_funded_operation_timeout(timeout_s, deadline_monotonic)
    if timeout <= 0.0:
        record["verdict"] = "budget_skipped"
        record["tactic_exit_reason"] = "root_exact_budget_disabled"
        record["root_exact_retryable"] = True
        return False, "", record
    # Building the transitive replay closure can itself be material work on a
    # large dossier.  Do it only after the enclosing deadline proves it can
    # fund the Lean operation this context exists to serve.
    replay_closure = getattr(dossier, "root_replay_helper_closure", None)
    if callable(replay_closure):
        helper_context = replay_closure(
            replay_helpers=[helper_source] if helper_source else [],
            support_helper_names=[name],
        )
    else:
        helper_context = merge_context_helpers(
            _proof_state_verified_helper_blocks(dossier),
            [helper_source] if helper_source else [],
        )
    async def run_check() -> Any:
        try:
            return await lean.check(
                conv.goal_statement,
                proof,
                helper_context,
                preamble_override=_proof_state_acceptance_preamble(conv),
                timeout_s=timeout,
                check_kind="proof_state_root_exact_helper",
            )
        except TypeError:
            try:
                return await lean.check(
                    conv.goal_statement,
                    proof,
                    helper_context,
                    preamble_override=_proof_state_acceptance_preamble(conv),
                    timeout_s=timeout,
                )
            except TypeError:
                return await lean.check(
                    conv.goal_statement,
                    proof,
                    helper_context,
                    preamble_override=_proof_state_acceptance_preamble(conv),
                )

    try:
        result = await _await_serialized_lean_operation(
            lean,
            run_check,
            timeout_s=timeout,
            deadline_monotonic=deadline_monotonic,
            operation_label="proof_state_root_exact_helper",
        )
    except _LeanOperationDeadline:
        record["error_type"] = "timeout"
        record["error"] = "strict Lean deadline exhausted"
        record["verdict"] = "root_exact_deadline_exhausted"
        record["root_exact_retryable"] = True
        return False, "", record
    except Exception as exc:
        record["error_type"] = type(exc).__name__
        record["error"] = f"{type(exc).__name__}: {exc}"
        record["verdict"] = "root_exact_retryable_error"
        record["root_exact_retryable"] = True
        return False, "", record
    record["lean_output"] = str(getattr(result, "output", "") or "")[:1000]
    lean_accepted = bool(getattr(result, "ok", False))
    record["accepted"] = lean_accepted
    record["lean_accepted"] = lean_accepted
    record["verdict"] = "solved" if lean_accepted else "tactic_rejected"
    if not lean_accepted:
        error_type = canonical_error_type(
            getattr(result, "parsed", None)
        ) or fallback_error_type_from_text(
            str(getattr(result, "output", "") or "")
        )
        if error_type:
            record["error_type"] = error_type
        if _decl_application_failure_is_retryable(error_type):
            record["verdict"] = "root_exact_retryable_error"
            record["root_exact_retryable"] = True
        return False, "", record
    contract_status = _root_exact_helper_contract_status(
        dossier,
        helper_name=name,
        target_statement=str(
            getattr(dossier, "root_statement", "")
            or getattr(conv, "goal_statement", "")
            or ""
        ),
    )
    record["route_assembly_contract_status"] = contract_status
    if not bool(contract_status.get("ready")):
        record["accepted"] = False
        record["verdict"] = "root_route_contract_not_ready"
        record["route_contract_verdict"] = str(contract_status.get("verdict") or "")
        dossier.record_attempt(
            phase="proof_state_root_exact_helper",
            turn_index=turn,
            proof=proof,
            helper_names=_helper_names_from_blocks(helper_context),
            verdict="root_route_contract_not_ready",
            metadata={
                "route_assembly_contract_status": contract_status,
                "helper_name": name,
            },
        )
        return False, "", record
    route_helper_names = [
        str(name or "").strip()
        for name in [
            contract_status.get("helper_name"),
            *list(contract_status.get("helper_names") or []),
        ]
        if str(name or "").strip()
    ]
    helper_names = route_helper_names or _helper_names_from_blocks(helper_context)
    replay_helpers = _root_replay_blocks_for_helper_names(
        dossier=dossier,
        helper_context=helper_context,
        helper_names=helper_names,
    )
    helper_names = _helper_names_from_blocks(replay_helpers) or helper_names
    from ensemble_prover.root_finalization import (
        finalize_root_solution,
        root_verification_certificate,
    )

    finalization = finalize_root_solution(
        dossier=dossier,
        proof_state=proof_state,
        proof=proof,
        replay_helpers=replay_helpers,
        helper_names=helper_names,
        phase="proof_state_root_exact_helper",
        turn_index=turn,
        route_id=str(contract_status.get("route_id") or ""),
        dependency_node_ids=tuple(
            str(node_id or "").strip()
            for node_id in list(
                contract_status.get("dependency_node_ids")
                or contract_status.get("required_node_ids")
                or []
            )
            if str(node_id or "").strip()
        ),
        dependency_helper_names=route_helper_names or helper_names,
        target_statement=str(
            getattr(dossier, "root_statement", "")
            or getattr(conv, "goal_statement", "")
            or ""
        ),
        require_route_contract=True,
        verification_certificate=root_verification_certificate(
            accepted=True,
            proof=proof,
            phase="proof_state_root_exact_helper",
            turn_index=turn,
            target_statement=str(
                getattr(dossier, "root_statement", "")
                or getattr(conv, "goal_statement", "")
                or ""
            ),
            replay_helpers=replay_helpers,
            helper_names=helper_names,
            source="proof_state_root_exact_helper",
        ),
        require_verification_certificate=True,
    )
    if not finalization.accepted:
        record["root_finalization_verdict"] = finalization.verdict
        return False, "", record
    return True, proof, record


def _reopen_root_after_failed_exact_helper(
    proof_state: ProofSearchState,
    root_record: Dict[str, Any],
) -> None:
    """Keep proof-state root honest when final root certification fails."""

    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return
    root.status = "open"
    root.action = "prove_or_assemble"
    root.proved_helper_name = ""
    root.successful_family = ""
    root.blocker = (
        "root exact helper certification failed: "
        + str(root_record.get("verdict") or "rejected")
    )
    if str(root_record.get("error") or "").strip():
        root.blocker += f" ({root_record['error']})"
    retryable = _root_exact_helper_failure_is_retryable(root_record)
    proof_state.record_transition(
        node_id=proof_state.root_node_id,
        source="root_exact_helper",
        error_type=(
            "root_exact_helper_retryable_error"
            if retryable
            else "root_exact_helper_rejected"
        ),
        action=root.action,
        blocker=root.blocker,
        phase=str(root_record.get("phase") or "proof_state_root_exact_helper"),
        turn_index=int(root_record.get("turn_in_phase") or 0),
        payload=dict(root_record),
    )
    if retryable:
        root.diagnostics.append(
            {
                "kind": "root_exact_helper_retryable_error",
                "helper_name": str(root_record.get("helper_name") or "").strip(),
                "helper_source_hash": str(
                    root_record.get("helper_source_hash") or ""
                ).strip(),
                "verdict": str(root_record.get("verdict") or "retryable_error"),
                "error": str(root_record.get("error") or ""),
                "error_type": str(root_record.get("error_type") or ""),
            }
        )
        del root.diagnostics[:-24]
        root.priority = proof_state._priority(root)
        return
    helper_name = str(root_record.get("helper_name") or "").strip()
    helper_source_hash = str(root_record.get("helper_source_hash") or "").strip()
    rejection_key = _root_exact_helper_rejection_key(helper_name, helper_source_hash)
    if rejection_key:
        rejected_keys = list(getattr(root, "root_exact_rejected_helper_keys", []) or [])
        if rejection_key not in rejected_keys:
            root.root_exact_rejected_helper_keys.append(rejection_key)
            del root.root_exact_rejected_helper_keys[:-4096]
            root.diagnostics.append(
                {
                    "kind": "root_exact_helper_rejected",
                    "helper_name": helper_name,
                    "helper_source_hash": helper_source_hash,
                    "verdict": str(root_record.get("verdict") or "rejected"),
                    "error": str(root_record.get("error") or ""),
                }
            )
            del root.diagnostics[:-24]
    root.priority = proof_state._priority(root)


def _root_exact_helper_failure_is_retryable(root_record: Dict[str, Any]) -> bool:
    """Whether a failed root-exact certification should keep the helper live."""

    if bool(root_record.get("root_exact_retryable")):
        return True
    if bool(root_record.get("lean_accepted")):
        return True
    verdict = str(root_record.get("verdict") or "").strip().lower()
    if verdict in {
        "budget_skipped",
        "root_exact_retryable_error",
        "root_route_contract_not_ready",
    }:
        return True
    if str(root_record.get("root_finalization_verdict") or "").strip():
        return True
    error_type = str(root_record.get("error_type") or "").strip()
    if _decl_application_failure_is_retryable(error_type):
        return True
    error_text = str(root_record.get("error") or "").strip()
    return _decl_application_failure_is_retryable(error_text)


def _retire_failed_root_exact_helper_routes(
    dossier: ProofDossier,
    root_record: Dict[str, Any],
) -> int:
    """Retire graph root-exact routes after a durable helper rejection."""

    if not root_record or _root_exact_helper_failure_is_retryable(root_record):
        return 0
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return 0
    helper_name = str(root_record.get("helper_name") or "").strip()
    if not helper_name:
        return 0
    helper_id = str(
        getattr(graph, "helper_name_to_node_id", {}).get(helper_name) or ""
    ).strip()
    if not helper_id:
        try:
            helper_id = str(graph.helper_node_id(helper_name) or "").strip()
        except Exception:
            helper_id = ""
    retired = 0
    retire_route = getattr(graph, "retire_strategy_route", None)
    if not callable(retire_route):
        return 0
    for route in list(graph.nodes_by_kind("strategy_route")):
        metadata = dict(getattr(route, "metadata", {}) or {})
        contract = metadata.get("route_assembly_contract")
        contract_metadata = (
            dict(contract.get("metadata") or {}) if isinstance(contract, dict) else {}
        )
        route_source = str(
            contract_metadata.get("source") or metadata.get("source") or ""
        ).strip()
        if route_source != "root_exact_helper":
            continue
        route_helper_name = str(
            contract_metadata.get("root_exact_helper_name")
            or metadata.get("root_exact_helper_name")
            or ""
        ).strip()
        route_helper_id = str(
            contract_metadata.get("root_exact_helper_node_id")
            or metadata.get("root_exact_helper_node_id")
            or ""
        ).strip()
        if route_helper_name != helper_name and (
            not helper_id or route_helper_id != helper_id
        ):
            continue
        if retire_route(
            route.node_id,
            reason="root_exact_helper_certification_rejected",
            dependency_node_id=helper_id,
            verdict="root_exact_helper_rejected",
        ):
            retired += 1
    return retired


def _proved_proof_state_helper_names(proof_state: ProofSearchState) -> List[str]:
    """Return proved helper names known to the executable proof-state graph."""

    names: List[str] = []
    seen: Set[str] = set()
    for node in proof_state.nodes.values():
        if node.status != "proved":
            continue
        name = str(node.proved_helper_name or "").strip()
        if not name or name in seen:
            continue
        seen.add(name)
        names.append(name)
    return names


def _root_equivalent_helper_names(
    *,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    exclude_rejected: bool = True,
) -> List[str]:
    """Find verified helpers whose theorem statement is alpha-equal to the root."""

    root = proof_state.nodes.get(proof_state.root_node_id)
    root_statement = str(
        (root.target if root is not None else "")
        or getattr(conv, "goal_statement", "")
        or ""
    ).strip()
    root_key = canonicalize_lean_statement_for_identity(root_statement)
    if not root_key:
        return []
    names: List[str] = []
    seen: Set[str] = set()
    rejected_keys = (
        _root_exact_rejected_helper_keys(proof_state) if exclude_rejected else set()
    )
    for name, record in getattr(dossier, "verified_helpers", {}).items():
        helper_name = str(name or "").strip()
        if not helper_name or helper_name in seen:
            continue
        helper_source = str(getattr(record, "source", "") or "")
        helper_key = _root_exact_helper_rejection_key(
            helper_name,
            text_hash(helper_source),
        )
        if helper_key in rejected_keys:
            continue
        statement = helper_decl_statement(helper_source)
        if (
            statement
            and canonicalize_lean_statement_for_identity(statement) == root_key
        ):
            seen.add(helper_name)
            names.append(helper_name)
    return names


def _active_root_exact_helper_names(
    *,
    conv: Any,
    dossier: ProofDossier,
) -> List[str]:
    active_items = list(_proof_state_active_root_targets_for_frame(dossier))
    active_statement = active_root_target_statement(
        active_items,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    active_key = canonicalize_lean_statement_for_identity(active_statement)
    root_key = canonicalize_lean_statement_for_identity(
        str(
            getattr(conv, "goal_statement", "")
            or getattr(dossier, "root_statement", "")
            or ""
        )
    )
    if not active_key or active_key == root_key:
        return []
    names: List[str] = []
    seen: Set[str] = set()
    for name, record in getattr(dossier, "verified_helpers", {}).items():
        helper_name = str(name or "").strip()
        if not helper_name or helper_name in seen:
            continue
        helper_source = str(getattr(record, "source", "") or "")
        statement = helper_decl_statement(helper_source)
        if (
            statement
            and canonicalize_lean_statement_for_identity(statement) == active_key
        ):
            seen.add(helper_name)
            names.append(helper_name)
    return names


def _proof_state_root_tactic_helper_blocks(
    *,
    conv: Any,
    dossier: ProofDossier,
) -> List[str]:
    helpers = list(_proof_state_verified_helper_blocks(dossier))
    active_exact_names = _active_root_exact_helper_names(conv=conv, dossier=dossier)
    if not active_exact_names:
        return helpers
    replay_closure = getattr(dossier, "root_replay_helper_closure", None)
    if callable(replay_closure):
        route_local_helpers = replay_closure(support_helper_names=active_exact_names)
    else:
        route_local_helpers = []
    if not route_local_helpers:
        return helpers
    return ProofDossier._merge_replay_helper_blocks(helpers, route_local_helpers)


def _root_exact_helper_rejection_key(helper_name: str, helper_source_hash: str) -> str:
    name = str(helper_name or "").strip()
    source_hash = str(helper_source_hash or "").strip()
    return f"{name}:{source_hash}" if name and source_hash else ""


def _root_exact_rejected_helper_keys(proof_state: ProofSearchState) -> Set[str]:
    root = proof_state.nodes.get(proof_state.root_node_id)
    if root is None:
        return set()
    out: Set[str] = {
        str(item or "").strip()
        for item in list(getattr(root, "root_exact_rejected_helper_keys", []) or ())
        if str(item or "").strip()
    }
    for diagnostic in list(getattr(root, "diagnostics", []) or ()):
        if str(diagnostic.get("kind") or "") != "root_exact_helper_rejected":
            continue
        key = _root_exact_helper_rejection_key(
            str(diagnostic.get("helper_name") or ""),
            str(diagnostic.get("helper_source_hash") or ""),
        )
        if key:
            out.add(key)
    return out


def _root_exact_helper_contract_status(
    dossier: ProofDossier,
    *,
    helper_name: str,
    target_statement: str = "",
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {"ready": False, "verdict": "missing_proof_graph"}
    name = str(helper_name or "").strip()
    helper_id = str(getattr(graph, "helper_name_to_node_id", {}).get(name) or "").strip()
    if not helper_id:
        try:
            helper_id = str(graph.helper_node_id(name) if name else "").strip()
        except Exception:
            helper_id = ""
    if not helper_id or helper_id not in getattr(graph, "nodes", {}):
        return {
            "ready": False,
            "verdict": "root_exact_helper_contract_missing_helper_node",
            "helper_name": name,
        }
    checked: List[Dict[str, Any]] = []
    status_getter = getattr(graph, "route_assembly_contract_status", None)
    if not callable(status_getter):
        return {
            "ready": False,
            "verdict": "root_exact_helper_contract_status_api_missing",
            "helper_name": name,
            "helper_node_id": helper_id,
        }
    for route in list(graph.nodes_by_kind("strategy_route")):
        metadata = dict(getattr(route, "metadata", {}) or {})
        contract = metadata.get("route_assembly_contract")
        route_scope = str(metadata.get("route_scope") or "").strip()
        contract_scope = (
            str(contract.get("scope") or "").strip()
            if isinstance(contract, dict)
            else ""
        )
        if route_scope != "root_assembly" and contract_scope != "root_assembly":
            continue
        status = dict(
            status_getter(
                route.node_id,
                target_statement=str(
                    target_statement or getattr(dossier, "root_statement", "") or ""
                ),
            )
            or {}
        )
        required_ids = {
            str(item or "").strip()
            for item in list(status.get("required_node_ids") or [])
            if str(item or "").strip()
        }
        dependency_ids = {
            str(item or "").strip()
            for item in list(status.get("dependency_node_ids") or [])
            if str(item or "").strip()
        }
        if helper_id in required_ids and bool(status.get("ready")):
            out = dict(status)
            out["helper_name"] = name
            out["helper_node_id"] = helper_id
            return out
        if helper_id in required_ids or helper_id in dependency_ids:
            checked.append(
                {
                    "route_id": route.node_id,
                    "verdict": str(status.get("verdict") or ""),
                    "ready": bool(status.get("ready")),
                }
            )
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        try:
            increment("mini_root_assembly_contract_blocked", 1)
        except Exception:
            pass
    return {
        "ready": False,
        "verdict": "missing_ready_root_exact_helper_contract",
        "helper_name": name,
        "helper_node_id": helper_id,
        "route_contract_verdicts": checked[:10],
    }


def _ensure_root_exact_helper_contract(
    *,
    dossier: ProofDossier,
    helper_name: str,
    turn: int,
    phase: str,
) -> Dict[str, Any]:
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return {"ready": False, "verdict": "missing_proof_graph"}
    name = str(helper_name or "").strip()
    helper_id = str(getattr(graph, "helper_name_to_node_id", {}).get(name) or "").strip()
    if not helper_id:
        helper_id = str(graph.helper_node_id(name) if name else "").strip()
    if not helper_id or helper_id not in getattr(graph, "nodes", {}):
        return {
            "ready": False,
            "verdict": "root_exact_helper_contract_missing_helper_node",
            "helper_name": name,
        }
    route = graph.record_strategy_route(
        name=f"{name}_root_exact_route",
        description="Root assembly contract for a verified root-equivalent helper.",
        route_key=":".join(("proof_state_root_exact", helper_id)),
        score=0.75,
        phase=phase,
        turn_index=turn,
        metadata={
            "route_scope": "root_assembly",
            "source_phase": phase,
            "source": "root_exact_helper",
            "root_exact_helper_name": name,
            "root_exact_helper_node_id": helper_id,
        },
    )
    graph.attach_claim_to_route(route.node_id, helper_id)
    graph.set_route_assembly_contract(
        route.node_id,
        required_node_ids=[helper_id],
        target_statement=str(getattr(dossier, "root_statement", "") or ""),
        phase=phase,
        turn_index=turn,
        metadata={
            "source": "root_exact_helper",
            "root_exact_helper_name": name,
            "root_exact_helper_node_id": helper_id,
        },
    )
    status_getter = getattr(graph, "route_assembly_contract_status", None)
    if callable(status_getter):
        status = dict(
            status_getter(
                route.node_id,
                target_statement=str(getattr(dossier, "root_statement", "") or ""),
            )
            or {}
        )
        status["helper_name"] = name
        status["helper_node_id"] = helper_id
        return status
    return {
        "ready": False,
        "verdict": "root_exact_helper_contract_status_api_missing",
        "helper_name": name,
        "helper_node_id": helper_id,
    }


async def _try_proof_state_root_exact_frontier(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    turn: int,
    timeout_s: float,
    deadline_monotonic: float = 0.0,
) -> Tuple[bool, Optional[str], List[str], List[Dict[str, Any]]]:
    """Try root certification from any verified helper alpha-equal to the root."""

    if _fully_funded_operation_timeout(timeout_s, deadline_monotonic) <= 0.0:
        return False, None, [], []
    helper_names = _root_equivalent_helper_names(
        conv=conv,
        dossier=dossier,
        proof_state=proof_state,
    )
    if not helper_names:
        return False, None, [], []
    records: List[Dict[str, Any]] = []
    for helper_name in helper_names:
        operation_timeout = _fully_funded_operation_timeout(
            timeout_s,
            deadline_monotonic,
        )
        if operation_timeout <= 0.0:
            break
        _ensure_root_exact_helper_contract(
            dossier=dossier,
            helper_name=helper_name,
            turn=turn,
            phase="proof_state_root_exact_helper",
        )
        ok, proof, record = await _try_proof_state_root_exact_helper(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            helper_name=helper_name,
            turn=turn,
            timeout_s=operation_timeout,
            deadline_monotonic=deadline_monotonic,
        )
        if record:
            records.append(record)
        if ok and proof:
            return True, proof, [helper_name], records
        _reopen_root_after_failed_exact_helper(proof_state, record)
        _retire_failed_root_exact_helper_routes(dossier, record)
    return False, None, [], records


async def _try_proof_state_assembly_frontier(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    turn: int,
    timeout_s: float,
    max_nodes: int,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    target_node_ids: Optional[Sequence[str]] = None,
    target_assembly_ids: Optional[Sequence[str]] = None,
    required_child_node_ids: Optional[Sequence[str]] = None,
    deadline_monotonic: float = 0.0,
) -> Tuple[bool, Optional[str], List[str], List[Dict[str, Any]]]:
    """Run the deterministic assembler over ready parent nodes."""

    accepted_helpers: List[str] = []
    records: List[Dict[str, Any]] = []
    if _fully_funded_operation_timeout(timeout_s, deadline_monotonic) <= 0.0:
        return False, None, accepted_helpers, records
    graph = getattr(dossier, "proof_graph", None)
    target_ids = {
        str(item or "").strip()
        for item in list(target_node_ids or ())
        if str(item or "").strip()
    }
    selected_assembly_ids = tuple(
        str(item or "").strip()
        for item in list(target_assembly_ids or ())
        if str(item or "").strip()
    )
    selected_child_ids = tuple(
        str(item or "").strip()
        for item in list(required_child_node_ids or ())
        if str(item or "").strip()
    )
    refresher = getattr(proof_state, "refresh_graph_readiness", None)
    if callable(refresher) and graph is not None:
        try:
            refresh_records = refresher(
                graph,
                phase="proof_state_assembly_frontier",
                turn_index=turn,
                target_node_ids=tuple(target_ids) if target_ids else None,
            )
            for record in refresh_records:
                records.append(
                    {
                        "phase": "proof_state_graph_refresh",
                        "turn_in_phase": turn,
                        **dict(record),
                    }
                )
            if refresh_records:
                proof_state.sync_to_graph(
                    dossier,
                    phase="proof_state_assembly_frontier",
                    turn_index=turn,
                    refresh_target_node_ids=tuple(target_ids) if target_ids else None,
                )
        except Exception as exc:
            records.append(
                {
                    "phase": "proof_state_graph_refresh",
                    "turn_in_phase": turn,
                    "error": f"{type(exc).__name__}: {exc}",
                    "verdict": "graph_refresh_failed",
                }
            )
    if target_ids:
        target_getter = getattr(proof_state, "assembly_targets", None)
        if selected_assembly_ids:
            nodes = [
                proof_state.nodes[node_id]
                for node_id in target_ids
                if node_id in proof_state.nodes
            ]
        else:
            nodes = (
                target_getter(tuple(target_ids))
                if callable(target_getter)
                else [
                    proof_state.nodes[node_id]
                    for node_id in target_ids
                    if node_id in proof_state.nodes
                ]
            )
    else:
        nodes = proof_state.assembly_frontier(max_nodes=max_nodes, graph=graph)
    for node in nodes:
        operation_timeout = _fully_funded_operation_timeout(
            timeout_s,
            deadline_monotonic,
        )
        if operation_timeout <= 0.0:
            break
        helper_name, attempts = await _try_proof_state_parent_assembly(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            node=node,
            turn=turn,
            timeout_s=operation_timeout,
            proof_cache=proof_cache,
            target_assembly_ids=selected_assembly_ids,
            required_child_node_ids=selected_child_ids,
            deadline_monotonic=deadline_monotonic,
        )
        if attempts:
            records.append(
                {
                    "phase": "proof_state_parent_assembly",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": helper_name,
                    "assembly_attempts": attempts,
                    "verdict": (
                        "helper_accepted"
                        if helper_name
                        else "assembly_rejected"
                    ),
                }
            )
        if not helper_name:
            continue
        accepted_helpers.append(helper_name)
        if node.node_id == proof_state.root_node_id:
            _ensure_root_exact_helper_contract(
                dossier=dossier,
                helper_name=helper_name,
                turn=turn,
                phase="proof_state_parent_assembly",
            )
            ok, proof, root_record = await _try_proof_state_root_exact_helper(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                helper_name=helper_name,
                turn=turn,
                timeout_s=_fully_funded_operation_timeout(
                    timeout_s,
                    deadline_monotonic,
                ),
                deadline_monotonic=deadline_monotonic,
            )
            if root_record:
                records.append(root_record)
            if ok and proof:
                return True, proof, accepted_helpers, records
            _reopen_root_after_failed_exact_helper(proof_state, root_record)
    return False, None, accepted_helpers, records


async def _run_proof_state_assembly_fixpoint(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    turn: int,
    timeout_s: float,
    max_nodes: int,
    proof_cache: Optional[MiniVerifiedLemmaCache],
    target_node_ids: Optional[Sequence[str]] = None,
    target_assembly_ids: Optional[Sequence[str]] = None,
    required_child_node_ids: Optional[Sequence[str]] = None,
    deadline_monotonic: float = 0.0,
) -> Tuple[bool, Optional[str], List[str], List[Dict[str, Any]]]:
    """Run parent assembly until no newly proved parent can unblock another.

    E1 fix (2026-05-09): replaces the 5-pass polling loop with
    inverse-index event-driven propagation. After a parent is proved
    in one pass, ``ProofSearchState._assembly_parents_by_child`` is
    consulted to find every grandparent whose assembly group now lists
    that parent — including diamond patterns where the just-proved
    child supports multiple grandparents. The loop terminates when
    a pass produces no new helpers (no further closure possible) or
    the safety cap is hit.
    """

    accepted_helpers: List[str] = []
    records: List[Dict[str, Any]] = []
    target_ids = tuple(
        str(item or "").strip()
        for item in list(target_node_ids or ())
        if str(item or "").strip()
    )
    active_assembly_ids = tuple(
        str(item or "").strip()
        for item in list(target_assembly_ids or ())
        if str(item or "").strip()
    )
    required_child_ids: Tuple[str, ...] = tuple(
        str(item or "").strip()
        for item in list(required_child_node_ids or ())
        if str(item or "").strip()
    )
    active_target_ids = target_ids

    inverse_index = getattr(proof_state, "_assembly_parents_by_child", None)

    def _next_target_ids(current_ids: Sequence[str]) -> Tuple[str, ...]:
        """Walk one step UP the dependency DAG from just-proved nodes.

        Uses the E1 inverse index so a single proved child can advance
        the wave to ALL of its parents (diamond patterns). Falls back
        to the legacy ``parent_node_id`` reference ONLY when the index
        has no entry for this node — we treat the index as
        authoritative when populated, so a stale or aliased
        ``parent_node_id`` cannot inject a phantom target alongside
        valid index hits (adversarial review fix 2026-05-09).
        """

        out: List[str] = []
        seen: Set[str] = set()
        for node_id in current_ids:
            node = proof_state.nodes.get(str(node_id or ""))
            if node is None or node.status != "proved":
                continue
            index_hits: List[str] = []
            if isinstance(inverse_index, dict):
                for parent_id, _assembly_id in inverse_index.get(node.node_id, ()):
                    pid = str(parent_id or "").strip()
                    if pid:
                        index_hits.append(pid)
            if index_hits:
                for pid in index_hits:
                    if pid not in seen:
                        seen.add(pid)
                        out.append(pid)
            else:
                legacy_parent = str(
                    getattr(node, "parent_node_id", "") or ""
                ).strip()
                if legacy_parent and legacy_parent not in seen:
                    seen.add(legacy_parent)
                    out.append(legacy_parent)
        return tuple(out)

    # E1: was capped at 5 (line 1098 pre-fix). Raised to a safety cap
    # (64) so deep dependency chains close in a single fixpoint call.
    # Natural termination remains "no helpers accepted in last pass".
    safety_pass_cap = 64
    for pass_index in range(safety_pass_cap):
        operation_timeout = _fully_funded_operation_timeout(
            timeout_s,
            deadline_monotonic,
        )
        if operation_timeout <= 0.0:
            break
        pass_target_ids = active_target_ids if target_ids else ()
        state_ok, state_proof, assembly_helpers, assembly_records = (
            await _try_proof_state_assembly_frontier(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                turn=turn,
                timeout_s=operation_timeout,
                max_nodes=max_nodes,
                proof_cache=proof_cache,
                target_node_ids=pass_target_ids,
                target_assembly_ids=active_assembly_ids,
                required_child_node_ids=required_child_ids,
                deadline_monotonic=deadline_monotonic,
            )
        )
        records.extend(assembly_records)
        if assembly_helpers:
            accepted_helpers.extend(assembly_helpers)
        if state_ok and state_proof:
            return True, state_proof, accepted_helpers, records
        if not assembly_helpers:
            break
        if target_ids:
            previous_target_ids = active_target_ids
            active_target_ids = _next_target_ids(active_target_ids)
            required_child_ids = previous_target_ids
            active_assembly_ids = ()
            if not active_target_ids:
                break
    if accepted_helpers:
        state_ok, state_proof, root_helpers, root_records = (
            await _try_proof_state_root_exact_frontier(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                turn=turn,
                timeout_s=_fully_funded_operation_timeout(
                    timeout_s,
                    deadline_monotonic,
                ),
                deadline_monotonic=deadline_monotonic,
            )
        )
        records.extend(root_records)
        if root_helpers:
            accepted_helpers.extend(root_helpers)
        if state_ok and state_proof:
            return True, state_proof, accepted_helpers, records
    return False, None, accepted_helpers, records


async def _try_proof_state_salvaged_helper_assembly(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    helper_names: Sequence[str],
    recorder: Optional[Any],
    trace_prefix: str,
    turn: int,
    timeout_s: float,
    max_nodes: int,
    proof_cache: Optional[MiniVerifiedLemmaCache],
    phase: str,
) -> Tuple[bool, Optional[str], List[str]]:
    """Reconnect newly salvaged helpers to graph nodes, then assemble."""

    if dossier is None or proof_state is None:
        return False, None, []
    accepted_helpers: List[str] = []
    match_records = proof_state.record_verified_helper_matches(
        dossier=dossier,
        helper_names=helper_names,
        source=phase,
        phase=phase,
        turn_index=turn,
    )
    if match_records:
        matched_helpers = [
            str(record.get("helper_name") or "")
            for record in match_records
            if str(record.get("helper_name") or "").strip()
        ]
        accepted_helpers.extend(matched_helpers)
        _trace(
            trace_prefix,
            "  proof-state matched salvaged helper(s): "
            + ", ".join(dict.fromkeys(matched_helpers)),
        )
        if recorder is not None:
            for record in match_records:
                recorder.record_turn(record)
    proof_state.sync_to_graph(
        dossier,
        phase=f"{phase}_proof_state_match",
        turn_index=turn,
    )
    if float(timeout_s or 0.0) <= 0.0:
        return False, None, accepted_helpers

    state_ok, state_proof, root_helpers, root_records = (
        await _try_proof_state_root_exact_frontier(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            turn=turn,
            timeout_s=timeout_s,
        )
    )
    accepted_helpers.extend(root_helpers)
    if recorder is not None:
        for record in root_records:
            recorder.record_turn(record)
    if state_ok and state_proof:
        return True, state_proof, accepted_helpers

    state_ok, state_proof, assembly_helpers, assembly_records = (
        await _run_proof_state_assembly_fixpoint(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            turn=turn,
            timeout_s=timeout_s,
            max_nodes=max(1, int(max_nodes or 1)),
            proof_cache=proof_cache,
        )
    )
    accepted_helpers.extend(assembly_helpers)
    if recorder is not None:
        for record in assembly_records:
            recorder.record_turn(record)
    if state_ok and state_proof:
        return True, state_proof, accepted_helpers
    return False, None, accepted_helpers


async def _try_proof_state_root_tactic_assembly(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    turn: int,
    timeout_s: float,
    max_candidates: int,
    allow_deferred_retry: bool = False,
    deadline_monotonic: float = 0.0,
    context_timeout_s: Optional[float] = None,
    candidate_attempt_limit: int = 0,
) -> Tuple[bool, Optional[str], List[str], List[Dict[str, Any]]]:
    """Try the root tactic closer once for each distinct helper context."""

    helpers = _proof_state_root_tactic_helper_blocks(conv=conv, dossier=dossier)
    helper_names = _helper_names_from_blocks(helpers)
    if not helpers:
        return False, None, [], []
    if int(max_candidates or 0) <= 0 or float(timeout_s or 0.0) <= 0.0:
        return False, None, [], [
            {
                "phase": "proof_state_root_assembly",
                "turn_in_phase": turn,
                "accepted_helpers": list(helper_names),
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_success_attempt": None,
                "tactic_elapsed_s": 0.0,
                "tactic_exit_reason": "tactic_budget_disabled",
                "verdict": "tactic_skipped",
            }
        ]

    root_tactic_preamble = _proof_state_acceptance_preamble(conv)
    context_timeout = (
        float(timeout_s or 0.0)
        if context_timeout_s is None
        else float(context_timeout_s or 0.0)
    )
    answer_safety_opaque_mode = bool(
        getattr(conv, "opaque_mode", getattr(dossier, "opaque_mode", True))
    )
    answer_safety_allow_official_answer_visibility = bool(
        getattr(
            conv,
            "allow_official_answer_visibility",
            getattr(dossier, "allow_official_answer_visibility", False),
        )
    )
    answer_safety_official_answer_payload_present = getattr(
        conv,
        "official_answer_payload_present",
        getattr(dossier, "official_answer_payload_present", None),
    )
    answer_safety_suppress_solution_placeholders = bool(
        getattr(
            conv,
            "suppress_solution_placeholders",
            getattr(dossier, "suppress_solution_placeholders", True),
        )
    )
    context_key = _root_tactic_context_key(
        goal_statement=str(getattr(conv, "goal_statement", "") or ""),
        preamble=root_tactic_preamble,
        helpers=helpers,
        timeout_s=context_timeout,
        max_candidates=max_candidates,
        active_root_targets=_proof_state_active_root_targets_for_frame(dossier),
    )
    root_node = proof_state.nodes.get(proof_state.root_node_id)
    active_root_targets = _proof_state_active_root_targets_for_frame(dossier)
    direct_root_tactic = not active_root_targets
    raw_continuation = (
        getattr(root_node, "root_tactic_portfolio_continuation", {})
        if root_node is not None
        else {}
    )
    portfolio_continuation = validated_root_tactic_portfolio_continuation(
        raw_continuation
    )
    continuation_phase = str(portfolio_continuation.get("phase") or "")
    if (
        str(portfolio_continuation.get("context_key") or "") != context_key
        or (
            direct_root_tactic
            and continuation_phase not in {"", "direct"}
        )
        or (
            not direct_root_tactic
            and continuation_phase not in {"", "active", "fallback"}
        )
        or len(list(portfolio_continuation.get("candidates") or ()))
        > max(0, int(max_candidates or 0))
    ):
        portfolio_continuation = {}
    if root_node is not None and portfolio_continuation != raw_continuation:
        root_node.root_tactic_portfolio_continuation = {}
    deferred_keys = _root_tactic_deferred_context_keys(proof_state)
    was_deferred = context_key in deferred_keys
    if context_key in _root_tactic_attempted_context_keys(proof_state):
        if root_node is not None:
            root_node.root_tactic_portfolio_continuation = {}
        try:
            proof_state.root_tactic_context_skips += 1
        except Exception:
            pass
        return False, None, [], [
            {
                "phase": "proof_state_root_assembly",
                "turn_in_phase": turn,
                "accepted_helpers": list(helper_names),
                "root_tactic_context_key": context_key,
                "verdict": "root_tactic_context_already_attempted",
            }
        ]
    if was_deferred:
        if not allow_deferred_retry:
            try:
                proof_state.root_tactic_deferred_skips += 1
            except Exception:
                pass
            return False, None, [], [
                {
                    "phase": "proof_state_root_assembly",
                    "turn_in_phase": turn,
                    "accepted_helpers": list(helper_names),
                    "root_tactic_context_key": context_key,
                    "root_tactic_context_deferred": True,
                    "verdict": "root_tactic_context_deferred",
                }
            ]
        try:
            proof_state.root_tactic_transient_retries += 1
        except Exception:
            pass
    elif deferred_keys:
        _mark_root_tactic_context_reenabled(proof_state, context_key)
    shared_root_tactic_pattern_cache = _proof_state_tactic_pattern_cache(proof_state)
    # Tactic closure records negative/cache evidence while it runs. Keep that
    # evidence isolated until the strict Lean operation returns on time so a
    # cancellation-resistant tail cannot mutate shared search state.
    root_tactic_pattern_cache = copy.deepcopy(shared_root_tactic_pattern_cache)
    root_tactic_pattern_context = _proof_state_tactic_pattern_context(
        proof_state,
        root_node or proof_state.nodes[proof_state.root_node_id],
        scope="proof_state_root_tactic",
        mode="root_assembly",
    )
    root_tactic_pattern_context.update(
        {
            "root_tactic_context_key": context_key,
            "tactic_timeout_s": str(round(max(0.0, context_timeout), 3)),
            "max_candidates": str(max(0, int(max_candidates or 0))),
        }
    )
    resumed_candidates = tuple(
        TacticCandidate(
            proof=str(item["proof"]),
            tactic=str(item["tactic"]),
            source=str(item["source"]),
            helper=(
                str(item["helper"])
                if item.get("helper") is not None
                else None
            ),
        )
        for item in list(portfolio_continuation.get("candidates") or ())
    )
    resumed_offset = int(
        portfolio_continuation.get("next_candidate_index", 0) or 0
    )
    resumed_phase = str(
        portfolio_continuation.get("phase")
        or ("direct" if direct_root_tactic else "active")
    )

    async def run_root_tactic() -> Any:
        return await try_close_root_with_active_lift(
                lean=lean,
                goal_statement=conv.goal_statement,
                preamble=root_tactic_preamble,
                helpers=helpers,
                active_root_targets=tuple(
                    item
                    for item in list(getattr(dossier, "active_root_targets", []) or ())
                    if isinstance(item, dict)
                ),
                timeout_s=float(timeout_s or 0.0),
                max_candidates=max(1, int(max_candidates or 1)),
                candidate_portfolio=resumed_candidates or None,
                candidate_portfolio_offset=resumed_offset,
                candidate_portfolio_phase=resumed_phase,
                candidate_attempt_limit=max(
                    0, int(candidate_attempt_limit or 0)
                ),
                pattern_cache=root_tactic_pattern_cache,
                pattern_context=root_tactic_pattern_context,
                defer_success_cache=True,
                active_root_frame_helper_blocks=dossier.verified_helper_blocks(),
                tactic_closer=try_close_with_tactics,
                suppress_solution_placeholders=(
                    answer_safety_suppress_solution_placeholders
                ),
                opaque_mode=answer_safety_opaque_mode,
                allow_official_answer_visibility=(
                    answer_safety_allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    answer_safety_official_answer_payload_present
                ),
                # Observer writes are replayed only after the strict operation
                # completes; detached tails must be mutation-free.
                attempt_observer=None,
            )

    try:
        root_tactic = await _await_serialized_lean_operation(
            lean,
            run_root_tactic,
            timeout_s=float(timeout_s or 0.0),
            deadline_monotonic=deadline_monotonic,
            operation_label="proof_state_root_tactic",
        )
    except _LeanOperationDeadline:
        if was_deferred and allow_deferred_retry:
            _mark_root_tactic_context_continued(proof_state, context_key)
            _mark_root_tactic_context_attempted(proof_state, context_key)
            try:
                proof_state.root_tactic_terminal_after_continuation += 1
            except Exception:
                pass
        elif not was_deferred:
            _mark_root_tactic_context_deferred(proof_state, context_key)
        return False, None, [], [
            {
                "phase": "proof_state_root_assembly",
                "turn_in_phase": turn,
                "accepted_helpers": list(helper_names),
                "root_tactic_context_key": context_key,
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_success_attempt": None,
                "tactic_elapsed_s": max(0.0, float(timeout_s or 0.0)),
                "tactic_exit_reason": "timeout",
                "root_tactic_context_preserved": True,
                "root_tactic_context_deferred": bool(not was_deferred),
                "root_tactic_context_retry_after_defer": bool(was_deferred),
                "verdict": "tactic_transient_failure",
            }
        ]
    except Exception as exc:
        if was_deferred and allow_deferred_retry:
            _mark_root_tactic_context_continued(proof_state, context_key)
            _mark_root_tactic_context_attempted(proof_state, context_key)
            try:
                proof_state.root_tactic_terminal_after_continuation += 1
            except Exception:
                pass
        elif not was_deferred:
            _mark_root_tactic_context_deferred(proof_state, context_key)
        return False, None, [], [
            {
                "phase": "proof_state_root_assembly",
                "turn_in_phase": turn,
                "accepted_helpers": list(helper_names),
                "root_tactic_context_key": context_key,
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_success_attempt": None,
                "tactic_elapsed_s": 0.0,
                "tactic_exit_reason": f"{type(exc).__name__}: {exc}",
                "root_tactic_context_preserved": True,
                "root_tactic_context_deferred": bool(not was_deferred),
                "root_tactic_context_retry_after_defer": bool(was_deferred),
                "verdict": "tactic_exception",
            }
        ]
    setattr(proof_state, "_tactic_pattern_cache", root_tactic_pattern_cache)
    _record_completed_tactic_observer_events(
        dossier,
        "proof_state_root_tactic",
        root_tactic,
    )
    success_attempt = next(
        (
            attempt
            for attempt in root_tactic.attempts
            if isinstance(attempt, dict) and attempt.get("ok")
        ),
        None,
    )
    root_tactic_exit_reason = str(
        getattr(root_tactic, "exit_reason", "") or ""
    )
    root_tactic_cache_metadata = dict(
        getattr(root_tactic, "cache_metadata", {}) or {}
    )
    continuation_result_phase = str(
        root_tactic_cache_metadata.get(
            "root_tactic_candidate_portfolio_phase"
        )
        or ("direct" if direct_root_tactic else resumed_phase)
    )
    capped_phase_timeout = bool(
        int(candidate_attempt_limit or 0) > 0
        and root_tactic_exit_reason == "timeout"
        and continuation_result_phase in {"direct", "active", "fallback"}
        and tuple(getattr(root_tactic, "candidate_portfolio", ()) or ())
    )
    if root_tactic_exit_reason == "candidate_quantum_exhausted" or capped_phase_timeout:
        candidate_portfolio = tuple(
            getattr(root_tactic, "candidate_portfolio", ()) or ()
        )
        next_candidate_index = int(
            getattr(root_tactic, "next_candidate_index", 0) or 0
        )
        saved_continuation: Dict[str, Any] = {}
        if root_node is not None:
            saved_continuation = validated_root_tactic_portfolio_continuation({
                "schema_version": (
                    PROOF_STATE_ROOT_TACTIC_PORTFOLIO_SCHEMA_VERSION
                ),
                "context_key": context_key,
                "phase": continuation_result_phase,
                "candidates": [
                    {
                        "proof": str(candidate.proof),
                        "tactic": str(candidate.tactic),
                        "source": str(candidate.source),
                        "helper": candidate.helper,
                    }
                    for candidate in candidate_portfolio
                    if isinstance(candidate, TacticCandidate)
                ],
                "next_candidate_index": next_candidate_index,
            })
            root_node.root_tactic_portfolio_continuation = saved_continuation
        if capped_phase_timeout and saved_continuation:
            if was_deferred and allow_deferred_retry:
                _mark_root_tactic_context_continued(proof_state, context_key)
                _mark_root_tactic_context_attempted(proof_state, context_key)
                try:
                    proof_state.root_tactic_terminal_after_continuation += 1
                except Exception:
                    pass
            elif not was_deferred:
                _mark_root_tactic_context_deferred(proof_state, context_key)
        record = {
            "phase": "proof_state_root_assembly",
            "turn_in_phase": turn,
            "accepted_helpers": list(helper_names),
            "root_tactic_context_key": context_key,
            "tactic_candidate_count": root_tactic.candidate_count,
            **tactic_attempt_telemetry_fields(root_tactic.attempts),
            "tactic_attempts": root_tactic.attempts[:10],
            "tactic_success_attempt": success_attempt,
            "tactic_elapsed_s": root_tactic.elapsed_s,
            "tactic_exit_reason": root_tactic.exit_reason,
            "tactic_pattern_cache": root_tactic_cache_metadata,
            "root_tactic_context_preserved": True,
            "root_tactic_context_deferred": bool(
                capped_phase_timeout and saved_continuation and not was_deferred
            ),
            "root_tactic_context_retry_after_defer": bool(was_deferred),
            "verdict": (
                (
                    "root_tactic_candidate_quantum_timeout_preserved"
                    if capped_phase_timeout
                    else "root_tactic_candidate_quantum_exhausted"
                )
                if saved_continuation
                else "root_tactic_candidate_quantum_state_rejected"
            ),
        }
        proof_state.record_tactic_pattern_cache_metrics(
            root_tactic_cache_metadata
        )
        return False, None, [], [record]
    if root_node is not None:
        root_node.root_tactic_portfolio_continuation = {}
    transient_failure = is_transient_tactic_close_failure(root_tactic)
    should_defer = bool(
        transient_failure and _root_tactic_transient_should_defer(root_tactic)
    )
    proof_found_pending_finalization = bool(root_tactic.ok and root_tactic.proof)
    if was_deferred and allow_deferred_retry:
        _mark_root_tactic_context_continued(proof_state, context_key)
    if proof_found_pending_finalization:
        pass
    elif not transient_failure:
        _mark_root_tactic_context_attempted(proof_state, context_key)
        if was_deferred:
            try:
                proof_state.root_tactic_terminal_after_continuation += 1
            except Exception:
                pass
    elif was_deferred and allow_deferred_retry:
        _mark_root_tactic_context_attempted(proof_state, context_key)
        try:
            proof_state.root_tactic_terminal_after_continuation += 1
        except Exception:
            pass
    elif should_defer:
        _mark_root_tactic_context_deferred(proof_state, context_key)
    else:
        _mark_root_tactic_context_attempted(proof_state, context_key)
    cache_metadata = dict(getattr(root_tactic, "cache_metadata", {}) or {})
    record = {
        "phase": "proof_state_root_assembly",
        "turn_in_phase": turn,
        "accepted_helpers": list(helper_names),
        "root_tactic_context_key": context_key,
        "tactic_candidate_count": root_tactic.candidate_count,
        **tactic_attempt_telemetry_fields(root_tactic.attempts),
        "tactic_attempts": root_tactic.attempts[:10],
        "tactic_success_attempt": success_attempt,
        "tactic_elapsed_s": root_tactic.elapsed_s,
        "tactic_exit_reason": root_tactic.exit_reason,
        "tactic_pattern_cache": cache_metadata,
        "root_tactic_context_preserved": bool(transient_failure),
        "root_tactic_context_deferred": bool(should_defer and not was_deferred),
        "root_tactic_context_retry_after_defer": bool(was_deferred),
        "verdict": (
            "tactic_solved"
            if root_tactic.ok
            else (
                "tactic_transient_failure"
                if transient_failure
                else "tactic_rejected"
            )
        ),
    }
    active_root_target_statement_text = str(
        cache_metadata.get("active_root_target_statement")
        or ""
    ).strip()
    if active_root_target_statement_text:
        record["active_root_target_statement"] = active_root_target_statement_text
        record["active_root_lift_attempted"] = bool(
            cache_metadata.get("active_root_lift_attempted")
        )
        record["active_root_lift_succeeded"] = bool(
            cache_metadata.get("active_root_lift_succeeded")
        )
    if root_tactic.ok and root_tactic.proof:
        contract_success_attempt = success_attempt
        if active_root_target_statement_text and isinstance(success_attempt, dict):
            contract_success_attempt = {
                **success_attempt,
                "active_root_target_statement": active_root_target_statement_text,
            }
        contract_status = root_tactic_success_contract_status(
            dossier,
            proof=root_tactic.proof,
            helper_blocks=helpers,
            success_attempt=contract_success_attempt,
            phase="proof_state_root_assembly",
            turn_index=turn,
            target_statement=str(
                getattr(dossier, "root_statement", "")
                or getattr(conv, "goal_statement", "")
                or ""
            ),
        )
        record["route_assembly_contract_status"] = contract_status
        if not bool(contract_status.get("ready")):
            record["verdict"] = "root_route_contract_not_ready"
            record["route_contract_verdict"] = str(
                contract_status.get("verdict") or ""
            )
            dossier.record_attempt(
                phase="proof_state_root_assembly",
                turn_index=turn,
                proof=root_tactic.proof,
                helper_names=list(helper_names),
                verdict="root_route_contract_not_ready",
                metadata={
                    "route_assembly_contract_status": contract_status,
                    "root_tactic_context_key": context_key,
                },
            )
            proof_state.record_tactic_pattern_cache_metrics(
                getattr(root_tactic, "cache_metadata", {})
            )
            _clear_root_tactic_context_retry_markers(proof_state, context_key)
            record["root_tactic_context_preserved"] = True
            record["root_tactic_finalization_pending"] = True
            return False, None, [], [record]
        route_helper_names = [
            str(name or "").strip()
            for name in list(contract_status.get("helper_names") or [])
            if str(name or "").strip()
        ]
        replay_helpers = _root_replay_blocks_for_helper_names(
            dossier=dossier,
            helper_context=helpers,
            helper_names=route_helper_names,
        )
        replay_helper_names = route_helper_names or _helper_names_from_blocks(
            replay_helpers
        )
        replay_helper_names = _helper_names_from_blocks(
            replay_helpers
        ) or replay_helper_names
        from ensemble_prover.root_finalization import (
            finalize_root_solution,
            root_verification_certificate,
        )

        finalization = finalize_root_solution(
            dossier=dossier,
            proof_state=proof_state,
            proof=root_tactic.proof,
            replay_helpers=replay_helpers,
            helper_names=replay_helper_names,
            phase="proof_state_root_assembly",
            turn_index=turn,
            route_id=str(
                contract_status.get("route_id")
                or contract_status.get("created_route_id")
                or ""
            ),
            dependency_node_ids=tuple(
                str(node_id or "").strip()
                for node_id in list(
                    contract_status.get("dependency_node_ids")
                    or contract_status.get("required_node_ids")
                    or []
                )
                if str(node_id or "").strip()
            ),
            dependency_helper_names=route_helper_names or replay_helper_names,
            target_statement=str(
                getattr(dossier, "root_statement", "")
                or getattr(conv, "goal_statement", "")
                or ""
            ),
            require_route_contract=True,
            verification_certificate=root_verification_certificate(
                accepted=True,
                proof=root_tactic.proof,
                phase="proof_state_root_assembly",
                turn_index=turn,
                target_statement=str(
                    getattr(dossier, "root_statement", "")
                    or getattr(conv, "goal_statement", "")
                    or ""
                ),
                replay_helpers=replay_helpers,
                helper_names=replay_helper_names,
                output=str(
                    (success_attempt or {}).get("output")
                    or (success_attempt or {}).get("output_preview")
                    or ""
                ),
                source="proof_state_root_assembly",
            ),
            require_verification_certificate=True,
        )
        if not finalization.accepted:
            record["root_finalization_verdict"] = finalization.verdict
            if _root_tactic_finalization_pending_retryable(finalization.verdict):
                _clear_root_tactic_context_retry_markers(proof_state, context_key)
                record["root_tactic_context_preserved"] = True
                record["root_tactic_finalization_pending"] = True
            else:
                _mark_root_tactic_context_attempted(proof_state, context_key)
            return False, None, [], [record]
        _mark_root_tactic_context_attempted(proof_state, context_key)
        if was_deferred:
            try:
                proof_state.root_tactic_terminal_after_continuation += 1
            except Exception:
                pass
        if isinstance(success_attempt, dict):
            candidate = TacticPatternCache.candidate_from_attempt(success_attempt)
            if candidate is not None:
                object.__setattr__(
                    root_tactic,
                    "cache_metadata",
                    _merge_tactic_cache_metadata(
                        getattr(root_tactic, "cache_metadata", {}),
                        root_tactic_pattern_cache.confirm_success(
                            goal_statement=conv.goal_statement,
                            preamble=root_tactic_preamble,
                            helpers=helpers,
                            candidate=candidate,
                            pattern_context=root_tactic_pattern_context,
                            suppress_solution_placeholders=(
                                answer_safety_suppress_solution_placeholders
                            ),
                            opaque_mode=answer_safety_opaque_mode,
                            allow_official_answer_visibility=(
                                answer_safety_allow_official_answer_visibility
                            ),
                        ),
                    ),
                )
                record["tactic_pattern_cache"] = dict(
                    getattr(root_tactic, "cache_metadata", {}) or {}
                )
        proof_state.record_tactic_pattern_cache_metrics(
            getattr(root_tactic, "cache_metadata", {})
        )
        return True, root_tactic.proof, helper_names, [record]
    proof_state.record_tactic_pattern_cache_metrics(
        getattr(root_tactic, "cache_metadata", {})
    )
    return False, None, [], [record]


async def _try_proof_state_cache_hit(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    proof_cache: Optional[MiniVerifiedLemmaCache],
    turn: int,
    timeout_s: float,
    deadline_monotonic: float = 0.0,
) -> Tuple[str, List[Dict[str, Any]]]:
    if (
        proof_cache is None
        or node.status == "proved"
        or _fully_funded_operation_timeout(timeout_s, deadline_monotonic) <= 0.0
    ):
        return "", []
    records: List[Dict[str, Any]] = []
    preamble = _proof_state_check_preamble(conv)
    for record in proof_cache.lookup(node.target, preamble=preamble, max_hits=3):
        operation_timeout = _fully_funded_operation_timeout(
            timeout_s,
            deadline_monotonic,
        )
        if operation_timeout <= 0.0:
            break
        helper_block = str(record.get("source") or "").strip()
        helper_name = helper_decl_name(helper_block) or ""
        # Tag emitted by lookup() so the recorder can attribute hits per
        # tier (tier1 = same-preamble, tier2 = cross-preamble fallback).
        cache_tier = str(record.get("_lookup_tier") or "")
        if not helper_block or not helper_name:
            continue
        rejection = _proof_state_helper_policy_rejection(
            helper_block,
            expected_statement=node.target,
        )
        if rejection:
            records.append(
                {
                    "phase": "proof_state_cache_lookup",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "cached_helper": helper_name,
                    "cache_source_hash": str(record.get("source_hash") or ""),
                    "cache_lookup_tier": cache_tier,
                    "accepted": False,
                    "rejection": rejection,
                }
            )
            continue
        existing = getattr(dossier, "verified_helpers", {}).get(helper_name)
        reused_existing_helper = False
        if existing is not None:
            existing_statement = helper_decl_statement(
                str(getattr(existing, "source", "") or "")
            )
            existing_key = canonicalize_lean_statement_for_identity(existing_statement)
            target_key = canonicalize_lean_statement_for_identity(node.target)
            if existing_key and existing_key == target_key:
                # Same-statement publication is not a current-context receipt.
                # Fall through to the complete acceptance/visibility checks.
                reused_existing_helper = True
            else:
                records.append(
                    {
                        "phase": "proof_state_cache_lookup",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "target": node.target,
                        "cached_helper": helper_name,
                        "cache_source_hash": str(record.get("source_hash") or ""),
                        "cache_lookup_tier": cache_tier,
                        "accepted": False,
                        "rejection": "cache_helper_name_collision",
                        "existing_statement": existing_statement,
                    }
                )
                continue
        staged_acceptance = stage_pending_helper_acceptance(
            conv=conv,
            dossier=dossier,
            node=node,
            helper_block=helper_block,
            source=f"cache_hit:{record.get('source_hash') or helper_name}",
            continuation={"kind": "cache_hit"},
        )
        if not staged_acceptance:
            records.append(
                {
                    "phase": "proof_state_cache_lookup",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "cached_helper": helper_name,
                    "cache_source_hash": str(record.get("source_hash") or ""),
                    "cache_lookup_tier": cache_tier,
                    "accepted": False,
                    "retryable_infrastructure": True,
                    "verdict": "pending_helper_acceptance_owned",
                }
            )
            return "", records
        acceptance_status: Dict[str, Any] = {}
        accepted = await _accept_proof_state_helper(
            lean=lean,
            conv=conv,
            dossier=dossier,
            helper_block=helper_block,
            phase="proof_state_cache_hit",
            turn_index=turn,
            timeout_s=operation_timeout,
            proof_cache=None,
            proof_state=proof_state,
            target_statement=node.target,
            deadline_monotonic=deadline_monotonic,
            status_out=acceptance_status,
        )
        records.append(
            {
                "phase": "proof_state_cache_lookup",
                "turn_in_phase": turn,
                "node_id": node.node_id,
                "target": node.target,
                "cached_helper": helper_name,
                "cache_source_hash": str(record.get("source_hash") or ""),
                "cache_lookup_tier": cache_tier,
                "accepted": bool(accepted),
                "reused_existing_helper": bool(
                    accepted and reused_existing_helper
                ),
            }
        )
        if accepted:
            node.pending_helper_acceptance = {}
            proof_state.record_cache_hit(
                node_id=node.node_id,
                helper_name=helper_name,
            )
            return helper_name, records
        if str(acceptance_status.get("status") or "") in {
            "retryable_error",
            "cancelled",
        }:
            retain_pending_helper_acceptance_retry(
                proof_state=proof_state,
                node=node,
                status=acceptance_status,
            )
            records[-1]["retryable_infrastructure"] = True
            records[-1]["acceptance_status"] = dict(acceptance_status)
            return "", records
        node.pending_helper_acceptance = {}
    return "", records


# D2 fix (2026-05-09, gate-side):
# Adversarial review found the original D2 ad-hoc opener was placed
# INSIDE _try_proof_state_lemma_dag_helpers, but every production caller
# guards that function with a `not has_open_decomposition_task()`
# precondition that returns early before invoking — making the in-
# function fix unreachable from real runs. The proper fix is at the
# CALL SITES: detect sorry-stub helpers BEFORE the gate, open a task
# if any are present, then let the existing gate logic proceed.
#
# This module-level helper is the shared entry point. Production callers
# (mini_prover.py twin sites, conversation_turn.py twin sites,
# helper_only_salvage.py, lemma_dag_decompose.py) all call this BEFORE
# their `has_open_decomposition_task()` gate. When the helper opens a
# task, the gate now passes and the lemma-DAG path proceeds.
def _is_sorry_stub_body(helper_block: str) -> bool:
    """Detect a single helper as a sorry-stub body.

    Strips line/block comments, collapses internal whitespace, then
    membership-tests against `{"by sorry", "by admit", "sorry",
    "admit"}`. Tolerant of multi-line, double-space, comment-suffixed,
    and indented forms — same set of phrasings the executor's body
    detector at proof_state_executor.py:1537+ catches.
    """
    body_text = helper_decl_body(str(helper_block or "")) or ""
    no_block = re.sub(r"/-[\s\S]*?-/", "", body_text)
    no_line = re.sub(r"--[^\n]*", "", no_block)
    body_norm = " ".join(no_line.split()).lower()
    return body_norm in {"by sorry", "by admit", "sorry", "admit"}


def ensure_decomposition_task_open_for_sorry_stubs(
    proof_state: Optional[Any],
    helpers: Sequence[str],
    *,
    source: str = "sorry_stub_helpers_volunteered",
) -> str:
    """Open a decomposition_task if helpers contain sorry-stubs and none open.

    Returns the task_id when a task is open after the call (either
    pre-existing OR newly created); empty string when no task is open
    (helpers had no sorry-stubs OR proof_state is None OR ensure
    failed).

    Idempotent: if a decomposition_task is already open, returns its
    id without creating another one.

    The blocker text on the new node carries the source string so
    post-mortem analysis can distinguish ad-hoc opens (this path)
    from canonical ``record_construction_collapse`` opens (controller-
    forced structural decomp).
    """
    if proof_state is None or not helpers:
        return ""
    has_open = getattr(proof_state, "has_open_decomposition_task", None)
    if callable(has_open) and has_open():
        # Already open — find the existing task's id by walking nodes.
        for node_id, node in (getattr(proof_state, "nodes", None) or {}).items():
            if (
                getattr(node, "kind", "") == "decomposition_task"
                and getattr(node, "status", "") == "open"
            ):
                return str(node_id)
        return ""
    # Detect at least one sorry-stub.
    for helper_block in list(helpers or []):
        if _is_sorry_stub_body(helper_block):
            ensure = getattr(proof_state, "ensure_decomposition_task_open", None)
            if callable(ensure):
                try:
                    return str(
                        ensure(
                            source=str(source or "sorry_stub_helpers_volunteered"),
                            blocker=(
                                f"ad_hoc:{source}: LLM emitted sorry-stub "
                                "helpers as decomposition request"
                            ),
                        )
                    )
                except Exception:
                    return ""
            return ""
    return ""


def ensure_decomposition_task_open_for_lemma_dag_candidates(
    proof_state: Optional[Any],
    helpers: Sequence[str],
    *,
    source: str = "lemma_dag_helpers_volunteered",
) -> Dict[str, Any]:
    """Open an ad-hoc decomposition task for actionable lemma-DAG candidates.

    Returns a structured record so callers can distinguish "already open",
    "opened for sorry stubs", "opened for parent/root stubs", and the many
    no-op cases that used to collapse into a misleading "task closed" trace.
    """

    record: Dict[str, Any] = {
        "task_id": "",
        "opened": False,
        "reason": "",
        "source": str(source or "lemma_dag_helpers_volunteered"),
        "candidate_count": len(list(helpers or [])),
    }
    if proof_state is None:
        record["reason"] = "missing_proof_state"
        return record
    if not helpers:
        record["reason"] = "no_candidates"
        return record
    has_open = getattr(proof_state, "has_open_decomposition_task", None)
    if callable(has_open) and has_open():
        for node_id, node in (getattr(proof_state, "nodes", None) or {}).items():
            if (
                getattr(node, "kind", "") == "decomposition_task"
                and getattr(node, "status", "") == "open"
            ):
                record["task_id"] = str(node_id)
                record["reason"] = "already_open"
                return record
        record["reason"] = "already_open_id_unavailable"
        return record

    candidate_helpers = list(helpers or [])
    has_sorry_stub = any(_is_sorry_stub_body(helper) for helper in candidate_helpers)
    parent_stub_sources: List[str] = []
    if not has_sorry_stub:
        try:
            parent_stub_sources = _lemma_dag_parent_stub_candidate_sources(
                proof_state,
                candidate_helpers,
            )
        except Exception as exc:
            record["reason"] = "parent_stub_probe_error"
            record["error_type"] = type(exc).__name__
            record["error"] = str(exc)[:240]
            return record
    if not has_sorry_stub and not parent_stub_sources:
        record["reason"] = "no_openable_stub"
        return record

    ensure = getattr(proof_state, "ensure_decomposition_task_open", None)
    if not callable(ensure):
        record["reason"] = "missing_open_task_api"
        return record

    kind = "sorry_stub" if has_sorry_stub else "parent_stub"
    record["open_kind"] = kind
    blocker = (
        f"ad_hoc:{source}: LLM emitted sorry-stub helpers as decomposition request"
        if has_sorry_stub
        else f"ad_hoc:{source}: LLM emitted parent proof stub as decomposition assembly contract"
    )
    try:
        task_id = str(
            ensure(
                source=str(source or "lemma_dag_helpers_volunteered"),
                blocker=blocker,
            )
            or ""
        )
    except Exception as exc:
        record["reason"] = "open_task_error"
        record["error_type"] = type(exc).__name__
        record["error"] = str(exc)[:240]
        return record
    if not task_id:
        record["reason"] = "open_task_returned_empty"
        return record
    record["task_id"] = task_id
    record["opened"] = True
    record["reason"] = f"opened_{kind}"
    return record


async def _try_proof_state_lemma_dag_helpers(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: Optional[ProofDossier],
    proof_state: Optional[ProofSearchState],
    helpers: Sequence[str],
    recorder: Optional[Any],
    trace_prefix: str,
    turn: int,
    timeout_s: float,
    deadline_monotonic: float = 0.0,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    target_task_id: str = "",
    max_parent_stub_goals: int = 8,
    initial_proposed_count: int = 0,
    initial_accepted_count: int = 0,
    initial_candidate_node_ids: Optional[Sequence[str]] = None,
    initial_accepted_helpers: Optional[Sequence[str]] = None,
    initial_renamed_collisions: Optional[Mapping[str, str]] = None,
    status_out: Optional[Dict[str, Any]] = None,
    records_out: Optional[List[Dict[str, Any]]] = None,
) -> List[str]:
    """Execute an open decomposition task by verifying LLM-proposed helpers.

    This turns a prompt-level lemma-DAG proposal into graph state: accepted
    helpers become proved child nodes, rejected but well-formed helper
    statements become open child nodes for retrieval/tactic proving, and
    parent/root-shaped partial theorem bodies become Lean-validated assembly
    contracts when they leave residual goals.
    """

    if dossier is None or proof_state is None or not helpers:
        return []
    target_task = str(target_task_id or "").strip()
    if target_task:
        candidate = proof_state.nodes.get(target_task)
        tasks = (
            [candidate]
            if candidate is not None
            and candidate.kind == "decomposition_task"
            and candidate.status == "open"
            else []
        )
    else:
        tasks = proof_state.decomposition_frontier(max_nodes=1)
    # D2 (2026-05-09, defense-in-depth): if a direct caller (tests,
    # future code) bypassed the gate-side opener and reaches here
    # with no open task, still open one ad hoc when sorry-stubs are
    # present. Production code paths are expected to call
    # ``ensure_decomposition_task_open_for_sorry_stubs`` upstream of
    # the gate that prevents reaching this function.
    if not tasks and not target_task:
        try:
            new_task_id = ensure_decomposition_task_open_for_sorry_stubs(
                proof_state,
                helpers,
                source="sorry_stub_helpers_volunteered:executor_inline",
            )
        except Exception:
            new_task_id = ""
        if not new_task_id and _lemma_dag_parent_stub_candidate_sources(
            proof_state,
            helpers,
        ):
            try:
                opener = getattr(proof_state, "ensure_decomposition_task_open", None)
                new_task_id = (
                    opener(
                        source="parent_stub_helpers_volunteered:executor_inline",
                        blocker=(
                            "LLM emitted parent proof stub as decomposition "
                            "assembly contract"
                        ),
                    )
                    if callable(opener)
                    else ""
                )
            except Exception:
                new_task_id = ""
        if new_task_id:
            new_task = proof_state.nodes.get(new_task_id)
            if new_task is not None:
                tasks = [new_task]
    if not tasks:
        return []
    task = tasks[0]
    accepted_helpers: List[str] = list(initial_accepted_helpers or ())
    candidate_records: List[Dict[str, Any]] = []
    candidate_node_ids: List[str] = list(initial_candidate_node_ids or ())
    proposed_count = max(0, int(initial_proposed_count or 0))
    accepted_count = max(0, int(initial_accepted_count or 0))
    initial_accepted_helper_count = len(accepted_helpers)
    new_node_count = 0
    reused_node_count = 0
    semantic_rejection_count = 0
    policy_rejection_count = 0
    retryable_deferred_count = 0
    batch_status: Dict[str, Any] = {}

    def _merge_retryable_status(
        status: Mapping[str, Any],
        *,
        helper_name: str = "",
    ) -> None:
        error_kind = str(status.get("error_kind") or "")
        retryable = str(status.get("status") or "") in {
            "retryable_error",
            "cancelled",
        }
        enclosing_deadline_elapsed = bool(
            float(deadline_monotonic or 0.0) > 0.0
            and time.monotonic() >= float(deadline_monotonic)
        )
        timeout = bool(
            retryable
            and (
                "timeout" in error_kind.lower()
                or "elapsed_budget_exhausted" in error_kind.lower()
                or "deadline" in error_kind.lower()
                or enclosing_deadline_elapsed
            )
        )
        for target in (
            batch_status,
            *([status_out] if status_out is not None else []),
        ):
            target["retryable_infrastructure"] = bool(
                target.get("retryable_infrastructure") or retryable
            )
            target["retryable_timeout"] = bool(
                target.get("retryable_timeout") or timeout
            )
            target["deadline_deferred"] = bool(
                target.get("deadline_deferred")
                or "elapsed_budget_exhausted" in error_kind.lower()
                or "deadline" in error_kind.lower()
                or enclosing_deadline_elapsed
            )
            if error_kind:
                target["error_kind"] = error_kind
            if helper_name:
                target["deferred_helper_name"] = helper_name
            target["deferred_node_id"] = task.node_id

    def _batch_record(verdict: str) -> Dict[str, Any]:
        return {
            "phase": "proof_state_lemma_dag_decomposition",
            "turn_in_phase": turn,
            "task_node_id": task.node_id,
            "candidate_count": len(candidate_records),
            "processed_candidate_count": len(candidate_records),
            "proposed_node_count": proposed_count,
            "new_node_count": new_node_count,
            "reused_node_count": reused_node_count,
            "accepted_helper_count": accepted_count,
            "accepted_helper_count_this_batch": max(
                0,
                len(accepted_helpers) - initial_accepted_helper_count,
            ),
            "semantic_rejection_count": semantic_rejection_count,
            "policy_rejection_count": policy_rejection_count,
            "retryable_deferred_count": retryable_deferred_count,
            "accepted_helpers": list(accepted_helpers),
            "candidate_records": list(candidate_records),
            "proof_state": proof_state.to_record(),
            "retryable_infrastructure": bool(
                batch_status.get("retryable_infrastructure")
            ),
            "retryable_timeout": bool(
                batch_status.get("retryable_timeout")
            ),
            "deadline_deferred": bool(
                batch_status.get("deadline_deferred")
            ),
            "error_kind": str(
                batch_status.get("error_kind") or ""
            ),
            "verdict": verdict,
        }

    def _publish_batch_record(verdict: str) -> None:
        record = _batch_record(verdict)
        if recorder is not None:
            recorder.record_turn(record)
        if records_out is not None:
            records_out.append(record)
        processed = int(record["processed_candidate_count"])
        _trace(
            trace_prefix,
            "  proof-state lemma-DAG batch processed "
            f"{processed} candidate(s): new {new_node_count}, "
            f"reused {reused_node_count}, "
            f"accepted {record['accepted_helper_count_this_batch']}, "
            f"rejected {semantic_rejection_count + policy_rejection_count}, "
            f"deferred {retryable_deferred_count}.",
        )
    ordered_helpers = order_helpers_for_incremental_validation(
        (
            str(helper or "").strip()
            for helper in helpers or ()
            if str(helper or "").strip()
        ),
        max_primary=8,
    )
    ordered_helpers = list(ordered_helpers)
    for parent_stub_source in _lemma_dag_parent_stub_candidate_sources(
        proof_state,
        helpers,
    )[:4]:
        parent_stub_closure = _helper_dependency_closure_sources(
            [parent_stub_source],
            list(helpers or ()),
        )
        closure_sources = set(parent_stub_closure)
        closure_names = {
            helper_decl_name(closure_source)
            for closure_source in parent_stub_closure
            if closure_source != parent_stub_source and helper_decl_name(closure_source)
        }
        ordered_helpers = [
            ordered_source
            for ordered_source in ordered_helpers
            if ordered_source not in closure_sources
            and helper_decl_name(ordered_source) not in closure_names
        ]
        for closure_source in parent_stub_closure:
            if closure_source not in ordered_helpers:
                ordered_helpers.append(closure_source)
    renamed_collisions: Dict[str, str] = {
        str(old): str(new)
        for old, new in dict(initial_renamed_collisions or {}).items()
        if str(old or "").strip() and str(new or "").strip()
    }
    for index, helper_block in enumerate(ordered_helpers, 1):
        source = str(helper_block or "").strip()
        for old_name, new_name in sorted(
            renamed_collisions.items(),
            key=lambda pair: (-len(str(pair[0]).split(".")), -len(pair[0])),
        ):
            source = _rename_helper_identifier(
                source,
                old_name,
                new_name,
            )
        helper_name = helper_decl_name(source) or ""
        statement = helper_decl_statement(source)
        if not helper_name or not statement:
            policy_rejection_count += 1
            source_rejection_recorder = getattr(
                proof_state,
                "record_lemma_dag_source_rejection",
                None,
            )
            if callable(source_rejection_recorder):
                source_rejection_recorder(
                    helper_name=helper_name,
                    target=statement or "",
                    accepted=False,
                    source=f"{task.node_id}:helper_{index}",
                    phase="proof_state_lemma_dag_helper",
                    turn_index=turn,
                    parent_node_id=task.node_id,
                    reason="missing_helper_name_or_statement",
                )
            candidate_records.append(
                {
                    "index": index,
                    "helper_name": helper_name,
                    "accepted": False,
                    "rejection": "missing_helper_name_or_statement",
                }
            )
            continue
        policy_rejection = _proof_state_helper_policy_rejection(source)
        body_text = helper_decl_body(source) or ""
        _no_block = re.sub(r"/-[\s\S]*?-/", "", body_text)
        _no_line = re.sub(r"--[^\n]*", "", _no_block)
        body_norm = " ".join(_no_line.split()).lower()
        is_sorry_stub = body_norm in {"by sorry", "by admit", "sorry", "admit"}
        parent_stub_reason = ""
        if not policy_rejection and not is_sorry_stub:
            parent_stub_continuation = {
                "kind": "lemma_dag_parent_stub_batch",
                "task_id": task.node_id,
                "parent_node_id": str(
                    task.parent_node_id or proof_state.root_node_id
                ),
                "helper_name": helper_name,
                "helper_block": source,
                "statement": statement,
                "source": f"{task.node_id}:helper_{index}",
                "phase": "proof_state_lemma_dag_helper",
                "turn_index": turn,
                "proposed_count": proposed_count,
                "accepted_count": accepted_count,
                "candidate_node_ids": list(candidate_node_ids),
                "remaining_helper_blocks": list(ordered_helpers[index:]),
                "renamed_collisions": dict(renamed_collisions),
                "max_parent_stub_goals": max_parent_stub_goals,
            }
            node_ids_before_parent_stub = set(proof_state.nodes)
            parent_stub_nodes, parent_stub_reason = (
                await _try_spawn_lemma_dag_parent_stub(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    task=task,
                    helper_name=helper_name,
                    statement=statement,
                    proof_stub=body_text,
                    source=f"{task.node_id}:helper_{index}",
                    phase="proof_state_lemma_dag_helper",
                    turn_index=turn,
                    timeout_s=float(timeout_s or 0.0),
                    max_goals=max_parent_stub_goals,
                    deadline_monotonic=deadline_monotonic,
                    producer_continuation=parent_stub_continuation,
                )
            )
            if parent_stub_nodes:
                candidate_node_ids.extend(parent_stub_nodes)
                proposed_count += len(parent_stub_nodes)
                for node_id in parent_stub_nodes:
                    if node_id in node_ids_before_parent_stub:
                        reused_node_count += 1
                    else:
                        new_node_count += 1
                        node_ids_before_parent_stub.add(node_id)
                candidate_records.append(
                    {
                        "index": index,
                        "node_ids": list(parent_stub_nodes),
                        "helper_name": helper_name,
                        "statement": statement,
                        "accepted": False,
                        "rejection": "",
                        "verdict": "parent_stub_residual_spawned",
                        "parent_stub_validation": parent_stub_reason,
                    }
                )
                continue
            if str(parent_stub_reason or "").endswith("_deferred"):
                retryable_deferred_count += 1
                deferred_error = str(parent_stub_reason or "")
                _merge_retryable_status(
                    {
                        "status": "retryable_error",
                        "error_kind": deferred_error,
                    },
                    helper_name=helper_name,
                )
                candidate_records.append(
                    {
                        "index": index,
                        "helper_name": helper_name,
                        "statement": statement,
                        "accepted": False,
                        "rejection": "",
                        "verdict": "parent_stub_residual_attestation_deferred",
                        "parent_stub_validation": parent_stub_reason,
                        "retryable_infrastructure": True,
                    }
                )
                # The exact stub/context is durable on its parent. Do not run
                # helper rejection or consume provider/math attempt authority.
                # Attach the producer's exact ordered suffix and graph commit
                # receipt to that verifier frame. The generic residual retry
                # can then finish the same lemma-DAG transition instead of
                # losing every later helper from this paid model response.
                parent = proof_state.nodes.get(task.parent_node_id) or (
                    proof_state.nodes.get(proof_state.root_node_id)
                )
                if parent is not None and parent.pending_residual_goal_extraction:
                    pending_residual = dict(
                        parent.pending_residual_goal_extraction
                    )
                    origin = dict(
                        pending_residual.get("origin_metadata") or {}
                    )
                    origin["producer_continuation"] = dict(
                        parent_stub_continuation
                    )
                    pending_residual["origin_metadata"] = origin
                    parent.pending_residual_goal_extraction = pending_residual
                # The task remains open and owns the saved continuation.
                _publish_batch_record("lemma_dag_helper_acceptance_deferred")
                return accepted_helpers
        accepted = False
        rejection = policy_rejection
        accept_status: Dict[str, Any] = {}
        if policy_rejection:
            policy_rejection_count += 1
        if not policy_rejection:
            continuation_kind = (
                "lemma_dag_parent_stub_closed"
                if parent_stub_reason == "parent_stub_closed_goal"
                else "lemma_dag"
            )
            staged_acceptance = stage_pending_helper_acceptance(
                conv=conv,
                dossier=dossier,
                node=task,
                helper_block=source,
                source=f"lemma_dag:{task.node_id}:helper_{index}",
                continuation={
                    "kind": continuation_kind,
                    "task_id": task.node_id,
                    "parent_node_id": str(
                        task.parent_node_id or proof_state.root_node_id
                    ),
                    "helper_name": helper_name,
                    "statement": statement,
                    "source": f"{task.node_id}:helper_{index}",
                    "phase": "proof_state_lemma_dag_helper",
                    "turn_index": turn,
                    "proposed_count": proposed_count,
                    "accepted_count": accepted_count,
                    "candidate_node_ids": list(candidate_node_ids),
                    "remaining_helper_blocks": list(ordered_helpers[index:]),
                    "renamed_collisions": dict(renamed_collisions),
                },
            )
            if not staged_acceptance:
                retryable_deferred_count += 1
                _merge_retryable_status(
                    {
                        "status": "retryable_error",
                        "error_kind": "pending_helper_acceptance_owned",
                    },
                    helper_name=helper_name,
                )
                candidate_records.append(
                    {
                        "index": index,
                        "helper_name": helper_name,
                        "statement": statement,
                        "accepted": False,
                        "rejection": "",
                        "verdict": "pending_helper_acceptance_owned",
                        "retryable_infrastructure": True,
                    }
                )
                _publish_batch_record("lemma_dag_helper_acceptance_deferred")
                return accepted_helpers
            accepted = await _accept_proof_state_helper(
                lean=lean,
                conv=conv,
                dossier=dossier,
                helper_block=source,
                phase="proof_state_lemma_dag_helper",
                turn_index=turn,
                timeout_s=float(timeout_s or 0.0),
                proof_cache=proof_cache,
                proof_state=proof_state,
                target_statement=str(getattr(task, "target", "") or ""),
                status_out=accept_status,
                deadline_monotonic=deadline_monotonic,
            )
            if accepted:
                task.pending_helper_acceptance = {}
                landed_helper_name = str(
                    accept_status.get("accepted_helper_name") or helper_name
                )
                if landed_helper_name != helper_name:
                    renamed_collisions[helper_name] = landed_helper_name
                    helper_name = landed_helper_name
                    source = str(
                        getattr(
                            dossier.verified_helpers.get(landed_helper_name),
                            "source",
                            source,
                        )
                        or source
                    )
                    statement = helper_decl_statement(source)
                accepted_helpers.append(helper_name)
                accepted_count += 1
                rejection = ""
            elif dossier.has_helper(helper_name):
                existing_helper_name = dossier.resolve_verified_helper_name(
                    helper_name
                )
                existing = dossier.verified_helpers.get(existing_helper_name)
                existing_statement = helper_decl_statement(
                    str(getattr(existing, "source", "") or "")
                )
                existing_source_hash = str(
                    getattr(existing, "source_hash", "") or ""
                ).strip()
                candidate_source_hash = text_hash(source)
                if (
                    canonicalize_lean_statement_for_identity(existing_statement)
                    == canonicalize_lean_statement_for_identity(statement)
                    and existing_source_hash
                    and existing_source_hash == candidate_source_hash
                ):
                    # Provenance equality is not a substitute for the
                    # authoritative recheck requested in the current Lean
                    # environment. A false result must remain a rejection.
                    rejection = "duplicate_helper_name_identical_source_recheck_failed"
                elif (
                    canonicalize_lean_statement_for_identity(existing_statement)
                    == canonicalize_lean_statement_for_identity(statement)
                ):
                    rejection = "duplicate_helper_name_rejected_proof"
                else:
                    rejection = "duplicate_helper_name_statement_mismatch"
            else:
                rejection = "lean_rejected_helper_proof"
            if str(accept_status.get("status") or "") in {
                "retryable_error",
                "cancelled",
            }:
                retryable_deferred_count += 1
                _merge_retryable_status(
                    accept_status,
                    helper_name=helper_name,
                )
                retain_pending_helper_acceptance_retry(
                    proof_state=proof_state,
                    node=task,
                    status=accept_status,
                )
                candidate_records.append(
                    {
                        "index": index,
                        "helper_name": helper_name,
                        "statement": statement,
                        "accepted": False,
                        "rejection": "",
                        "verdict": "helper_acceptance_deferred",
                        "retryable_infrastructure": True,
                    }
                )
                # The task and exact candidate remain durable. Closing the
                # decomposition here would turn infrastructure unavailability
                # into false mathematical evidence.
                _publish_batch_record("lemma_dag_helper_acceptance_deferred")
                return accepted_helpers
            task.pending_helper_acceptance = {}
        if accepted and parent_stub_reason == "parent_stub_closed_goal":
            _close_lemma_dag_task_with_parent_helper(
                proof_state=proof_state,
                task_id=task.node_id,
                parent_node_id=str(task.parent_node_id or proof_state.root_node_id),
                helper_name=helper_name,
                source=f"{task.node_id}:helper_{index}",
                phase="proof_state_lemma_dag_helper",
                turn_index=turn,
            )
            candidate_records.append(
                {
                    "index": index,
                    "node_id": "",
                    "helper_name": helper_name,
                    "statement": statement,
                    "accepted": True,
                    "rejection": "",
                    "verdict": "parent_stub_closed_goal_accepted",
                }
            )
            _publish_batch_record("lemma_dag_parent_stub_closed")
            return accepted_helpers
        # Phase 2 (2026-05-09): detect sorry-stub bodies to suppress the
        # failed_attempts bump on the resulting child_goal. The LLM's
        # ``:= by sorry`` is a decomposition request — registering it
        # is durable evidence; the rejection is structurally expected.
        #
        # Adversarial review fix: real LLM output frequently uses
        # multi-line / commented / whitespace-irregular forms:
        #   "by\n  sorry"
        #   "by  sorry"
        #   "by sorry  -- TODO"
        #   "by\n  -- explanation\n  sorry"
        #   "by\nsorry"
        #   "by\n    admit\n"
        # The naive ``body.strip().lower() in {...}`` check missed all
        # of these. Strip line/block comments first, then collapse
        # whitespace, then membership-test.
        prior_node_ids = set(proof_state.nodes)
        node_id = proof_state.record_lemma_dag_candidate(
            helper_name=helper_name,
            statement=statement,
            accepted=bool(accepted),
            source=f"{task.node_id}:helper_{index}",
            phase="proof_state_lemma_dag_helper",
            turn_index=turn,
            parent_node_id=task.node_id,
            rejection=rejection,
            is_sorry_stub_body=is_sorry_stub,
        )
        if node_id:
            proposed_count += 1
            candidate_node_ids.append(node_id)
            if node_id in prior_node_ids:
                reused_node_count += 1
            else:
                new_node_count += 1
        if not accepted and not policy_rejection:
            semantic_rejection_count += 1
        candidate_records.append(
            {
                "index": index,
                "node_id": node_id,
                "helper_name": helper_name,
                "statement": statement,
                "accepted": bool(accepted),
                "rejection": rejection,
            }
        )
    proof_state.close_decomposition_task_from_lemma_dag(
        task_id=task.node_id,
        proposed_count=proposed_count,
        accepted_count=accepted_count,
        node_ids=candidate_node_ids,
    )
    _publish_batch_record(
        "lemma_dag_helpers_accepted"
        if accepted_helpers
        else "lemma_dag_helpers_recorded"
    )
    return accepted_helpers


def _child_falsification_preflight_seen(
    node: ProofStateNode,
    context_key: str,
) -> bool:
    for transition in list(getattr(node, "typed_transitions", []) or []):
        if str(getattr(transition, "source", "") or "") != "falsification_preflight":
            continue
        payload = dict(getattr(transition, "payload", {}) or {})
        if (
            str(payload.get("context_key") or "") == context_key
            and bool(payload.get("completed"))
        ):
            return True
    return False


def _child_falsification_preflight_transient_seen(
    node: ProofStateNode,
    context_key: str,
) -> bool:
    """Whether this exact tactic context already spent its transient retry."""

    if context_key in set(
        getattr(node, "falsification_preflight_transient_context_keys", []) or []
    ):
        return True
    for transition in list(getattr(node, "typed_transitions", []) or []):
        if str(getattr(transition, "source", "") or "") != "falsification_preflight":
            continue
        payload = dict(getattr(transition, "payload", {}) or {})
        if (
            str(payload.get("context_key") or "") == context_key
            and not bool(payload.get("completed"))
        ):
            return True
    return False


def _remember_child_falsification_preflight_transient(
    node: ProofStateNode,
    context_key: str,
) -> None:
    keys = getattr(node, "falsification_preflight_transient_context_keys", None)
    if not isinstance(keys, list):
        keys = []
        node.falsification_preflight_transient_context_keys = keys
    if context_key not in keys:
        keys.append(context_key)
        del keys[:-24]


def _proof_state_child_tactic_terminal_context_key(
    *,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    timeout_s: float,
    max_candidates: int,
) -> str:
    timeout_value = max(0.0, float(timeout_s or 0.0))
    timeout_class = (
        "adequate"
        if timeout_value >= 30.0
        else f"constrained_{int(timeout_value // 5.0) * 5}"
    )
    preamble = _proof_state_residual_preamble(conv)
    helpers = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    pattern_context = _proof_state_tactic_pattern_context(
        proof_state,
        node,
        scope="proof_state_child_tactic",
        mode="child_residual",
    )
    pattern_context.update(
        {
            "tactic_timeout_class": timeout_class,
            "max_candidates": str(max(0, int(max_candidates or 0))),
        }
    )
    return text_hash(
        json.dumps(
            {
                "target": node.target,
                "preamble": preamble,
                "helpers": helpers,
                "pattern_context": pattern_context,
                "tactic_timeout_class": timeout_class,
                "suppress_solution_placeholders": bool(
                    getattr(conv, "suppress_solution_placeholders", True)
                ),
                "opaque_mode": bool(
                    getattr(conv, "opaque_mode", getattr(dossier, "opaque_mode", True))
                ),
                "allow_official_answer_visibility": bool(
                    getattr(
                        conv,
                        "allow_official_answer_visibility",
                        getattr(dossier, "allow_official_answer_visibility", False),
                    )
                ),
                "official_answer_payload_present": getattr(
                    conv,
                    "official_answer_payload_present",
                    getattr(dossier, "official_answer_payload_present", None),
                ),
            },
            sort_keys=True,
            default=str,
        )
    )


def _remember_child_tactic_timeout_retry(
    node: ProofStateNode,
    context_key: str,
) -> None:
    keys = getattr(node, "tactic_timeout_retry_context_keys", None)
    if not isinstance(keys, list):
        keys = []
        node.tactic_timeout_retry_context_keys = keys
    if context_key not in keys:
        keys.append(context_key)
        del keys[:-16]


async def _try_proof_state_child_falsification_preflight(
    *,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    preamble: str,
    helpers: Sequence[str],
    turn: int,
    timeout_s: float,
    deadline_monotonic: float = 0.0,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> Tuple[bool, Dict[str, Any]]:
    """Run one bounded, certificate-authoritative falsification gate."""

    if bool(getattr(node, "falsified", False)):
        return True, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "already_authoritatively_falsified",
            "certificate_hash": str(
                getattr(node, "falsification_certificate_hash", "") or ""
            ),
        }
    budget_s = min(15.0, max(0.0, float(timeout_s or 0.0)))
    if budget_s < 1.0:
        return False, {}
    node_environment_hash = str(
        getattr(node, "statement_environment_hash", "") or ""
    ).strip()
    dossier_environment_hash = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    if (
        not node_environment_hash
        or not dossier_environment_hash
        or node_environment_hash != dossier_environment_hash
    ):
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "node_environment_hash": node_environment_hash,
            "dossier_environment_hash": dossier_environment_hash,
            "verdict": "falsification_environment_mismatch",
        }
    binders, body = leading_forall_binders(str(node.target or ""))
    domains = tuple(binder_domain(item.type_text) for item in binders)
    numeric_literals = [
        abs(int(item))
        for item in re.findall(r"(?<![A-Za-z0-9_'])-?[0-9]+", body)
    ]
    numeric_stress_target = bool(
        numeric_literals and max(numeric_literals) >= 8
    )
    if (
        binders
        and all(domain in {"nat", "int", "rat"} for domain in domains)
        and numeric_stress_target
    ):
        preflight_engines = ("structural", "numeric")
    elif (
        binders
        and all(
            domain in {"int", "rat", "real", "complex"}
            for domain in domains
        )
        and any(
            token in body
            for token in ("=", "≠", "<", "≤", ">", "≥", "+", "-", "*", "^", "/")
        )
    ):
        preflight_engines = ("structural", "exact_algebra")
    else:
        preflight_engines = ("structural", "finite")
    policy = FalsificationPolicy(
        engines=preflight_engines,
        max_candidates_per_engine=12,
        max_finite_checks=12,
        max_numeric_examples=12,
        operation_timeout_s=min(5.0, budget_s),
        engine_timeout_s=budget_s,
        aggregate_timeout_s=budget_s,
    )
    context_key = text_hash(
        json.dumps(
            {
                "target": str(node.target or ""),
                "preamble": str(preamble or ""),
                "helpers": list(helpers or ()),
                "policy_hash": policy.policy_hash,
                "node_environment_hash": node_environment_hash,
                "dossier_environment_hash": dossier_environment_hash,
            },
            sort_keys=True,
            default=str,
        )
    )
    if _child_falsification_preflight_seen(node, context_key):
        return bool(getattr(node, "falsified", False)), {}
    if _child_falsification_preflight_transient_seen(node, context_key):
        # A preflight infrastructure failure may defer tactic search once, but
        # must not permanently monopolize the exact tactic frontier.  Lean still
        # validates every tactic candidate, so bypassing a repeatedly unavailable
        # advisory falsifier does not weaken proof soundness.
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "falsification_transient_bypassed",
            "retryable_infrastructure": False,
            "retryable_timeout": False,
        }

    def dispatch_replaced() -> bool:
        try:
            return bool(deadline_exhausted and deadline_exhausted())
        except Exception:
            return True

    def remember_transient(error_kind: str, blocker: str, *, timeout: bool) -> None:
        if dispatch_replaced():
            return
        # Deadline rollback may replace ``proof_state.nodes`` with a snapshot,
        # so always resolve the live node instead of mutating a stale argument.
        live_node = proof_state.nodes.get(node.node_id) or node
        _remember_child_falsification_preflight_transient(live_node, context_key)
        proof_state.record_transition(
            node_id=live_node.node_id,
            source="falsification_preflight",
            error_type="child_goal_falsification_preflight_transient",
            action=live_node.action,
            blocker=str(blocker or "")[:500],
            phase="proof_state_child_falsification",
            turn_index=turn,
            payload={
                "context_key": context_key,
                "completed": False,
                "infrastructure_exception": str(error_kind or ""),
                "retryable_timeout": bool(timeout),
            },
        )

    try:
        falsification_lean = _SerializedFalsificationLeanProxy(
            lean,
            timeout_s=budget_s,
            deadline_monotonic=deadline_monotonic,
        )
        report = await await_with_strict_deadline(
            FalsificationService(policy=policy).falsify(
                falsification_lean,
                statement=node.target,
                target_kind=TargetKind.HELPER,
                preamble=str(preamble or ""),
                helpers=tuple(helpers or ()),
            ),
            timeout_s=budget_s,
            deadline_monotonic=deadline_monotonic,
            operation_label="proof_state_child_falsification",
            operation_ownership="result_only",
        )
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        retryable_timeout = isinstance(exc, (asyncio.TimeoutError, TimeoutError))
        remember_transient(
            type(exc).__name__,
            f"{type(exc).__name__}: {exc}",
            timeout=retryable_timeout,
        )
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "falsification_infrastructure_error",
            "error": f"{type(exc).__name__}: {exc}"[:500],
            "retryable_infrastructure": True,
            "retryable_timeout": retryable_timeout,
        }
    if dispatch_replaced():
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "falsification_dispatch_replaced_before_commit",
            "retryable_infrastructure": True,
            "retryable_timeout": False,
        }
    if (
        float(deadline_monotonic or 0.0) > 0.0
        and time.monotonic() >= float(deadline_monotonic)
    ):
        remember_transient(
            "deadline_expired_before_commit",
            "falsification deadline expired before commit",
            timeout=True,
        )
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "falsification_deadline_expired_before_commit",
            "retryable_infrastructure": True,
            "retryable_timeout": True,
        }
    def commit_deadline_exhausted() -> bool:
        return bool(
            dispatch_replaced()
            or (
                float(deadline_monotonic or 0.0) > 0.0
                and time.monotonic() >= float(deadline_monotonic)
            )
        )

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=commit_deadline_exhausted,
        dossier=dossier,
        proof_state=proof_state,
        label="proof_state_child_falsification_commit",
    )
    outcome = getattr(report, "outcome", FalsificationOutcome.INCONCLUSIVE)
    completed = outcome is not FalsificationOutcome.TRANSIENT_FAILURE
    transient_error_kinds = {
        str(getattr(finding, "error_kind", "") or "").strip().lower()
        for finding in tuple(getattr(report, "findings", ()) or ())
    }
    retryable_infrastructure = outcome is FalsificationOutcome.TRANSIENT_FAILURE
    retryable_timeout = bool(
        retryable_infrastructure and "timeout" in transient_error_kinds
    )
    promoted = False
    certificate = getattr(report, "authoritative_refutation", None)
    certificate_hash = ""
    terminalized: Tuple[str, ...] = ()
    falsified = False
    unpromoted_refutation_candidate = False
    advisory_candidate_hash = ""
    deadline_verdict = ""
    with transaction:
        if not transaction.can_mutate():
            deadline_verdict = "falsification_deadline_expired_before_commit"
        else:
            promoted = bool(dossier.record_falsification_report(report))
            if certificate is not None:
                certificate_hash = str(
                    certificate.to_record().get("certificate_hash") or ""
                )
                try:
                    from .mini_session.child_goal_falsification import (
                        terminalize_exact_proof_state_aliases,
                    )

                    terminalized = terminalize_exact_proof_state_aliases(
                        parent_session=SimpleNamespace(
                            proof_state=proof_state,
                            iteration=turn,
                        ),
                        dossier=dossier,
                        statement=node.target,
                        certificate_hash=certificate_hash,
                        target_environment_hash=str(
                            getattr(
                                dossier,
                                "current_lean_environment_hash",
                                "",
                            )
                            or ""
                        ).strip(),
                        reason="bounded child preflight proved and audited not goal",
                    )
                except Exception:
                    terminalized = ()
            falsified = bool(node.node_id in terminalized and node.falsified)
            if certificate is not None and not falsified:
                completed = False
            advisory_candidates = (
                dossier.lean_checked_unpromoted_refutation_candidates_for_statement(
                    node.target
                )
            )
            unpromoted_refutation_candidate = bool(advisory_candidates)
            if advisory_candidates:
                advisory_candidate_hash = text_hash(
                    json.dumps(
                        advisory_candidates,
                        sort_keys=True,
                        separators=(",", ":"),
                        default=str,
                    )
                )
            live_node = proof_state.nodes.get(node.node_id) or node
            live_node.falsification_advisory_candidate_hash = (
                "" if falsified else advisory_candidate_hash
            )
            proof_state.record_transition(
                node_id=node.node_id,
                source="falsification_preflight",
                error_type=(
                    "child_goal_lean_falsified"
                    if falsified
                    else "child_goal_falsification_preflight_complete"
                    if completed
                    else "child_goal_falsification_preflight_transient"
                ),
                action="retire_false_route" if falsified else node.action,
                blocker=(
                    "authoritative negation certificate"
                    if falsified
                    else str(getattr(outcome, "value", outcome) or "")
                ),
                phase="proof_state_child_falsification",
                turn_index=turn,
                payload={
                    "context_key": context_key,
                    "completed": completed,
                    "promoted": promoted,
                    "certificate_hash": certificate_hash,
                    "terminalized_node_ids": list(terminalized),
                    "unpromoted_refutation_candidate": (
                        unpromoted_refutation_candidate
                    ),
                    "advisory_candidate_hash": advisory_candidate_hash,
                },
            )
            if not completed:
                _remember_child_falsification_preflight_transient(node, context_key)
            if not transaction.can_mutate():
                deadline_verdict = "falsification_deadline_expired_during_commit"
    if deadline_verdict:
        remember_transient(
            deadline_verdict,
            deadline_verdict.replace("_", " "),
            timeout=True,
        )
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": deadline_verdict,
            "retryable_infrastructure": True,
            "retryable_timeout": True,
        }
    if transaction.enabled and not transaction.committed:
        remember_transient(
            "falsification_deadline_rollback",
            "falsification deadline rollback",
            timeout=True,
        )
        return False, {
            "phase": "proof_state_child_falsification",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "verdict": "falsification_deadline_rollback",
            "retryable_infrastructure": True,
            "retryable_timeout": True,
        }
    return falsified, {
        "phase": "proof_state_child_falsification",
        "turn_in_phase": turn,
        "node_id": node.node_id,
        "target": node.target,
        "outcome": str(getattr(outcome, "value", outcome) or ""),
        "certificate_hash": certificate_hash,
        "terminalized_node_ids": list(terminalized),
        "retryable_infrastructure": retryable_infrastructure,
        "retryable_timeout": retryable_timeout,
        "unpromoted_refutation_candidate": unpromoted_refutation_candidate,
        "advisory_candidate_hash": advisory_candidate_hash,
        "verdict": (
            "child_falsified"
            if falsified
            else "falsification_transient_failure"
            if retryable_infrastructure
            else "falsification_complete"
        ),
    }


async def _try_proof_state_one_child_closure(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: ProofStateNode,
    trace_prefix: str,
    turn: int,
    timeout_s: float,
    max_candidates: int,
    max_decl_applications: int,
    max_residual_goals: int,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    allowed_work_types: Optional[Sequence[str]] = None,
    formal_search_config: Optional[Any] = None,
    formal_search_client: Optional[Any] = None,
    cost_controller: Optional[Any] = None,
    action_deadline_monotonic: float = 0.0,
) -> Tuple[List[str], List[Dict[str, Any]]]:
    """Run the declaration/tactic/assembler swarm for one proof-state node."""

    accepted_helpers: List[str] = []
    records: List[Dict[str, Any]] = []
    allowed = {
        str(item or "").strip()
        for item in list(allowed_work_types or ())
        if str(item or "").strip()
    }
    allow_parent_assembly = not allowed or "assembly" in allowed
    allow_decl_probe = not allowed or "decl_probe" in allowed
    allow_tactic_swarm = not allowed or "tactic_swarm" in allowed

    if bool(getattr(node, "falsified", False)):
        proof_state.positive_close_blocked_by_falsification(
            node,
            source="child_closure_entry",
            phase="proof_state_child_closure",
            turn_index=turn,
        )
        return [], records

    def _remaining_timeout(default_s: float) -> float:
        return _fully_funded_operation_timeout(
            default_s,
            action_deadline_monotonic,
        )

    def _acceptance_deadline_expired(status: Mapping[str, Any]) -> bool:
        error_kind = str(status.get("error_kind") or "").lower()
        return bool(
            (
                float(action_deadline_monotonic or 0.0) > 0.0
                and time.monotonic() >= float(action_deadline_monotonic)
            )
            or "elapsed_budget_exhausted" in error_kind
        )

    def _acceptance_retryable(status: Mapping[str, Any]) -> bool:
        return bool(
            str(status.get("status") or "")
            in {
                "retryable_error",
                "cancelled",
            }
            or _acceptance_deadline_expired(status)
        )

    def _stage_pending_acceptance(
        helper_block: str,
        *,
        source: str,
        context_hash: str = "",
        continuation: Optional[Mapping[str, Any]] = None,
    ) -> bool:
        return stage_pending_helper_acceptance(
            conv=conv,
            dossier=dossier,
            node=node,
            helper_block=helper_block,
            source=source,
            context_hash=context_hash,
            continuation=dict(continuation or {"kind": source}),
        )

    def _settle_deferred_tactic_candidate(
        continuation: Mapping[str, Any],
        *,
        accepted: bool,
        helper_name: str = "",
    ) -> None:
        """Commit the original tactic producer receipt exactly once."""

        attempt_count = max(
            1,
            _durable_nonnegative_int(continuation.get("attempt_count")),
        )
        terminal_context_key = str(
            continuation.get("terminal_context_key") or ""
        )
        # The producer's base cache metrics are committed when the tactic
        # result first returns. The verifier WAL owns only the later
        # acceptance delta; replaying the aggregate here would double-count
        # lookups/hits on every transient acceptance failure.
        producer_cache_metadata = dict(
            continuation.get("cache_metadata") or {}
        )
        cache_metadata: Dict[str, Any] = {
            "enabled": bool(producer_cache_metadata.get("enabled", False))
        }
        success_attempt = dict(continuation.get("success_attempt") or {})
        pattern_cache = _proof_state_tactic_pattern_cache(proof_state)
        candidate = TacticPatternCache.candidate_from_attempt(success_attempt)
        if candidate is not None:
            tactic_preamble = _proof_state_residual_preamble(conv)
            tactic_helpers = _proof_state_residual_lemmas(
                conv,
                _proof_state_verified_helper_blocks(dossier),
            )
            pattern_context = _proof_state_tactic_pattern_context(
                proof_state,
                node,
                scope="proof_state_child_tactic",
                mode="child_residual",
            )
            pattern_context.update(
                {
                    "tactic_timeout_s": str(
                        round(max(0.0, float(timeout_s or 0.0)), 3)
                    ),
                    "max_candidates": str(
                        max(0, int(max_candidates or 0))
                    ),
                }
            )
            cache_delta = (
                pattern_cache.confirm_success(
                    goal_statement=node.target,
                    preamble=tactic_preamble,
                    helpers=tactic_helpers,
                    candidate=candidate,
                    pattern_context=pattern_context,
                    suppress_solution_placeholders=bool(
                        getattr(conv, "suppress_solution_placeholders", True)
                    ),
                    opaque_mode=bool(getattr(conv, "opaque_mode", True)),
                    allow_official_answer_visibility=bool(
                        getattr(
                            conv,
                            "allow_official_answer_visibility",
                            False,
                        )
                    ),
                )
                if accepted
                else pattern_cache.record_acceptance_veto(
                    goal_statement=node.target,
                    preamble=tactic_preamble,
                    helpers=tactic_helpers,
                    candidate=candidate,
                    pattern_context=pattern_context,
                    suppress_solution_placeholders=bool(
                        getattr(conv, "suppress_solution_placeholders", True)
                    ),
                    opaque_mode=bool(getattr(conv, "opaque_mode", True)),
                    allow_official_answer_visibility=bool(
                        getattr(
                            conv,
                            "allow_official_answer_visibility",
                            False,
                        )
                    ),
                )
            )
            cache_metadata = _merge_tactic_cache_metadata(
                cache_metadata,
                cache_delta,
            )
        elif not accepted:
            cache_metadata = _merge_tactic_cache_metadata(
                cache_metadata,
                {"acceptance_vetoes": 1},
            )
        setattr(proof_state, "_tactic_pattern_cache", pattern_cache)
        proof_state.record_tactic_pattern_cache_metrics(cache_metadata)
        proof_state.record_tactic_result(
            node_id=node.node_id,
            ok=accepted,
            attempt_count=attempt_count,
            exit_reason=(
                "solved_after_verifier_retry"
                if accepted
                else "acceptance_vetoed_after_verifier_retry"
            ),
            helper_name=helper_name if accepted else "",
            terminal_context_key=terminal_context_key,
            terminal_for_context=False,
        )

    def _settle_deferred_formal_candidate(
        continuation: Mapping[str, Any],
        *,
        accepted: bool,
        helper_name: str = "",
    ) -> None:
        attempt_count = _durable_nonnegative_int(
            continuation.get("attempt_count")
        )
        proof_state.record_tactic_result(
            node_id=node.node_id,
            ok=accepted,
            attempt_count=attempt_count,
            exit_reason=(
                "solved_by_formal_state_search_after_verifier_retry"
                if accepted
                else "formal_search_acceptance_vetoed_after_verifier_retry"
            ),
            helper_name=helper_name if accepted else "",
        )
        proof_state.record_transition(
            node_id=node.node_id,
            source="goal_conditioned_formal_search",
            error_type="" if accepted else "formal_candidate_acceptance_vetoed",
            action=(
                "formal_state_helper_accepted"
                if accepted
                else "backtrack_from_formal_candidate"
            ),
            blocker=(
                ""
                if accepted
                else "authoritative helper acceptance rejected candidate"
            ),
            phase="proof_state_formal_search",
            turn_index=turn,
            payload={
                "context_hash": str(
                    continuation.get("context_hash") or ""
                ),
                "deferred_acceptance_settlement": True,
            },
        )
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            increment(
                (
                    "mini_formal_state_search_solved"
                    if accepted
                    else "mini_formal_state_search_acceptance_vetoes"
                ),
                1,
            )

    async def _retry_pending_acceptance() -> Tuple[bool, List[str]]:
        pending = dict(getattr(node, "pending_helper_acceptance", {}) or {})
        if not pending:
            return False, []
        helper_block = str(pending.get("helper_block") or "").strip()
        if (
            not helper_block
            or str(pending.get("target_hash") or "") != text_hash(node.target)
        ):
            node.pending_helper_acceptance = {}
            return False, []
        helper_name = helper_decl_name(helper_block) or ""
        caller_context_hash = str(
            pending.get("caller_context_hash")
            if "caller_context_hash" in pending
            else pending.get("context_hash") or ""
        )
        request_hash, exact_context_hash, retry_key = (
            _helper_acceptance_request_hashes(
                conv=conv,
                dossier=dossier,
                node=node,
                helper_block=helper_block,
                source=str(pending.get("source") or ""),
                context_hash=caller_context_hash,
            )
        )
        if str(pending.get("acceptance_request_hash") or "") != request_hash:
            prior_retry_key = str(pending.get("verifier_retry_key") or "").strip()
            pending["attempt_count"] = "0"
            pending["acceptance_request_hash"] = request_hash
            pending["context_hash"] = exact_context_hash
            pending["caller_context_hash"] = caller_context_hash
            pending["verifier_retry_key"] = retry_key
            pending.pop("verifier_failure", None)
            node.pending_helper_acceptance = pending
            if prior_retry_key and prior_retry_key != retry_key:
                proof_state.clear_verifier_retry_state(node, prior_retry_key)
        if proof_state.verifier_retry_status(node, retry_key) == "cooling":
            records.append(
                {
                    "phase": "proof_state_pending_acceptance",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": helper_name,
                    "pending_source": str(pending.get("source") or ""),
                    "retryable_infrastructure": True,
                    "verdict": "pending_acceptance_cooling",
                }
            )
            return True, []
        acceptance_status: Dict[str, Any] = {}
        pending_acceptance_timeout_s = _typed_residual_operation_timeout(
            lean,
            timeout_s,
        )
        continuation = dict(pending.get("continuation") or {})
        continuation_kind = str(continuation.get("kind") or "")
        cache_seed_batch_receipt = (
            _cached_seed_batch_receipt(
                proof_state,
                str(continuation.get("batch_receipt_key") or ""),
            )
            if continuation_kind == "cache_seed_batch"
            else None
        )
        cache_seed_batch_context: Optional[List[str]] = None
        cache_seed_batch_admission: Optional[_CacheSeedBatchAdmission] = None
        if cache_seed_batch_receipt is not None:
            cache_seed_batch_admission = cache_seed_batch_receipt.admission(
                conv=conv,
                dossier=dossier,
                helper_block=helper_block,
            )
            if cache_seed_batch_admission is not None:
                cache_seed_batch_context = list(
                    cache_seed_batch_admission.context
                )
        accepted = await _accept_proof_state_helper(
            lean=lean,
            conv=conv,
            dossier=dossier,
            helper_block=helper_block,
            phase="proof_state_pending_acceptance",
            turn_index=turn,
            timeout_s=_remaining_timeout(pending_acceptance_timeout_s),
            proof_cache=proof_cache,
            proof_state=proof_state,
            target_statement=node.target,
            deadline_monotonic=action_deadline_monotonic,
            status_out=acceptance_status,
            cache_seed_batch_receipt=cache_seed_batch_receipt,
            cache_seed_batch_context=cache_seed_batch_context,
            cache_seed_batch_admission=cache_seed_batch_admission,
        )
        if accepted:
            helper_name = str(
                acceptance_status.get("accepted_helper_name") or helper_name
            )
            proof_state.clear_verifier_retry_state(node, retry_key)
            # The verified candidate is now durably represented by the
            # dossier. Release its write-ahead slot before dispatching the
            # typed producer continuation: a batch continuation may need to
            # stage the next already-paid candidate in the same slot.
            node.pending_helper_acceptance = {}
            if proof_state.positive_close_blocked_by_falsification(
                node,
                source=f"pending_acceptance:{continuation_kind or 'unknown'}",
                phase="proof_state_pending_acceptance",
                turn_index=turn,
                helper_name=helper_name,
            ):
                records.append(
                    {
                        "phase": "proof_state_pending_acceptance",
                        "turn_in_phase": turn,
                        "node_id": node.node_id,
                        "target": node.target,
                        "helper_name": helper_name,
                        "pending_source": str(pending.get("source") or ""),
                        "accepted": False,
                        "verdict": (
                            "accepted_helper_discarded_after_falsification"
                        ),
                    }
                )
                return True, []
            resumed_helper_names: List[str] = [helper_name] if helper_name else []
            if continuation_kind == "assembly":
                assembly_id = str(
                    continuation.get("assembly_id") or ""
                )
                for group in node.assembly_attempt_groups:
                    if group.assembly_id != assembly_id:
                        continue
                    group.status = "proved"
                    group.attempt_count += max(
                        1,
                        _durable_nonnegative_int(
                            continuation.get("candidate_index")
                        ),
                    )
                    group.last_attempt_witness = tuple(
                        str(item)
                        for item in list(
                            continuation.get("attempt_witness") or ()
                        )
                    )
                    break
                proof_state.record_assembly_result(
                    node_id=node.node_id,
                    ok=True,
                    attempt_count=max(
                        1,
                        _durable_nonnegative_int(
                            continuation.get("candidate_index")
                        ),
                    ),
                    exit_reason="assembled_from_children_after_verifier_retry",
                    helper_name=helper_name,
                )
            elif continuation_kind == "cache_hit":
                proof_state.record_cache_hit(
                    node_id=node.node_id,
                    helper_name=helper_name,
                )
            elif continuation_kind == "cache_seed_batch":
                remaining_cache_records = [
                    dict(item)
                    for item in list(
                        continuation.get("remaining_cache_records") or ()
                    )
                    if isinstance(item, Mapping)
                ]
                if remaining_cache_records:
                    cache_summary = await seed_verified_helpers_from_same_problem_cache(
                        lean=lean,
                        conv=conv,
                        dossier=dossier,
                        proof_state=proof_state,
                        proof_cache=None,
                        theorem_name=str(
                            continuation.get("theorem_name")
                            or getattr(dossier, "theorem_name", "")
                        ),
                        timeout_s=_remaining_timeout(
                            float(continuation.get("timeout_s") or timeout_s)
                        ),
                        max_helpers=len(remaining_cache_records),
                        _candidate_records=remaining_cache_records,
                        _batch_receipt_key=str(
                            continuation.get("batch_receipt_key") or ""
                        ),
                    )
                    resumed_helper_names.extend(
                        item
                        for item in list(
                            cache_summary.get("accepted_helper_names") or ()
                        )
                        if item and item not in resumed_helper_names
                    )
            elif continuation_kind == "decl_application":
                proof_state.record_decl_application_result(
                    node_id=node.node_id,
                    ok=True,
                    attempt_count=max(
                        1,
                        _durable_nonnegative_int(pending.get("attempt_count")),
                    ),
                    exit_reason=(
                        "closed_by:"
                        + str(continuation.get("decl_name") or "declaration")
                        + "_after_verifier_retry"
                    ),
                    helper_name=helper_name,
                    decl_application_signature=str(
                        continuation.get("decl_application_signature")
                        or node.decl_application_signature
                        or ""
                    ),
                )
            elif continuation_kind == "lemma_dag_parent_stub_closed":
                _close_lemma_dag_task_with_parent_helper(
                    proof_state=proof_state,
                    task_id=str(continuation.get("task_id") or node.node_id),
                    parent_node_id=str(
                        continuation.get("parent_node_id")
                        or node.parent_node_id
                        or proof_state.root_node_id
                    ),
                    helper_name=helper_name,
                    source=str(continuation.get("source") or ""),
                    phase=str(
                        continuation.get("phase")
                        or "proof_state_lemma_dag_helper"
                    ),
                    turn_index=_durable_nonnegative_int(
                        continuation.get("turn_index")
                    ),
                )
            elif continuation_kind == "lemma_dag":
                prior_node_ids = [
                    str(item)
                    for item in list(
                        continuation.get("candidate_node_ids") or ()
                    )
                    if str(item or "").strip()
                ]
                candidate_node_id = proof_state.record_lemma_dag_candidate(
                    helper_name=helper_name,
                    statement=(
                        helper_decl_statement(helper_block)
                        or str(continuation.get("statement") or "")
                    ),
                    accepted=True,
                    source=str(continuation.get("source") or ""),
                    phase=str(
                        continuation.get("phase")
                        or "proof_state_lemma_dag_helper"
                    ),
                    turn_index=_durable_nonnegative_int(
                        continuation.get("turn_index")
                    ),
                    parent_node_id=str(
                        continuation.get("task_id") or node.node_id
                    ),
                )
                if candidate_node_id:
                    prior_node_ids.append(candidate_node_id)
                proposed_count = (
                    _durable_nonnegative_int(
                        continuation.get("proposed_count")
                    )
                    + int(bool(candidate_node_id))
                )
                accepted_count = (
                    _durable_nonnegative_int(
                        continuation.get("accepted_count")
                    )
                    + 1
                )
                remaining_helper_blocks = [
                    str(item or "").strip()
                    for item in list(
                        continuation.get("remaining_helper_blocks") or ()
                    )
                    if str(item or "").strip()
                ]
                if remaining_helper_blocks:
                    # A provider response is one paid ordered batch. Resume
                    # its unvisited suffix before closing the decomposition
                    # task; otherwise a transient verifier failure on the
                    # first candidate silently discards every later lemma.
                    renamed_collisions = {
                        str(old): str(new)
                        for old, new in dict(
                            continuation.get("renamed_collisions") or {}
                        ).items()
                    }
                    original_helper_name = str(
                        continuation.get("helper_name") or ""
                    ).strip()
                    if (
                        original_helper_name
                        and helper_name
                        and helper_name != original_helper_name
                    ):
                        renamed_collisions[original_helper_name] = helper_name
                    suffix_status: Dict[str, Any] = {}
                    suffix_records: List[Dict[str, Any]] = []
                    suffix_helpers = await _try_proof_state_lemma_dag_helpers(
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        helpers=remaining_helper_blocks,
                        recorder=None,
                        trace_prefix=trace_prefix,
                        turn=turn,
                        timeout_s=_remaining_timeout(timeout_s),
                        deadline_monotonic=action_deadline_monotonic,
                        proof_cache=proof_cache,
                        target_task_id=str(
                            continuation.get("task_id") or node.node_id
                        ),
                        max_parent_stub_goals=max_residual_goals,
                        initial_proposed_count=proposed_count,
                        initial_accepted_count=accepted_count,
                        initial_candidate_node_ids=prior_node_ids,
                        initial_accepted_helpers=[helper_name],
                        initial_renamed_collisions=renamed_collisions,
                        status_out=suffix_status,
                        records_out=suffix_records,
                    )
                    records.extend(suffix_records)
                    resumed_helper_names.extend(
                        item
                        for item in suffix_helpers
                        if item and item not in resumed_helper_names
                    )
                else:
                    proof_state.close_decomposition_task_from_lemma_dag(
                        task_id=str(
                            continuation.get("task_id") or node.node_id
                        ),
                        proposed_count=proposed_count,
                        accepted_count=accepted_count,
                        node_ids=prior_node_ids,
                    )
            elif continuation_kind == "recursive_helper":
                proof_state.record_lemma_dag_candidate(
                    helper_name=helper_name,
                    statement=(
                        helper_decl_statement(helper_block)
                        or str(continuation.get("statement") or node.target)
                    ),
                    accepted=True,
                    source=str(
                        continuation.get("source")
                        or f"recursive_helper_prover:{node.node_id}"
                    ),
                    phase=str(
                        continuation.get("phase") or "recursive_helper_prover"
                    ),
                    turn_index=_durable_nonnegative_int(
                        continuation.get("turn_index")
                    ),
                    target_node_id=str(
                        continuation.get("target_node_id") or node.node_id
                    ),
                )
            elif continuation_kind == "tactic_swarm":
                _settle_deferred_tactic_candidate(
                    continuation,
                    accepted=True,
                    helper_name=helper_name,
                )
            elif continuation_kind == "formal_state_search":
                _settle_deferred_formal_candidate(
                    continuation,
                    accepted=True,
                    helper_name=helper_name,
                )
            records.append(
                {
                    "phase": "proof_state_pending_acceptance",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": helper_name,
                    "pending_source": str(pending.get("source") or ""),
                    "verdict": "helper_accepted",
                }
            )
            return True, resumed_helper_names
        if _acceptance_retryable(acceptance_status):
            deadline_retry = _acceptance_deadline_expired(acceptance_status)
            retain_pending_helper_acceptance_retry(
                proof_state=proof_state,
                node=node,
                status=acceptance_status,
            )
            pending = dict(node.pending_helper_acceptance or {})
            attempt_count = _durable_nonnegative_int(
                pending.get("attempt_count", 0)
            )
            # Transport, cancellation, and deadline failures are not evidence
            # against this already-paid candidate. Keep it durably retryable;
            # scheduler backoff rotates other live work after the first retry,
            # while normal session iterations still bound persistent outages.
            retry_exhausted = False
            error_kind = str(
                acceptance_status.get("error_kind")
                or "acceptance_infrastructure_failure"
            )
            records.append(
                {
                    "phase": "proof_state_pending_acceptance",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": helper_name,
                    "pending_source": str(pending.get("source") or ""),
                    "error_kind": error_kind,
                    "retryable_infrastructure": not retry_exhausted,
                    "retryable_timeout": bool(
                        deadline_retry and not retry_exhausted
                    ),
                    "retry_exhausted": retry_exhausted,
                    "acceptance_attempt_count": attempt_count,
                    "verdict": (
                        "pending_acceptance_retry_exhausted"
                        if retry_exhausted
                        else "pending_acceptance_retryable"
                    ),
                }
            )
            return True, []
        # A completed authoritative rejection is semantic evidence. Clear the
        # candidate and allow the normal search lanes to find another proof.
        proof_state.clear_verifier_retry_state(node, retry_key)
        continuation = dict(pending.get("continuation") or {})
        # As in the success path, release the completed candidate before a
        # batch continuation stages its next exact candidate.
        node.pending_helper_acceptance = {}
        lemma_suffix_resumed = False
        resumed_helper_names: List[str] = []
        continuation_kind = str(continuation.get("kind") or "")
        if continuation_kind == "lemma_dag":
            prior_node_ids = [
                str(item)
                for item in list(continuation.get("candidate_node_ids") or ())
                if str(item or "").strip()
            ]
            candidate_node_id = proof_state.record_lemma_dag_candidate(
                helper_name=(
                    helper_name
                    or str(continuation.get("helper_name") or "")
                ),
                statement=(
                    helper_decl_statement(helper_block)
                    or str(continuation.get("statement") or "")
                ),
                accepted=False,
                source=str(continuation.get("source") or ""),
                phase=str(
                    continuation.get("phase")
                    or "proof_state_lemma_dag_helper"
                ),
                turn_index=_durable_nonnegative_int(
                    continuation.get("turn_index")
                ),
                parent_node_id=str(
                    continuation.get("task_id") or node.node_id
                ),
                rejection=(
                    str(acceptance_status.get("error_kind") or "")
                    or "lean_rejected_helper_proof"
                ),
            )
            if candidate_node_id:
                prior_node_ids.append(candidate_node_id)
            proposed_count = (
                _durable_nonnegative_int(
                    continuation.get("proposed_count")
                )
                + int(bool(candidate_node_id))
            )
            accepted_count = _durable_nonnegative_int(
                continuation.get("accepted_count")
            )
            remaining_helper_blocks = [
                str(item or "").strip()
                for item in list(
                    continuation.get("remaining_helper_blocks") or ()
                )
                if str(item or "").strip()
            ]
            if remaining_helper_blocks:
                lemma_suffix_resumed = True
                suffix_status = {}
                suffix_records = []
                suffix_helpers = await _try_proof_state_lemma_dag_helpers(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    helpers=remaining_helper_blocks,
                    recorder=None,
                    trace_prefix=trace_prefix,
                    turn=turn,
                    timeout_s=_remaining_timeout(timeout_s),
                    deadline_monotonic=action_deadline_monotonic,
                    proof_cache=proof_cache,
                    target_task_id=str(
                        continuation.get("task_id") or node.node_id
                    ),
                    max_parent_stub_goals=max_residual_goals,
                    initial_proposed_count=proposed_count,
                    initial_accepted_count=accepted_count,
                    initial_candidate_node_ids=prior_node_ids,
                    initial_renamed_collisions=dict(
                        continuation.get("renamed_collisions") or {}
                    ),
                    status_out=suffix_status,
                    records_out=suffix_records,
                )
                records.extend(suffix_records)
                resumed_helper_names.extend(
                    item
                    for item in suffix_helpers
                    if item and item not in resumed_helper_names
                )
            else:
                proof_state.close_decomposition_task_from_lemma_dag(
                    task_id=str(
                        continuation.get("task_id") or node.node_id
                    ),
                    proposed_count=proposed_count,
                    accepted_count=accepted_count,
                    node_ids=prior_node_ids,
                )
        elif continuation_kind == "lemma_dag_parent_stub_closed":
            # Residual extraction proved that this parent-shaped helper can
            # close the goal, but normal answer-safe helper acceptance is the
            # final authority. A semantic veto rejects only this candidate;
            # it must not erase the rest of the already-paid ordered batch.
            prior_node_ids = [
                str(item)
                for item in list(
                    continuation.get("candidate_node_ids") or ()
                )
                if str(item or "").strip()
            ]
            proposed_count = _durable_nonnegative_int(
                continuation.get("proposed_count")
            )
            accepted_count = _durable_nonnegative_int(
                continuation.get("accepted_count")
            )
            remaining_helper_blocks = [
                str(item or "").strip()
                for item in list(
                    continuation.get("remaining_helper_blocks") or ()
                )
                if str(item or "").strip()
            ]
            if remaining_helper_blocks:
                lemma_suffix_resumed = True
                suffix_status = {}
                suffix_records = []
                suffix_helpers = await _try_proof_state_lemma_dag_helpers(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    helpers=remaining_helper_blocks,
                    recorder=None,
                    trace_prefix=trace_prefix,
                    turn=turn,
                    timeout_s=_remaining_timeout(timeout_s),
                    deadline_monotonic=action_deadline_monotonic,
                    proof_cache=proof_cache,
                    target_task_id=str(
                        continuation.get("task_id") or node.node_id
                    ),
                    max_parent_stub_goals=max_residual_goals,
                    initial_proposed_count=proposed_count,
                    initial_accepted_count=accepted_count,
                    initial_candidate_node_ids=prior_node_ids,
                    initial_renamed_collisions=dict(
                        continuation.get("renamed_collisions") or {}
                    ),
                    status_out=suffix_status,
                    records_out=suffix_records,
                )
                records.extend(suffix_records)
                resumed_helper_names.extend(
                    item
                    for item in suffix_helpers
                    if item and item not in resumed_helper_names
                )
            else:
                proof_state.close_decomposition_task_from_lemma_dag(
                    task_id=str(
                        continuation.get("task_id") or node.node_id
                    ),
                    proposed_count=proposed_count,
                    accepted_count=accepted_count,
                    node_ids=prior_node_ids,
                )
        elif continuation_kind == "cache_seed_batch":
            remaining_cache_records = [
                dict(item)
                for item in list(
                    continuation.get("remaining_cache_records") or ()
                )
                if isinstance(item, Mapping)
            ]
            if remaining_cache_records:
                lemma_suffix_resumed = True
                cache_summary = await seed_verified_helpers_from_same_problem_cache(
                    lean=lean,
                    conv=conv,
                    dossier=dossier,
                    proof_state=proof_state,
                    proof_cache=None,
                    theorem_name=str(
                        continuation.get("theorem_name")
                        or getattr(dossier, "theorem_name", "")
                    ),
                    timeout_s=_remaining_timeout(
                        float(continuation.get("timeout_s") or timeout_s)
                    ),
                    max_helpers=len(remaining_cache_records),
                    _candidate_records=remaining_cache_records,
                    _batch_receipt_key=str(
                        continuation.get("batch_receipt_key") or ""
                    ),
                )
                resumed_helper_names.extend(
                    item
                    for item in list(
                        cache_summary.get("accepted_helper_names") or ()
                    )
                    if item and item not in resumed_helper_names
                )
        elif continuation_kind == "recursive_helper":
            proof_state.record_lemma_dag_candidate(
                helper_name=(
                    helper_name
                    or str(continuation.get("helper_name") or "")
                ),
                statement=(
                    helper_decl_statement(helper_block)
                    or str(continuation.get("statement") or node.target)
                ),
                accepted=False,
                source=str(
                    continuation.get("source")
                    or f"recursive_helper_prover:{node.node_id}"
                ),
                phase=str(
                    continuation.get("phase") or "recursive_helper_prover"
                ),
                turn_index=_durable_nonnegative_int(
                    continuation.get("turn_index")
                ),
                target_node_id=str(
                    continuation.get("target_node_id") or node.node_id
                ),
                rejection=(
                    str(acceptance_status.get("error_kind") or "")
                    or "lean_rejected_helper_proof"
                ),
            )
        elif continuation_kind == "tactic_swarm":
            _settle_deferred_tactic_candidate(
                continuation,
                accepted=False,
            )
            lemma_suffix_resumed = True
        elif continuation_kind == "formal_state_search":
            _settle_deferred_formal_candidate(
                continuation,
                accepted=False,
            )
            lemma_suffix_resumed = True
        return lemma_suffix_resumed, resumed_helper_names
    _trace(
        trace_prefix,
        f"  proof-state child closure: {node.node_id} "
        f"({len(node.target)} chars)",
    )
    if _remaining_timeout(timeout_s) <= 0.0:
        deadline_deferred = bool(
            float(timeout_s or 0.0) > 0.0
            and float(action_deadline_monotonic or 0.0) > 0.0
        )
        if not deadline_deferred:
            proof_state.record_budget_skip(
                node_id=node.node_id,
                reason="tactic_budget_disabled",
            )
        records.append(
            {
                "phase": "proof_state_child_tactic",
                "turn_in_phase": turn,
                "node_id": node.node_id,
                "target": node.target,
                "helper_name": "",
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_success_attempt": None,
                "spawned_child_nodes": [],
                "tactic_elapsed_s": 0.0,
                "tactic_exit_reason": (
                    "enclosing_deadline_deferred"
                    if deadline_deferred
                    else "tactic_budget_disabled"
                ),
                "deferred_before_launch": deadline_deferred,
                "verdict": (
                    "child_operation_deferred"
                    if deadline_deferred
                    else "tactic_skipped"
                ),
            }
        )
        return accepted_helpers, records

    pending_handled, pending_helpers = await _retry_pending_acceptance()
    if pending_handled:
        return pending_helpers, records

    if not allowed or "cache_hit" in allowed:
        cached_helper, cache_records = await _try_proof_state_cache_hit(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            node=node,
            proof_cache=proof_cache,
            turn=turn,
            timeout_s=_remaining_timeout(timeout_s),
            deadline_monotonic=action_deadline_monotonic,
        )
        records.extend(cache_records)
        if cached_helper:
            return [cached_helper], records

    if allow_parent_assembly:
        assembled_helper, assembly_attempts = await _try_proof_state_parent_assembly(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            node=node,
            turn=turn,
            timeout_s=_remaining_timeout(timeout_s),
            proof_cache=proof_cache,
            deadline_monotonic=action_deadline_monotonic,
        )
        if assembly_attempts:
            records.append(
                {
                    "phase": "proof_state_parent_assembly",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": assembled_helper,
                    "assembly_attempts": assembly_attempts,
                    "verdict": (
                        "helper_accepted"
                        if assembled_helper
                        else "assembly_rejected"
                    ),
                }
            )
        if assembled_helper:
            return [assembled_helper], records

    falsification_retryable = False
    if allow_decl_probe or allow_tactic_swarm:
        # The gate remains certificate-authoritative and advisory on every
        # non-refuting outcome, but it must precede every expensive proving
        # quantum. A context refresh can reopen declarations against a child
        # that has since become certifiably false; retire that route before
        # purchasing another full declaration timeout. Context-key memory in
        # the preflight keeps this bounded to one run per exact Lean context.
        falsification_preamble = _proof_state_residual_preamble(conv)
        falsification_helpers = _proof_state_residual_lemmas(
            conv,
            _proof_state_verified_helper_blocks(dossier),
        )
        child_falsified, falsification_record = (
            await _try_proof_state_child_falsification_preflight(
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                node=node,
                preamble=falsification_preamble,
                helpers=falsification_helpers,
                turn=turn,
                timeout_s=_remaining_timeout(timeout_s),
                deadline_monotonic=action_deadline_monotonic,
            )
        )
        if falsification_record:
            records.append(falsification_record)
        if child_falsified:
            return accepted_helpers, records
        falsification_retryable = bool(
            falsification_record.get("retryable_infrastructure")
        )

    if allow_decl_probe:
        # Every decl probe is one deterministic Lean operation, including
        # untargeted legacy/salvage cascades. Leaving the remaining ranked
        # declarations pending preserves the complete configured portfolio
        # without multiplying one action by the retrieval page size.
        decl_probe_limit = min(1, max(0, int(max_decl_applications or 0)))
        decl_helper_name, decl_attempts = await _try_proof_state_decl_closure(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            node=node,
            turn=turn,
            timeout_s=_remaining_timeout(timeout_s),
            max_decls=decl_probe_limit,
            max_residual_goals=max_residual_goals,
            proof_cache=proof_cache,
            deadline_monotonic=action_deadline_monotonic,
        )
        if decl_attempts:
            records.append(
                {
                    "phase": "proof_state_decl_application",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "helper_name": decl_helper_name,
                    "decl_attempts": decl_attempts[:10],
                    "verdict": (
                        "helper_accepted" if decl_helper_name else "decl_rejected"
                    ),
                }
            )
        if decl_helper_name:
            return [decl_helper_name], records

    if not allow_tactic_swarm:
        return accepted_helpers, records
    if falsification_retryable:
        # Preserve this exact tactic item for one retry.  The recorded transient
        # context causes the next invocation to bypass the failed advisory gate
        # and proceed to Lean-validated tactic search.
        return accepted_helpers, records

    if int(max_candidates or 0) <= 0 or _remaining_timeout(timeout_s) <= 0.0:
        deadline_deferred = bool(
            int(max_candidates or 0) > 0
            and float(timeout_s or 0.0) > 0.0
            and float(action_deadline_monotonic or 0.0) > 0.0
        )
        if not deadline_deferred:
            proof_state.record_budget_skip(
                node_id=node.node_id,
                reason="tactic_budget_disabled",
            )
        records.append(
            {
                "phase": "proof_state_child_tactic",
                "turn_in_phase": turn,
                "node_id": node.node_id,
                "target": node.target,
                "helper_name": "",
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_success_attempt": None,
                "spawned_child_nodes": [],
                "tactic_elapsed_s": 0.0,
                "tactic_exit_reason": (
                    "enclosing_deadline_deferred"
                    if deadline_deferred
                    else "tactic_budget_disabled"
                ),
                "deferred_before_launch": deadline_deferred,
                "verdict": (
                    "child_operation_deferred"
                    if deadline_deferred
                    else "tactic_skipped"
                ),
            }
        )
        return accepted_helpers, records

    tactic_preamble = _proof_state_residual_preamble(conv)
    tactic_helpers = _proof_state_residual_lemmas(
        conv,
        _proof_state_verified_helper_blocks(dossier),
    )
    answer_safety_opaque_mode = bool(
        getattr(conv, "opaque_mode", getattr(dossier, "opaque_mode", True))
    )
    answer_safety_allow_official_answer_visibility = bool(
        getattr(
            conv,
            "allow_official_answer_visibility",
            getattr(dossier, "allow_official_answer_visibility", False),
        )
    )
    answer_safety_official_answer_payload_present = getattr(
        conv,
        "official_answer_payload_present",
        getattr(dossier, "official_answer_payload_present", None),
    )
    answer_safety_suppress_solution_placeholders = bool(
        getattr(
            conv,
            "suppress_solution_placeholders",
            getattr(dossier, "suppress_solution_placeholders", True),
        )
    )
    tactic_pattern_cache = _proof_state_tactic_pattern_cache(proof_state)
    tactic_pattern_context = _proof_state_tactic_pattern_context(
        proof_state,
        node,
        scope="proof_state_child_tactic",
        mode="child_residual",
    )
    tactic_pattern_context.update(
        {
            "tactic_timeout_s": str(round(max(0.0, float(timeout_s or 0.0)), 3)),
            "max_candidates": str(max(0, int(max_candidates or 0))),
        }
    )
    tactic_available_timeout = _remaining_timeout(timeout_s)
    tactic_terminal_context_key = _proof_state_child_tactic_terminal_context_key(
        conv=conv,
        dossier=dossier,
        proof_state=proof_state,
        node=node,
        timeout_s=tactic_available_timeout,
        max_candidates=max_candidates,
    )
    if tactic_terminal_context_key in set(
        getattr(node, "tactic_terminal_context_keys", []) or []
    ):
        records.append(
            {
                "phase": "proof_state_child_tactic",
                "turn_in_phase": turn,
                "node_id": node.node_id,
                "target": node.target,
                "tactic_candidate_count": 0,
                "tactic_attempts": [],
                "tactic_elapsed_s": 0.0,
                "tactic_exit_reason": "unchanged_terminal_context",
                "verdict": "tactic_skipped",
            }
        )
        return accepted_helpers, records
    tactic_started = time.monotonic()
    suppressed_proofs: Set[str] = set()
    aggregate_attempts: List[Dict[str, Any]] = []
    aggregate_candidate_count = 0
    aggregate_cache_metadata: Dict[str, Any] = {}
    result: Any = None
    success_attempt: Optional[Dict[str, Any]] = None
    final_exit_reason = "exhausted"
    helper_name = ""
    had_acceptance_veto = False
    candidate_portfolio: Optional[Tuple[Any, ...]] = None
    candidate_portfolio_offset = 0
    reusable_candidate_portfolio = False

    # Resume the unattempted suffix of one generated/ranked portfolio after
    # an acceptance veto. This preserves the configured candidate budget
    # without regenerating a full swarm for every Lean-successful proof.
    for _veto_loop in range(max(1, int(max_candidates or 1))):
        operation_timeout = _remaining_timeout(timeout_s)
        if operation_timeout <= 0.0:
            final_exit_reason = "timeout"
            break
        operation_pattern_cache = copy.deepcopy(tactic_pattern_cache)

        async def run_child_tactic() -> Any:
            return await try_close_with_tactics(
                lean,
                node.target,
                tactic_preamble,
                tactic_helpers,
                timeout_s=operation_timeout,
                max_candidates=max(1, int(max_candidates or 1)),
                pattern_cache=operation_pattern_cache,
                pattern_context=tactic_pattern_context,
                defer_success_cache=True,
                candidate_portfolio=candidate_portfolio,
                candidate_portfolio_offset=candidate_portfolio_offset,
                # The offset already excludes the vetoed prefix on resumed
                # portfolios. Avoid sorting and copying the growing veto set.
                suppressed_proofs=(
                    ()
                    if candidate_portfolio is not None
                    else tuple(sorted(suppressed_proofs))
                ),
                suppress_solution_placeholders=(
                    answer_safety_suppress_solution_placeholders
                ),
                opaque_mode=answer_safety_opaque_mode,
                allow_official_answer_visibility=(
                    answer_safety_allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    answer_safety_official_answer_payload_present
                ),
                # Publish observer events only after the strict operation
                # completes, never from a cancellation-resistant tail.
                attempt_observer=None,
            )

        try:
            result = await _await_serialized_lean_operation(
                lean,
                run_child_tactic,
                timeout_s=operation_timeout,
                deadline_monotonic=action_deadline_monotonic,
                operation_label="proof_state_child_tactic",
            )
        except _LeanOperationDeadline:
            final_exit_reason = "timeout"
            break
        tactic_pattern_cache = operation_pattern_cache
        setattr(proof_state, "_tactic_pattern_cache", tactic_pattern_cache)
        _record_completed_tactic_observer_events(
            dossier,
            "proof_state_child_tactic",
            result,
        )
        result_attempts = [
            dict(attempt)
            for attempt in list(getattr(result, "attempts", []) or [])
            if isinstance(attempt, dict)
        ]
        aggregate_attempts.extend(result_attempts)
        if hasattr(result, "candidate_portfolio"):
            reusable_candidate_portfolio = True
            candidate_portfolio = tuple(
                getattr(result, "candidate_portfolio", ()) or ()
            )
            candidate_portfolio_offset = max(
                0,
                int(getattr(result, "next_candidate_index", 0) or 0),
            )
        try:
            result_candidate_count = int(
                getattr(result, "candidate_count", 0) or 0
            )
            if reusable_candidate_portfolio:
                aggregate_candidate_count = max(
                    aggregate_candidate_count,
                    result_candidate_count,
                )
            else:
                aggregate_candidate_count += result_candidate_count
        except Exception:
            pass
        aggregate_cache_metadata = _merge_tactic_cache_metadata(
            aggregate_cache_metadata,
            getattr(result, "cache_metadata", {}),
        )
        final_exit_reason = str(getattr(result, "exit_reason", "") or "exhausted")
        if not (getattr(result, "ok", False) and getattr(result, "proof", None)):
            break
        local_success_attempt = next(
            (
                attempt
                for attempt in result_attempts
                if attempt.get("ok")
                and str(attempt.get("proof") or "") == str(result.proof or "")
            ),
            None,
        )
        helper_name = proof_state.helper_name_for_node(node, dossier)
        helper_block = _proof_state_helper_block(
            helper_name,
            node.target,
            str(result.proof or ""),
        )
        if not _stage_pending_acceptance(
            helper_block,
            source="tactic_swarm",
            context_hash=tactic_terminal_context_key,
            continuation={
                "kind": "tactic_swarm",
                "attempt_count": len(aggregate_attempts),
                "terminal_context_key": tactic_terminal_context_key,
                "success_attempt": dict(local_success_attempt or {}),
                "cache_metadata": dict(aggregate_cache_metadata),
            },
        ):
            final_exit_reason = "pending_helper_acceptance_owned"
            break
        acceptance_status: Dict[str, Any] = {}
        accepted = await _accept_proof_state_helper(
            lean=lean,
            conv=conv,
            dossier=dossier,
            helper_block=helper_block,
            phase="proof_state_child_tactic",
            turn_index=turn,
            timeout_s=operation_timeout,
            proof_cache=proof_cache,
            proof_state=proof_state,
            target_statement=node.target,
            deadline_monotonic=action_deadline_monotonic,
            status_out=acceptance_status,
        )
        if accepted:
            node.pending_helper_acceptance = {}
            record_dossier_lean_attempt_event(
                dossier,
                lane="proof_state_child_tactic",
                event="certificate_accepted",
                attempt={"helper_name": helper_name, "node_id": node.node_id},
            )
            accepted_helpers.append(helper_name)
            success_attempt = local_success_attempt
            if isinstance(local_success_attempt, dict):
                local_success_attempt["accepted_by_proof_state"] = True
                if aggregate_attempts:
                    aggregate_attempts[-1]["accepted_by_proof_state"] = True
                candidate = TacticPatternCache.candidate_from_attempt(
                    local_success_attempt
                )
                if candidate is not None:
                    aggregate_cache_metadata = _merge_tactic_cache_metadata(
                        aggregate_cache_metadata,
                        tactic_pattern_cache.confirm_success(
                            goal_statement=node.target,
                            preamble=tactic_preamble,
                            helpers=tactic_helpers,
                            candidate=candidate,
                            pattern_context=tactic_pattern_context,
                            suppress_solution_placeholders=(
                                answer_safety_suppress_solution_placeholders
                            ),
                            opaque_mode=answer_safety_opaque_mode,
                            allow_official_answer_visibility=(
                                answer_safety_allow_official_answer_visibility
                            ),
                        ),
                    )
            final_exit_reason = "solved"
            break
        if _acceptance_retryable(acceptance_status):
            final_exit_reason = "acceptance_retryable_error"
            helper_name = ""
            break
        node.pending_helper_acceptance = {}
        had_acceptance_veto = True
        vetoed_proof = str(getattr(result, "proof", "") or "").strip()
        if vetoed_proof:
            suppressed_proofs.add(vetoed_proof)
        if isinstance(local_success_attempt, dict):
            local_success_attempt["acceptance_vetoed"] = True
            if aggregate_attempts:
                aggregate_attempts[-1]["acceptance_vetoed"] = True
            candidate = TacticPatternCache.candidate_from_attempt(local_success_attempt)
            if candidate is not None:
                aggregate_cache_metadata = _merge_tactic_cache_metadata(
                    aggregate_cache_metadata,
                    tactic_pattern_cache.record_acceptance_veto(
                        goal_statement=node.target,
                        preamble=tactic_preamble,
                        helpers=tactic_helpers,
                        candidate=candidate,
                        pattern_context=tactic_pattern_context,
                        suppress_solution_placeholders=(
                            answer_safety_suppress_solution_placeholders
                        ),
                        opaque_mode=answer_safety_opaque_mode,
                        allow_official_answer_visibility=(
                            answer_safety_allow_official_answer_visibility
                        ),
                    ),
                )
                suppressed_proofs.add(candidate.proof)
        else:
            # Compatibility/swappable backends may report only ``ok`` and
            # ``proof``.  Classification cannot depend on optional attempt
            # telemetry; retain an aggregate veto receipt even without a
            # cache candidate record.
            aggregate_cache_metadata = _merge_tactic_cache_metadata(
                aggregate_cache_metadata,
                {"acceptance_vetoes": 1},
            )
        helper_name = ""
        if (
            reusable_candidate_portfolio
            and candidate_portfolio_offset >= len(candidate_portfolio or ())
        ):
            break
    if (
        not helper_name
        and had_acceptance_veto
        and final_exit_reason in {"exhausted", "solved"}
    ):
        # A later exhausted portfolio must not erase the fact that Lean found
        # a closing tactic and only the downstream helper-acceptance boundary
        # vetoed it.  The acceptance environment may recover or change on the
        # next turn, so this context remains retryable.
        final_exit_reason = "acceptance_vetoed"
    if result is None:
        result = SimpleNamespace(
            ok=False,
            proof=None,
            attempts=[],
            candidate_count=0,
            elapsed_s=0.0,
            exit_reason=final_exit_reason,
            cache_metadata={},
        )
    object.__setattr__(result, "attempts", aggregate_attempts)
    object.__setattr__(result, "candidate_count", aggregate_candidate_count)
    object.__setattr__(result, "elapsed_s", round(time.monotonic() - tactic_started, 3))
    object.__setattr__(result, "exit_reason", final_exit_reason)
    object.__setattr__(result, "cache_metadata", aggregate_cache_metadata)
    formal_search_run: Optional[Any] = None
    formal_search_attempt_count = 0
    normalized_formal_config: Optional[Any] = None
    if formal_search_config is not None:
        try:
            normalized_formal_config = formal_search_config.normalized()
            formal_remaining = _remaining_timeout(
                float(getattr(normalized_formal_config, "total_timeout_s", 0.0) or 0.0)
            )
            normalized_formal_config = replace(
                normalized_formal_config,
                total_timeout_s=formal_remaining,
                operation_timeout_s=float(
                    getattr(
                        normalized_formal_config,
                        "operation_timeout_s",
                        formal_remaining,
                    )
                    or formal_remaining
                ),
                enabled=bool(
                    getattr(normalized_formal_config, "enabled", False)
                    and formal_remaining > 0.0
                ),
            )
        except Exception:
            normalized_formal_config = None
    if (
        not helper_name
        and normalized_formal_config is not None
        and bool(getattr(normalized_formal_config, "enabled", False))
        and formal_search_client is not None
    ):
        from .lean_parser import LeanGoalState
        from .mini_formal_state_search import (
            OnlineTacticValueModel,
            run_goal_conditioned_formal_search,
        )

        online_value_model = getattr(
            proof_state,
            "_formal_state_online_value_model",
            None,
        )
        if not isinstance(online_value_model, OnlineTacticValueModel):
            online_value_model = OnlineTacticValueModel()
            setattr(
                proof_state,
                "_formal_state_online_value_model",
                online_value_model,
            )
        try:
            formal_search_run = await run_goal_conditioned_formal_search(
                client=formal_search_client,
                lean=lean,
                statement=node.target,
                initial_goals=[
                    LeanGoalState(
                        index=0,
                        # node.target is already a closed statement produced by
                        # proof-state normalization. Repeating its former local
                        # binders here gives the model a state Lean never checks.
                        hypotheses=[],
                        target=node.target,
                    )
                ],
                preamble=tactic_preamble,
                helpers=tactic_helpers,
                config=normalized_formal_config,
                value_model=online_value_model,
                cost_controller=cost_controller,
                role=str(getattr(conv, "role", "prove") or "prove"),
                suppress_solution_placeholders=bool(
                    getattr(conv, "suppress_solution_placeholders", True)
                ),
                opaque_mode=answer_safety_opaque_mode,
                allow_official_answer_visibility=(
                    answer_safety_allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    answer_safety_official_answer_payload_present
                ),
            )
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            records.append(
                {
                    "phase": "proof_state_formal_search",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "verdict": "formal_search_infrastructure_error",
                    "exception_type": type(exc).__name__,
                    "exception_text": str(exc)[:500],
                }
            )
        if formal_search_run is not None:
            formal_result = formal_search_run.result
            formal_bottlenecks = _formal_state_root_bottlenecks(
                proof_state,
                node,
                list(formal_result.bottlenecks or ())[:5],
                tactic_helpers,
            )
            formal_search_attempt_count = max(
                0,
                int(getattr(formal_result, "nodes_created", 0) or 0) - 1,
            )
            proof_state.record_transition(
                node_id=node.node_id,
                source="goal_conditioned_formal_search",
                error_type=(
                    "formal_candidate_pending_acceptance"
                    if bool(getattr(formal_result, "solved", False))
                    else "formal_state_bottleneck"
                ),
                action=(
                    "validate_formal_state_candidate"
                    if bool(getattr(formal_result, "solved", False))
                    else "backtrack_or_attack_bottleneck"
                ),
                blocker=(
                    "authoritative helper acceptance pending"
                    if bool(getattr(formal_result, "solved", False))
                    else str(getattr(formal_result, "exit_reason", "") or "unsolved")
                ),
                phase="proof_state_formal_search",
                turn_index=turn,
                payload={
                    "context_hash": str(formal_search_run.context_hash or ""),
                    "nodes_created": int(formal_result.nodes_created),
                    "nodes_expanded": int(formal_result.nodes_expanded),
                    "backtracks": int(formal_result.backtracks),
                    "value_estimates": int(formal_result.value_estimates),
                    "diversity_pruned": int(formal_result.diversity_pruned),
                    "operation_timeouts": int(formal_result.operation_timeouts),
                    "infrastructure_failures": int(
                        formal_result.infrastructure_failures
                    ),
                    "completion_rejections": int(formal_result.completion_rejections),
                    "bottlenecks": formal_bottlenecks,
                },
            )
            formal_record = {
                    "phase": "proof_state_formal_search",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "context_hash": str(formal_search_run.context_hash or ""),
                    "solved": bool(formal_result.solved),
                    "proof": str(formal_result.proof or "")
                    if formal_result.solved
                    else "",
                    "exit_reason": str(formal_result.exit_reason or ""),
                    "nodes_created": int(formal_result.nodes_created),
                    "nodes_expanded": int(formal_result.nodes_expanded),
                    "max_depth_reached": int(formal_result.max_depth_reached),
                    "lean_checks": int(formal_result.lean_checks),
                    "backtracks": int(formal_result.backtracks),
                    "value_estimates": int(formal_result.value_estimates),
                    "diversity_pruned": int(formal_result.diversity_pruned),
                    "operation_timeouts": int(formal_result.operation_timeouts),
                    "infrastructure_failures": int(
                        formal_result.infrastructure_failures
                    ),
                    "completion_rejections": int(formal_result.completion_rejections),
                    "bottlenecks": formal_bottlenecks,
                    "events": [
                        dict(item)
                        for item in list(formal_search_run.events or ())[:20]
                    ],
                    "value_model": dict(formal_search_run.value_model_record or {}),
                    "verdict": (
                        "formal_search_candidate_found"
                        if formal_result.solved and formal_result.proof
                        else "formal_search_unsolved"
                    ),
                }
            records.append(formal_record)
            increment_metric = getattr(dossier, "increment_tool_metric", None)
            if callable(increment_metric):
                for metric_key, metric_value in (
                    ("mini_formal_state_search_invocations", 1),
                    ("mini_formal_state_search_nodes_created", formal_result.nodes_created),
                    ("mini_formal_state_search_nodes_expanded", formal_result.nodes_expanded),
                    ("mini_formal_state_search_lean_checks", formal_result.lean_checks),
                    ("mini_formal_state_search_backtracks", formal_result.backtracks),
                    ("mini_formal_state_search_value_estimates", formal_result.value_estimates),
                    ("mini_formal_state_search_diversity_pruned", formal_result.diversity_pruned),
                    ("mini_formal_state_search_operation_timeouts", formal_result.operation_timeouts),
                    (
                        "mini_formal_state_search_infrastructure_failures",
                        formal_result.infrastructure_failures,
                    ),
                    ("mini_formal_state_search_completion_rejections", formal_result.completion_rejections),
                    ("mini_formal_state_search_bottlenecks", len(formal_bottlenecks)),
                    (
                        "mini_formal_state_search_root_unlocking_bottlenecks",
                        sum(
                            1
                            for item in formal_bottlenecks
                            if item.get("root_unlocking_candidate")
                        ),
                    ),
                ):
                    increment_metric(metric_key, int(metric_value or 0))
            if formal_result.solved and formal_result.proof:
                candidate_helper_name = proof_state.helper_name_for_node(node, dossier)
                candidate_helper_block = _proof_state_helper_block(
                    candidate_helper_name,
                    node.target,
                    str(formal_result.proof or ""),
                )
                acceptance_timeout = _fully_funded_operation_timeout(
                    float(
                        getattr(
                            normalized_formal_config,
                            "operation_timeout_s",
                            timeout_s,
                        )
                        or timeout_s
                        or 0.0
                    ),
                    action_deadline_monotonic,
                )
                staged_formal_acceptance = _stage_pending_acceptance(
                    candidate_helper_block,
                    source="formal_state_search",
                    context_hash=str(formal_search_run.context_hash or ""),
                    continuation={
                        "kind": "formal_state_search",
                        "attempt_count": (
                            len(result.attempts) + formal_search_attempt_count
                        ),
                        "context_hash": str(
                            formal_search_run.context_hash or ""
                        ),
                        "exit_reason": str(formal_result.exit_reason or ""),
                    },
                )
                if not staged_formal_acceptance:
                    formal_record["accepted"] = False
                    formal_record["retryable_infrastructure"] = True
                    formal_record["verdict"] = "pending_helper_acceptance_owned"
                    final_exit_reason = "pending_helper_acceptance_owned"
                    object.__setattr__(result, "exit_reason", final_exit_reason)
                accepted = False
                acceptance_status: Dict[str, Any] = {}
                if staged_formal_acceptance and acceptance_timeout > 0.0:
                    accepted = await _accept_proof_state_helper(
                        lean=lean,
                        conv=conv,
                        dossier=dossier,
                        helper_block=candidate_helper_block,
                        phase="proof_state_formal_search",
                        turn_index=turn,
                        timeout_s=acceptance_timeout,
                        proof_cache=proof_cache,
                        proof_state=proof_state,
                        target_statement=node.target,
                        deadline_monotonic=action_deadline_monotonic,
                        status_out=acceptance_status,
                    )
                elif staged_formal_acceptance:
                    acceptance_status.update(
                        {
                            "status": "retryable_error",
                            "error_kind": "enclosing_deadline_deferred",
                        }
                    )
                if not staged_formal_acceptance:
                    pass
                elif accepted:
                    node.pending_helper_acceptance = {}
                    helper_name = candidate_helper_name
                    accepted_helpers.append(helper_name)
                    final_exit_reason = "solved_by_formal_state_search"
                    object.__setattr__(result, "exit_reason", final_exit_reason)
                    if callable(increment_metric):
                        increment_metric("mini_formal_state_search_solved", 1)
                    formal_record["accepted"] = True
                    formal_record["verdict"] = "formal_search_helper_accepted"
                    proof_state.record_transition(
                        node_id=node.node_id,
                        source="goal_conditioned_formal_search",
                        error_type="",
                        action="formal_state_helper_accepted",
                        blocker="",
                        phase="proof_state_formal_search",
                        turn_index=turn,
                        payload={"context_hash": str(formal_search_run.context_hash or "")},
                    )
                elif _acceptance_retryable(acceptance_status):
                    final_exit_reason = "acceptance_retryable_error"
                    object.__setattr__(result, "exit_reason", final_exit_reason)
                    formal_record["accepted"] = False
                    formal_record["verdict"] = (
                        "formal_search_acceptance_retryable_error"
                    )
                    proof_state.record_transition(
                        node_id=node.node_id,
                        source="goal_conditioned_formal_search",
                        error_type="formal_candidate_acceptance_retryable_error",
                        action="retry_formal_candidate_acceptance",
                        blocker=str(
                            acceptance_status.get("error_kind")
                            or "acceptance infrastructure failure"
                        ),
                        phase="proof_state_formal_search",
                        turn_index=turn,
                        payload={
                            "context_hash": str(formal_search_run.context_hash or "")
                        },
                    )
                else:
                    node.pending_helper_acceptance = {}
                    formal_record["accepted"] = False
                    formal_record["verdict"] = "formal_search_acceptance_vetoed"
                    proof_state.record_transition(
                        node_id=node.node_id,
                        source="goal_conditioned_formal_search",
                        error_type="formal_candidate_acceptance_vetoed",
                        action="backtrack_from_formal_candidate",
                        blocker="authoritative helper acceptance rejected candidate",
                        phase="proof_state_formal_search",
                        turn_index=turn,
                        payload={"context_hash": str(formal_search_run.context_hash or "")},
                    )
                    if callable(increment_metric):
                        increment_metric(
                            "mini_formal_state_search_acceptance_vetoes",
                            1,
                        )
    tactic_spawned: List[str] = []
    tactic_residual_deferred = False
    if not helper_name:
        for attempt in result.attempts[:8]:
            if not isinstance(attempt, dict):
                continue
            remaining_goals = list(attempt.get("remaining_goals") or [])
            partial_stub = str(
                attempt.get("partial_proof_stub")
                or attempt.get("proof_stub")
                or ""
            ).strip()
            if (
                not remaining_goals
                or not partial_stub
                or not bool(attempt.get("partial_stub_validated", False))
            ):
                continue
            residual_source = (
                f"tactic:{attempt.get('source') or attempt.get('tactic') or result.exit_reason}"
            )
            spawned, typed_goal_count, receipt_status = (
                await _extract_and_spawn_typed_residual_goals(
                    lean=lean,
                    proof_state=proof_state,
                    parent_node=node,
                    parent_proof_stub=partial_stub,
                    source=residual_source,
                    preamble=_proof_state_residual_preamble(conv),
                    lemmas=_proof_state_residual_lemmas(
                        conv,
                        _proof_state_verified_helper_blocks(dossier),
                    ),
                    timeout_s=_remaining_timeout(timeout_s),
                    max_goals=max_residual_goals,
                    deadline_monotonic=action_deadline_monotonic,
                    origin_metadata={
                        "kind": "tactic_residual",
                        "turn_index": turn,
                        "tactic_source": str(
                            attempt.get("source") or attempt.get("tactic") or ""
                        ),
                        "attempt_count": len(result.attempts),
                        "terminal_context_key": tactic_terminal_context_key,
                        "cache_metadata": dict(
                            getattr(result, "cache_metadata", {}) or {}
                        ),
                    },
                )
            )
            node = proof_state.nodes.get(node.node_id, node)
            attempt["partial_stub_validation"] = receipt_status
            attempt["typed_residual_goal_count"] = typed_goal_count
            if receipt_status.endswith("_deferred"):
                tactic_residual_deferred = True
                final_exit_reason = receipt_status
                break
            if receipt_status != "residual_attestation_admitted" or not spawned:
                continue
            tactic_spawned.extend(spawned)
            if len(tactic_spawned) >= max(1, int(max_residual_goals or 1)):
                break
        if tactic_spawned:
            node.action = "assemble_from_children"
            node.blocker = f"tactic residual spawned {len(set(tactic_spawned))} subgoal(s)"
            node.priority = proof_state._priority(node)
    timeout_outcome = bool(
        not helper_name
        and not tactic_spawned
        and final_exit_reason == "timeout"
    )
    timeout_retry_exhausted = bool(
        timeout_outcome
        and tactic_terminal_context_key
        in set(getattr(node, "tactic_timeout_retry_context_keys", []) or [])
    )
    retryable_tactic_outcome = bool(
        not helper_name
        and not tactic_spawned
        and (
            final_exit_reason == "acceptance_retryable_error"
            or final_exit_reason == "pending_helper_acceptance_owned"
            or tactic_residual_deferred
            or (timeout_outcome and not timeout_retry_exhausted)
        )
    )
    if timeout_outcome and not timeout_retry_exhausted:
        _remember_child_tactic_timeout_retry(
            node,
            tactic_terminal_context_key,
        )
        node.blocker = final_exit_reason
        proof_state.record_transition(
            node_id=node.node_id,
            source="tactic",
            error_type="tactic_timeout_retryable",
            action=node.action,
            blocker=final_exit_reason,
            phase="proof_state_child_tactic",
            turn_index=turn,
            payload={
                "context_key": tactic_terminal_context_key,
                "retry_exhausted": False,
                "attempt_count": len(result.attempts),
            },
        )
    elif not retryable_tactic_outcome:
        proof_state.record_tactic_result(
            node_id=node.node_id,
            ok=bool(helper_name),
            attempt_count=(
                max(1, len(result.attempts))
                if timeout_retry_exhausted
                else len(result.attempts) + formal_search_attempt_count
            ),
            exit_reason=final_exit_reason,
            helper_name=helper_name,
            terminal_context_key=tactic_terminal_context_key,
            terminal_for_context=bool(
                not helper_name
                and (
                    timeout_retry_exhausted
                    or (
                        final_exit_reason == "exhausted"
                        and not had_acceptance_veto
                    )
                )
            ),
        )
    else:
        node.blocker = final_exit_reason
    proof_state.record_tactic_pattern_cache_metrics(
        getattr(result, "cache_metadata", {})
    )
    records.append(
        {
            "phase": "proof_state_child_tactic",
            "turn_in_phase": turn,
            "node_id": node.node_id,
            "target": node.target,
            "helper_name": helper_name,
            "tactic_candidate_count": result.candidate_count,
            **tactic_attempt_telemetry_fields(result.attempts),
            "tactic_attempts": result.attempts[:10],
            "tactic_success_attempt": success_attempt,
            "spawned_child_nodes": sorted(set(tactic_spawned)),
            "tactic_elapsed_s": result.elapsed_s,
            "tactic_exit_reason": final_exit_reason,
            "tactic_pattern_cache": dict(getattr(result, "cache_metadata", {}) or {}),
            "retryable_timeout": retryable_tactic_outcome,
            "residual_attestation_deferred": tactic_residual_deferred,
            "retry_exhausted": timeout_retry_exhausted,
            "verdict": (
                "helper_accepted"
                if helper_name
                else (
                    "tactic_residual_attestation_deferred"
                    if tactic_residual_deferred
                    else (
                        "tactic_retryable_timeout"
                        if retryable_tactic_outcome
                        else (
                            "tactic_timeout_exhausted"
                            if timeout_retry_exhausted
                            else "tactic_rejected"
                        )
                    )
                )
            ),
        }
    )
    return accepted_helpers, records


async def _try_proof_state_child_closures(
    *,
    conv: Any,
    lean: LeanRunner,
    dossier: Optional[ProofDossier],
    proof_state: Optional[ProofSearchState],
    recorder: Optional[Any],
    trace_prefix: str,
    turn: int,
    timeout_s: float,
    max_candidates: int,
    max_nodes: int,
    max_decl_applications: int = 6,
    max_residual_goals: int = 4,
    batch_parallelism: int = 1,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    target_node_ids: Optional[Sequence[str]] = None,
    target_work_types: Optional[Sequence[str]] = None,
    formal_search_config: Optional[Any] = None,
    formal_search_client: Optional[Any] = None,
    cost_controller: Optional[Any] = None,
    action_deadline_monotonic: float = 0.0,
    candidate_attempt_limit: int = 0,
    status_out: Optional[Dict[str, Any]] = None,
) -> Tuple[bool, Optional[str], List[str]]:
    """Try deterministic closures for scheduled child goals, then assemble root."""

    if dossier is None or proof_state is None:
        return False, None, []

    # ``timeout_s`` is a full per-operation capability. Only a separately
    # supplied enclosing hard deadline may bound the action. Formal search's
    # own total_timeout_s remains local to that subsystem.
    action_deadline_monotonic = max(
        0.0,
        float(action_deadline_monotonic or 0.0),
    )

    def _remaining_timeout(default_s: float) -> float:
        return _fully_funded_operation_timeout(
            default_s,
            action_deadline_monotonic,
        )

    def _update_status(records: Sequence[Mapping[str, Any]]) -> None:
        if status_out is None:
            return
        deferred = any(
            bool(record.get("deadline_deferred"))
            or bool(record.get("deferred_before_launch"))
            or any(
                bool(attempt.get("deferred_before_launch"))
                for attempt in list(record.get("decl_attempts") or ())
                if isinstance(attempt, Mapping)
            )
            for record in records
            if isinstance(record, Mapping)
        )
        retryable_timeout = any(
            bool(record.get("retryable_timeout"))
            or any(
                bool(attempt.get("retryable_failure"))
                and not bool(attempt.get("retry_exhausted"))
                and "timeout" in str(attempt.get("error_kind") or "").lower()
                for attempt in list(record.get("decl_attempts") or ())
                if isinstance(attempt, Mapping)
            )
            for record in records
            if isinstance(record, Mapping)
        )
        status_out["deadline_deferred"] = bool(
            status_out.get("deadline_deferred") or deferred
        )
        status_out["retryable_timeout"] = bool(
            status_out.get("retryable_timeout") or retryable_timeout
        )
        status_out["retryable_infrastructure"] = bool(
            status_out.get("retryable_infrastructure")
            or any(
                bool(record.get("retryable_infrastructure"))
                or any(
                    bool(attempt.get("retryable_failure"))
                    and not bool(attempt.get("retry_exhausted"))
                    for attempt in list(record.get("decl_attempts") or ())
                    if isinstance(attempt, Mapping)
                )
                for record in records
                if isinstance(record, Mapping)
            )
        )

    accepted_helpers: List[str] = []

    def _extend_accepted_helpers(helper_names: Sequence[str]) -> None:
        """Merge accepted helper names without duplicating semantic progress."""

        for raw_name in helper_names:
            helper_name = str(raw_name or "").strip()
            if helper_name and helper_name not in accepted_helpers:
                accepted_helpers.append(helper_name)

    checks_enabled = _remaining_timeout(timeout_s) > 0.0
    ensure_current_typed_residual_attestation_retries(
        conv=conv,
        dossier=dossier,
        lean=lean,
        proof_state=proof_state,
    )
    target_ids = {
        str(item or "").strip()
        for item in list(target_node_ids or ())
        if str(item or "").strip()
    }
    target_types = {
        str(item or "").strip()
        for item in list(target_work_types or ())
        if str(item or "").strip()
    }
    targeted_child_work = bool(target_ids)
    drain_pending_residuals = bool(
        not targeted_child_work or "residual_goal_extraction" in target_types
    )
    root_exact_timeout_s = float(timeout_s or 0.0)
    if checks_enabled and drain_pending_residuals:
        pending_records = await _retry_pending_typed_residual_extractions(
            conv=conv,
            dossier=dossier,
            lean=lean,
            proof_state=proof_state,
            deadline_monotonic=action_deadline_monotonic,
            max_nodes=max_nodes,
            turn=turn,
            target_node_ids=(
                tuple(target_ids)
                if targeted_child_work
                and "residual_goal_extraction" in target_types
                else None
            ),
            proof_cache=proof_cache,
            trace_prefix=trace_prefix,
        )
        _update_status(pending_records)
        for record in pending_records:
            for helper_name in list(record.get("accepted_helpers") or ()):
                helper_name = str(helper_name or "").strip()
                if helper_name and helper_name not in accepted_helpers:
                    accepted_helpers.append(helper_name)
            if (
                str(record.get("verdict") or "")
                == "residual_closed_helper_accepted"
            ):
                helper_name = str(record.get("helper_name") or "").strip()
                if helper_name and helper_name not in accepted_helpers:
                    accepted_helpers.append(helper_name)
                if str(record.get("node_id") or "") == str(
                    proof_state.root_node_id
                ):
                    # The closed receipt lane was admitted with a full
                    # verifier quantum. Preserve that floor for the immediate
                    # root-exact certification instead of falling back to the
                    # shorter ordinary child-tactic timeout.
                    root_exact_timeout_s = max(
                        root_exact_timeout_s,
                        _typed_residual_operation_timeout(lean, 0.0),
                    )
        if recorder is not None:
            for record in pending_records:
                recorder.record_turn(record)
        if any(
            str(record.get("verdict") or "").endswith("_deferred")
            for record in pending_records
        ):
            # Verifier-only replay owns this route until it settles. A
            # specifically selected tactic/decl alternative bypasses this
            # block above so scheduler backoff actually nudges the session to
            # different work instead of re-entering the same 300-second
            # receipt retry through ChildClosure's shared executor.
            return False, None, accepted_helpers
    graph = getattr(dossier, "proof_graph", None)
    refresher = getattr(proof_state, "refresh_graph_readiness", None)
    if callable(refresher) and graph is not None:
        try:
            refresh_records = refresher(
                graph,
                phase="proof_state_child_closure",
                turn_index=turn,
                target_node_ids=tuple(target_ids) if target_ids else None,
            )
            if recorder is not None:
                for record in refresh_records:
                    recorder.record_turn(
                        {
                            "phase": "proof_state_graph_refresh",
                            "turn_in_phase": turn,
                            **dict(record),
                        }
                    )
            if refresh_records:
                proof_state.sync_to_graph(
                    dossier,
                    phase="proof_state_child_closure",
                    turn_index=turn,
                    refresh_target_node_ids=tuple(target_ids) if target_ids else None,
                )
        except Exception as exc:
            if recorder is not None:
                recorder.record_turn(
                    {
                        "phase": "proof_state_graph_refresh",
                        "turn_in_phase": turn,
                        "error": f"{type(exc).__name__}: {exc}",
                        "verdict": "graph_refresh_failed",
                    }
                )
    async def _run_root_exact_checkpoint() -> Tuple[bool, Optional[str]]:
        state_ok, state_proof, root_helpers, root_records = (
            await _try_proof_state_root_exact_frontier(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                turn=turn,
                timeout_s=_remaining_timeout(root_exact_timeout_s),
                deadline_monotonic=action_deadline_monotonic,
            )
        )
        _extend_accepted_helpers(root_helpers)
        if recorder is not None:
            for record in root_records:
                recorder.record_turn(record)
        return state_ok, state_proof

    resume_root_tactic_directly = bool(
        checks_enabled
        and not targeted_child_work
        and _has_current_root_tactic_portfolio_continuation(
            conv=conv,
            dossier=dossier,
            proof_state=proof_state,
            timeout_s=timeout_s,
            max_candidates=max_candidates,
        )
    )

    # A targeted child dispatch owns this quantum. Root-exact certification is
    # still attempted after the selected child below, but a retryable root
    # verifier timeout must not consume every quantum before the selected
    # frontier identity ever launches.
    if checks_enabled and not targeted_child_work and not resume_root_tactic_directly:
        state_ok, state_proof = await _run_root_exact_checkpoint()
        if state_ok and state_proof:
            return True, state_proof, accepted_helpers

    if checks_enabled and not targeted_child_work and not resume_root_tactic_directly:
        state_ok, state_proof, assembly_helpers, assembly_records = (
            await _run_proof_state_assembly_fixpoint(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                turn=turn,
                timeout_s=_remaining_timeout(timeout_s),
                max_nodes=max_nodes,
                proof_cache=proof_cache,
                deadline_monotonic=action_deadline_monotonic,
            )
        )
    else:
        state_ok, state_proof, assembly_helpers, assembly_records = (
            False,
            None,
            [],
            [],
        )
    _extend_accepted_helpers(assembly_helpers)
    if recorder is not None:
        for record in assembly_records:
            recorder.record_turn(record)
    if state_ok and state_proof:
        return True, state_proof, accepted_helpers

    if checks_enabled and not targeted_child_work:
        state_ok, state_proof, root_tactic_helpers, root_tactic_records = (
            await _try_proof_state_root_tactic_assembly(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                turn=turn,
                timeout_s=_remaining_timeout(timeout_s),
                max_candidates=max_candidates,
                allow_deferred_retry=True,
                deadline_monotonic=action_deadline_monotonic,
                context_timeout_s=timeout_s,
                candidate_attempt_limit=candidate_attempt_limit,
            )
        )
        _extend_accepted_helpers(root_tactic_helpers)
        if recorder is not None:
            for record in root_tactic_records:
                recorder.record_turn(record)
        if state_ok and state_proof:
            return True, state_proof, accepted_helpers
        root_tactic_quantum_verdict = str(
            (root_tactic_records[-1] if root_tactic_records else {}).get(
                "verdict"
            )
            or ""
        )
        settled_capped_candidate = bool(
            int(candidate_attempt_limit or 0) > 0
            and any(
                str(attempt.get("source") or "") != "active_root_lift"
                for record in root_tactic_records
                if isinstance(record, Mapping)
                and str(record.get("tactic_exit_reason") or "") != "timeout"
                for attempt in list(record.get("tactic_attempts") or ())
                if isinstance(attempt, Mapping)
            )
        )
        if settled_capped_candidate or root_tactic_quantum_verdict in {
            "root_tactic_candidate_quantum_exhausted",
            "root_tactic_candidate_quantum_timeout_preserved",
            "root_tactic_candidate_quantum_state_rejected",
        }:
            if status_out is not None:
                status_out["root_tactic_candidate_quantum_exhausted"] = True
                if (
                    root_tactic_quantum_verdict
                    == "root_tactic_candidate_quantum_timeout_preserved"
                ):
                    status_out[
                        "root_tactic_candidate_quantum_timeout_preserved"
                    ] = True
                status_out["root_tactic_candidate_quantum_verdict"] = (
                    root_tactic_quantum_verdict
                )
            # This settled candidate is the complete deterministic quantum.
            # Returning here prevents the later helper/fallback root-tactic
            # checkpoint from consuming a second candidate in one action.
            return False, None, accepted_helpers

    # Reconcile persisted terminal tactic keys against the exact current
    # preamble/helper/budget context before the frontier suppresses this lane.
    for candidate_node in proof_state.nodes.values():
        terminal_keys = list(
            getattr(candidate_node, "tactic_terminal_context_keys", []) or []
        )
        retry_keys = list(
            getattr(candidate_node, "tactic_timeout_retry_context_keys", []) or []
        )
        if (
            candidate_node.kind != "child_goal"
            or not (terminal_keys or retry_keys)
        ):
            continue
        current_key = _proof_state_child_tactic_terminal_context_key(
            conv=conv,
            dossier=dossier,
            proof_state=proof_state,
            node=candidate_node,
            timeout_s=timeout_s,
            max_candidates=max_candidates,
        )
        if current_key in terminal_keys or current_key in retry_keys:
            continue
        candidate_node.tactic_terminal_context_keys = []
        candidate_node.tactic_timeout_retry_context_keys = []
        proof_state.record_transition(
            node_id=candidate_node.node_id,
            source="tactic",
            error_type="tactic_terminal_context_reset_exact_context_change",
            action=candidate_node.action,
            blocker="tactic preamble/helper/budget context changed",
            phase="proof_state_child_closure",
            turn_index=turn,
            payload={"current_context_key": current_key},
        )

    work_items = proof_state.work_frontier(
        max_items=max(8, int(max_nodes or 0) * 4),
        graph=getattr(dossier, "proof_graph", None),
    )
    decomposition_records: List[Dict[str, Any]] = []
    if not targeted_child_work:
        for item in work_items:
            if item.work_type != "lemma_dag_decomposition":
                continue
            task = proof_state.nodes.get(item.node_id)
            if task is None or task.kind != "decomposition_task" or task.status != "open":
                continue
            scheduled = proof_state.record_decomposition_task_prompted(
                task_id=task.node_id,
                phase="proof_state_lemma_dag_decomposition",
                turn_index=turn,
            )
            if not scheduled:
                continue
            _trace(
                trace_prefix,
                "  proof-state scheduled lemma-DAG decomposition task "
                f"{task.node_id}",
            )
            decomposition_records.append(
                {
                    "phase": "proof_state_lemma_dag_decomposition",
                    "turn_in_phase": turn,
                    "node_id": task.node_id,
                    "target": task.target,
                    "action": task.action,
                    "verdict": "decomposition_task_scheduled",
                }
            )
    if recorder is not None:
        for record in decomposition_records:
            recorder.record_turn(record)

    node_ids: List[str] = []
    selected_work_type_by_node: Dict[str, str] = {}
    for item in work_items:
        if item.work_type not in {
            "decl_probe",
            "tactic_swarm",
            "helper_acceptance",
        }:
            continue
        if target_types and item.work_type not in target_types:
            continue
        if target_ids and item.node_id not in target_ids:
            continue
        if item.node_id in node_ids:
            continue
        node = proof_state.nodes.get(item.node_id)
        if node is None or node.status != "open":
            continue
        if (
            item.work_type != "helper_acceptance"
            and node.kind != "child_goal"
        ):
            continue
        node_ids.append(item.node_id)
        selected_work_type_by_node[item.node_id] = item.work_type
        if len(node_ids) >= max(0, int(max_nodes or 0)):
            break
    nodes = [proof_state.nodes[node_id] for node_id in node_ids]
    if not nodes:
        if checks_enabled and accepted_helpers:
            state_ok, state_proof = await _run_root_exact_checkpoint()
            if state_ok and state_proof:
                return True, state_proof, accepted_helpers
        return False, None, accepted_helpers

    requested_parallelism = max(1, int(batch_parallelism or 1))
    # Child closure currently mutates the shared dossier/proof_state as it
    # probes. Keep the executor honest: until this grows immutable per-node
    # deltas with serial merge, the effective mutation model is serial.
    parallelism = 1
    _trace(
        trace_prefix,
        f"  proof-state batch executor: {len(nodes)} work item node(s), "
        f"parallelism={parallelism}"
        + (
            f" (requested {requested_parallelism}; serialized for shared state)"
            if requested_parallelism != parallelism
            else ""
        ),
    )

    decl_quantum_owner_id = next(
        (
            node_id
            for node_id in node_ids
            if selected_work_type_by_node.get(node_id) == "decl_probe"
        ),
        "",
    )

    async def _run_safe(
        node: ProofStateNode,
    ) -> Tuple[List[str], List[Dict[str, Any]]]:
        try:
            return await _try_proof_state_one_child_closure(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                node=node,
                trace_prefix=trace_prefix,
                turn=turn,
                timeout_s=timeout_s,
                max_candidates=max_candidates,
                # A batch is one scheduler dispatch. Fund at most one
                # declaration operation across the whole batch; other nodes
                # remain durably pending for later work identities.
                max_decl_applications=(
                    min(1, max(0, int(max_decl_applications or 0)))
                    if node.node_id == decl_quantum_owner_id
                    else 0
                ),
                max_residual_goals=max_residual_goals,
                proof_cache=proof_cache,
                allowed_work_types=target_types or None,
                formal_search_config=formal_search_config,
                formal_search_client=formal_search_client,
                cost_controller=cost_controller,
                action_deadline_monotonic=action_deadline_monotonic,
            )
        except Exception as exc:
            reason = f"{type(exc).__name__}: {exc}"
            exception_context_key = text_hash(
                json.dumps(
                    {
                        "node_id": node.node_id,
                        "target": canonicalize_lean_statement_for_identity(
                            str(node.target or "")
                        ),
                        "statement_environment_hash": str(
                            node.statement_environment_hash or ""
                        ),
                        "work_types": sorted(target_types),
                        "retrieval_signature": str(node.retrieval_signature or ""),
                        "decl_candidates": proof_state_decl_application_candidate_names(
                            node
                        ),
                        "application_context_hash": (
                            proof_state_decl_application_context_hash(conv, dossier)
                        ),
                        "exception_type": type(exc).__name__,
                    },
                    sort_keys=True,
                )
            )
            retry_keys = node.child_executor_exception_retry_context_keys
            retryable = exception_context_key not in set(retry_keys)
            if retryable:
                retry_keys.append(exception_context_key)
                del retry_keys[:-256]
            proof_state.record_transition(
                node_id=node.node_id,
                source="child_executor",
                error_type=(
                    "child_executor_exception_retryable"
                    if retryable
                    else "child_executor_exception_exhausted"
                ),
                action=node.action,
                blocker=reason,
                phase="proof_state_child_exception",
                turn_index=turn,
                payload={
                    "context_key": exception_context_key,
                    "retry_exhausted": not retryable,
                    "exception_type": type(exc).__name__,
                },
            )
            return [], [
                {
                    "phase": "proof_state_child_exception",
                    "turn_in_phase": turn,
                    "node_id": node.node_id,
                    "target": node.target,
                    "error": reason,
                    "verdict": (
                        "child_probe_exception_retryable"
                        if retryable
                        else "child_probe_exception_exhausted"
                    ),
                    "exception_context_key": exception_context_key,
                    "retryable_infrastructure": retryable,
                    "retryable_timeout": False,
                    "retry_exhausted": not retryable,
                }
            ]

    results: List[Tuple[List[str], List[Dict[str, Any]]]] = []
    for node in nodes:
        if (
            float(timeout_s or 0.0) > 0.0
            and action_deadline_monotonic > 0.0
            and _remaining_timeout(timeout_s) <= 0.0
        ):
            if status_out is not None:
                status_out["deadline_deferred"] = True
                status_out["deferred_node_id"] = node.node_id
            break
        results.append(await _run_safe(node))

    for helper_names, records in results:
        _update_status(records)
        _extend_accepted_helpers(helper_names)
        if recorder is not None:
            for record in records:
                recorder.record_turn(record)

    if checks_enabled and targeted_child_work:
        state_ok, state_proof = await _run_root_exact_checkpoint()
        if state_ok and state_proof:
            return True, state_proof, accepted_helpers

    if targeted_child_work and not accepted_helpers:
        return False, None, accepted_helpers

    # Proved children are only useful if the parent/root assembler gets a
    # chance to consume them. Run a deterministic fixpoint so child -> parent
    # -> root chains can close without waiting for the next LLM turn.
    affected_parent_ids: Tuple[str, ...] = ()
    if targeted_child_work:
        affected_parents: List[str] = []
        parent_group_getter = getattr(proof_state, "parent_groups_for_child", None)
        for node in nodes:
            if node.status != "proved":
                continue
            index_hit = False
            if callable(parent_group_getter):
                for parent_id, _assembly_id in parent_group_getter(node.node_id):
                    pid = str(parent_id or "").strip()
                    if pid:
                        affected_parents.append(pid)
                        index_hit = True
            if index_hit:
                continue
            legacy_parent = str(getattr(node, "parent_node_id", "") or "").strip()
            if legacy_parent:
                affected_parents.append(legacy_parent)
        affected_parent_ids = tuple(dict.fromkeys(affected_parents))
        if not affected_parent_ids:
            return False, None, accepted_helpers
    state_ok, state_proof, assembly_helpers, assembly_records = (
        await _run_proof_state_assembly_fixpoint(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            turn=turn,
            timeout_s=_remaining_timeout(timeout_s),
            max_nodes=max_nodes,
            proof_cache=proof_cache,
            target_node_ids=affected_parent_ids or None,
            required_child_node_ids=tuple(node_ids) if targeted_child_work else None,
            deadline_monotonic=action_deadline_monotonic,
        )
    )
    if recorder is not None:
        for record in assembly_records:
            recorder.record_turn(record)
    if assembly_helpers:
        _extend_accepted_helpers(assembly_helpers)
    if state_ok and state_proof:
        return True, state_proof, accepted_helpers
    if targeted_child_work:
        return False, None, accepted_helpers

    available_helpers: List[str] = []
    seen_helpers: Set[str] = set()
    for name in [*accepted_helpers, *_proved_proof_state_helper_names(proof_state)]:
        helper_name = str(name or "").strip()
        if helper_name and helper_name not in seen_helpers:
            seen_helpers.add(helper_name)
            available_helpers.append(helper_name)

    if not available_helpers:
        return False, None, []

    _trace(
        trace_prefix,
        "  proof-state accepted child helper(s): "
        + ", ".join(available_helpers),
    )
    state_ok, state_proof, root_tactic_helpers, root_tactic_records = (
        await _try_proof_state_root_tactic_assembly(
            conv=conv,
            lean=lean,
            dossier=dossier,
            proof_state=proof_state,
            turn=turn,
            timeout_s=_remaining_timeout(timeout_s),
            max_candidates=max_candidates,
            allow_deferred_retry=bool(accepted_helpers),
            deadline_monotonic=action_deadline_monotonic,
            context_timeout_s=timeout_s,
            candidate_attempt_limit=candidate_attempt_limit,
        )
    )
    _extend_accepted_helpers(root_tactic_helpers)
    if recorder is not None:
        for record in root_tactic_records:
            recorder.record_turn(record)
    if state_ok and state_proof:
        return True, state_proof, accepted_helpers
    return False, None, accepted_helpers
