"""Build and run the production ``MiniSession`` theorem prover.

The factory owns container-level parallel samples, boolean-branch sweeps,
session assembly, and the public ``prove_problem_via_session`` entry point.
"""

from __future__ import annotations

import asyncio
import copy
import hashlib
import json
import math
import threading
import time
import uuid
import weakref
from dataclasses import asdict, is_dataclass
from functools import partial, update_wrapper
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple

from ..config import LeanConfig, RetrievalConfig, RoleConfig  # noqa: F401  (parity with mini_prover imports)
from ..lean_runner import LeanRunner
from ..llm_error_policy import (
    is_terminal_llm_failure_reason,
    is_terminal_session_failure_reason,
    llm_failure_scope,
)
from ..llm_usage import reservation_pricing_targets
from ..mini_runtime_defaults import (
    DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
    DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
)
from ..mathlib_api_search import MathlibApiSearcher
from ..models import OpenAICompatClient
from ..runtime_context import mark_runtime_owned_callback
from ..pricing import lookup_known_token_pricing
from ..premise_retrieval import DEFAULT_TOP_K as PREMISE_DEFAULT_TOP_K
from ..proof_dossier import (
    ProofDossier,
    active_root_disproof_certificate_is_valid,
    active_root_target_statement,
    effective_solution_placeholder_suppression,
    text_hash,
)
from ..proof_state_cache import MiniVerifiedLemmaCache, _make_proof_state_cache
from ..putnam import problem_docstring_text
from ..theorem_project import TheoremProblem
from ..quarantined_turn_recorder import QuarantinedTurnRecorder
from ..deadline_guard import await_with_strict_deadline
from ..mini_recursive import PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS
from ..mini_theory.promotion_outbox import PromotionOutbox
from ..mini_branching import (
    _GuardedProofCache,
    _GuardedRecorder,
    _SampleAbandonGuard,
    _begin_parallel_falsification_conflict_receipt_scope,
    _consume_parallel_falsification_conflict_receipts,
    _copy_branch_failure_observability as _copy_branch_failure_observability,
    _copy_dossier_contents,
    _clear_parallel_sample_observability,
    _install_parallel_monotonic_metric_sink,
    _merge_dossier_helpers,
    _merge_dossier_observability,  # noqa: F401 - re-exported for tests/compat
    _merge_dossier_tool_metrics as _merge_dossier_tool_metrics,
    _merge_parallel_sample_structural_progress,
    _merge_verified_dossier_helpers as _merge_verified_dossier_helpers,  # noqa: F401 - re-exported for tests/compat
    _mark_parallel_proof_disproof_conflict,
    _parallel_authoritative_failure_records,
    _parallel_completed_root_disproof_certificate_hashes,
    _transfer_validated_falsification_state,
    _resolve_parallel_root_disproof_terminal_state,
    _parallel_observability_snapshot,
    _parallel_monotonic_metric_snapshot,
    _parallel_failure_sample_score,
    _parallel_proof_disproof_conflict_certificate_hashes,
    _parallel_sample_has_finalized_root_proof,
    _parallel_sample_has_proof_disproof_conflict,
    _parallel_sample_proof_state_record,
    _restore_parallel_observability_snapshot,
    _restore_parallel_monotonic_metric_snapshot,
    record_parallel_sample_failure,
    record_parallel_samples_zero_completed,
    _select_parallel_failure_primary,
    _snapshot_parallel_live_root_disproof,
    _snapshot_parallel_live_root_proof,
    _snapshot_parallel_live_proof_disproof_conflict,
    _stratify_sample_temperatures,
)
from ..mini_falsification import (
    DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
    DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
    FalsificationPolicy,
    require_falsification_search_bound,
    require_falsification_watchdog,
)
from .actions import (
    CastNormalizationAction,
    ChildClosureAction,
    ConversationTurnAction,
    DomainTheoryAction,
    FinsetReindexingAction,
    FalsifyCoverageAction,
    FalsifyTargetAction,
    FormalStateSearchAction,
    GraphRecursiveDecomposeAction,
    GraphRouteAssemblyAction,
    GraphNativeShortcutAction,
    HelperOnlySalvageAction,
    InterTurnAssemblyAction,
    LemmaDagDecomposeAction,
    PremiseRetrievalAction,
    ProofStateRetrievalAction,
    RecursiveControllerAction,
    RecursiveHelperProverAction,
    RootTacticCloseAction,
)
from .action import ActionBudget
from .actions.conversation_turn import _conversation_client_role_configs
from .session import MiniSession, _dispatch_capability_generation_nonce


_RECURSIVE_PAID_NO_ARTIFACT_KINDS = frozenset(
    {
        "final_no_tools_empty_output",
        "final_no_tools_token_exhausted",
        "final_no_tools_transcript_echo",
        "final_no_tools_reasoning_only",
        "final_no_tools_provider_ignored_tool_choice_none_budget_exhausted",
        "llm_turn_elapsed_budget_exhausted",
    }
)
_RECURSIVE_CONVERSATION_LEDGER_CREATE_LOCK = threading.Lock()


class _RecursiveConversationLaneLedger:
    """Atomic per-attempt authority for paid recursive model lanes."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._attempts: Dict[str, int] = {}
        self._reservations: Dict[str, Tuple[str, int]] = {}

    def try_reserve(
        self,
        lane_key: str,
        *,
        limit: int,
    ) -> Optional[Tuple[str, int]]:
        with self._lock:
            committed = max(0, int(self._attempts.pop(lane_key, 0) or 0))
            if committed:
                self._attempts[lane_key] = committed
            if any(
                reserved_key == lane_key
                for reserved_key, _allowance in self._reservations.values()
            ):
                return None
            allowance = max(1, int(limit or 1)) - committed
            if allowance <= 0:
                return None
            token = uuid.uuid4().hex
            self._reservations[token] = (lane_key, allowance)
            return token, allowance

    def unavailable(self, lane_key: str, *, limit: int) -> bool:
        with self._lock:
            committed = max(0, int(self._attempts.pop(lane_key, 0) or 0))
            if committed:
                self._attempts[lane_key] = committed
            in_flight = any(
                reserved_key == lane_key
                for reserved_key, _allowance in self._reservations.values()
            )
            return bool(committed >= max(1, int(limit or 1)) or in_flight)

    def settle(self, token: str, *, charge_count: int) -> None:
        with self._lock:
            lane_key, allowance = self._reservations.pop(
                str(token or ""),
                ("", 0),
            )
            if not lane_key or charge_count <= 0:
                return
            committed = max(
                0,
                int(self._attempts.pop(lane_key, 0) or 0),
            )
            self._attempts[lane_key] = committed + min(
                max(0, int(charge_count or 0)),
                allowance,
            )
            while len(self._attempts) > 4096:
                self._attempts.pop(next(iter(self._attempts)))


def _recursive_conversation_lane_ledger(owner: Any) -> Any:
    if owner is None:
        return None
    ledger = getattr(owner, "_recursive_conversation_lane_ledger", None)
    if ledger is None:
        with _RECURSIVE_CONVERSATION_LEDGER_CREATE_LOCK:
            ledger = getattr(owner, "_recursive_conversation_lane_ledger", None)
            if ledger is None:
                ledger = _RecursiveConversationLaneLedger()
                owner._recursive_conversation_lane_ledger = ledger
    return ledger


def _recursive_client_provider_policy(client: Any) -> Dict[str, Any]:
    """Stable request-capability identity for one provider client chain."""

    if client is None:
        return {}
    cfg = getattr(client, "cfg", None)
    provider_config_keys = (
        "name",
        "model",
        "base_url",
        "model_revision",
        "revision",
        "deployment_revision",
        "weights_hash",
        "model_hash",
        "reasoning_effort",
        "timeout_s",
        "request_timeout_s",
        "request_timeout_disabled",
        "operation_timeout_s",
        "max_tokens",
        "max_output_tokens",
        "conversation_max_tokens_override",
        "context_window",
        "llm_deadline_policy",
        "temperature",
        "top_p",
        "reasoning_control_required",
        "thinking_enabled",
        "prompt_style",
    )
    role_configs = _conversation_client_role_configs(client)
    if not role_configs and cfg is not None:
        role_configs = (cfg,)
    return {
        "role_configs": [
            {key: getattr(role_cfg, key, None) for key in provider_config_keys}
            for role_cfg in role_configs
        ],
        "adapter_type": f"{type(client).__module__}.{type(client).__qualname__}",
        "effective_base_url": str(
            getattr(client, "base_url", "") or getattr(cfg, "base_url", "") or ""
        ),
    }


def _recursive_conversation_lane_key(
    *,
    conv: Any,
    client: Any,
    lean: Any,
    dossier: Any,
    role: str,
    max_tool_calls_per_turn: int,
    max_turns: int,
    temperature_override: Any,
    recursive_max_elapsed_s: float,
    execution_policy: Mapping[str, Any],
    mini_phase_temperatures: Any = None,
) -> str:
    helpers = dict(getattr(dossier, "verified_helpers", {}) or {})
    helper_fingerprints = tuple(
        sorted(
            (
                str(name or ""),
                str(
                    getattr(helper, "source_hash", "")
                    or text_hash(str(getattr(helper, "source", "") or ""))
                ),
            )
            for name, helper in helpers.items()
        )
    )
    provider_policy = _recursive_client_provider_policy(client)
    live_lean = lean
    seen_generations: set[int] = set()
    while live_lean is not None and id(live_lean) not in seen_generations:
        seen_generations.add(id(live_lean))
        current_generation = getattr(live_lean, "current_generation", None)
        if not callable(current_generation):
            break
        try:
            replacement = current_generation()
        except BaseException:
            break
        if replacement is None or replacement is live_lean:
            break
        live_lean = replacement
    generation_nonce = _dispatch_capability_generation_nonce(live_lean)
    productive_history = []
    for raw_message in list(getattr(conv, "history", ()) or ()):
        if not isinstance(raw_message, Mapping):
            productive_history.append(raw_message)
            continue
        message = dict(raw_message)
        message_role = str(message.get("role") or "").strip().lower()
        content = str(message.get("content") or "")
        if (
            message_role == "assistant"
            and not message.get("tool_calls")
            and not content.strip()
        ):
            # A transport may append an empty assistant shell around a failed
            # response. It changes no provider-visible evidence and must not
            # mint a fresh paid lane. Nonempty proof attempts, tool calls, and
            # compacted diagnostics are exact repair context and are retained.
            continue
        productive_history.append(message)
    payload = {
        "version": 2,
        "role": str(role or "prove"),
        "target": str(getattr(conv, "goal_statement", "") or "").strip(),
        "problem_text_sha256": text_hash(str(getattr(conv, "problem_text", "") or "")),
        "lean_signature_sha256": text_hash(
            str(getattr(conv, "lean_signature", "") or "")
        ),
        "preamble_sha256": text_hash(str(getattr(conv, "preamble", "") or "")),
        "lean_preamble_sha256": text_hash(
            str(
                getattr(conv, "lean_preamble", None)
                or getattr(conv, "preamble", "")
                or ""
            )
        ),
        "helper_fingerprints": helper_fingerprints,
        "lean_generation": generation_nonce,
        "provider_policy": provider_policy,
        "conversation_policy": {
            "known_premise_names": list(getattr(conv, "known_premise_names", ()) or ()),
            "turn_budget": getattr(conv, "turn_budget", None),
            "rejected_code_fragments": list(
                getattr(conv, "rejected_code_fragments", ()) or ()
            ),
            "transient_goal_targets": list(
                getattr(conv, "transient_goal_targets", ()) or ()
            ),
            "repair_self_check_active": bool(
                getattr(conv, "repair_self_check_active", False)
            ),
            "opaque_mode": bool(getattr(conv, "opaque_mode", True)),
            "allow_official_answer_visibility": bool(
                getattr(conv, "allow_official_answer_visibility", False)
            ),
            "official_answer_payload_present": getattr(
                conv,
                "official_answer_payload_present",
                None,
            ),
            "suppress_solution_placeholders": bool(
                getattr(conv, "suppress_solution_placeholders", True)
            ),
            "allow_helper_decomposition": bool(
                getattr(conv, "allow_helper_decomposition", True)
            ),
            "declaration_required_submission": bool(
                getattr(conv, "declaration_required_submission", False)
            ),
            "productive_history_sha256": text_hash(
                json.dumps(
                    productive_history,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=True,
                    default=str,
                )
            ),
        },
        "max_tool_calls_per_turn": max(0, int(max_tool_calls_per_turn or 0)),
        "max_turns": max(1, int(max_turns or 1)),
        "temperature_override": temperature_override,
        "mini_phase_temperatures": mini_phase_temperatures,
        "recursive_max_elapsed_s": max(
            0.0,
            float(recursive_max_elapsed_s or 0.0),
        ),
        "execution_policy": dict(execution_policy or {}),
    }
    return hashlib.sha256(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            default=str,
        ).encode("utf-8")
    ).hexdigest()


def _recursive_proof_state_fingerprint(proof_state: Any) -> str:
    if proof_state is None:
        return ""
    serializer = getattr(proof_state, "to_execution_record", None)
    if callable(serializer):
        try:
            execution_record = serializer()
        except Exception:
            execution_record = None
        if execution_record is not None:
            return text_hash(
                json.dumps(
                    execution_record,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=True,
                    default=str,
                )
            )
    nodes = dict(getattr(proof_state, "nodes", {}) or {})
    return text_hash(
        json.dumps(
            {
                "root_node_id": str(getattr(proof_state, "root_node_id", "") or ""),
                "nodes": {
                    str(node_id): vars(node)
                    if hasattr(node, "__dict__")
                    else repr(node)
                    for node_id, node in nodes.items()
                },
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            default=str,
        )
    )


def _recursive_proof_cache_served_frontier(
    proof_cache: Any,
    *,
    conv: Any,
    proof_state: Any,
) -> Dict[str, Any]:
    """Fingerprint helpers exposed to cache-hit-capable child goals."""

    frontier_config = getattr(proof_cache, "solver_frontier_config", None)
    if not callable(frontier_config):
        return {}
    statements: Set[str] = set()
    for node in dict(getattr(proof_state, "nodes", {}) or {}).values():
        if str(getattr(node, "kind", "") or "") != "child_goal":
            continue
        if str(getattr(node, "status", "") or "") != "open":
            continue
        if bool(getattr(node, "falsified", False)):
            continue
        target = str(getattr(node, "target", "") or "").strip()
        if target:
            statements.add(target)
    statements.discard("")
    preamble = str(
        getattr(conv, "lean_preamble", None) or getattr(conv, "preamble", "") or ""
    )
    try:
        return dict(
            frontier_config(
                sorted(statements),
                preamble=preamble,
                max_hits=3,
            )
            or {}
        )
    except Exception:
        return {}


def _recursive_runtime_capability_fingerprint(value: Any) -> Dict[str, Any]:
    """Stable semantic identity for a live retrieval/cache capability.

    Fresh wrappers around the same corpus/configuration are equivalent.  A
    process-local object nonce would mint unlimited paid lanes when recursive
    callbacks rebuild those wrappers, so only explicit semantic generations
    participate in this fingerprint.
    """

    if value is None:
        return {}
    record: Dict[str, Any] = {
        "type": f"{type(value).__module__}.{type(value).__qualname__}",
    }
    for field_name in (
        "capability",
        "mode",
        "root",
        "index_snapshot_id",
        "environment_hash",
        "environment_key",
        "snapshot_id",
        "compatibility_snapshot_id",
        "schema_version",
        "policy_version",
        "capability_generation",
        "generation_id",
        "enabled",
        "path",
        "run_id",
    ):
        try:
            field_value = getattr(value, field_name)
            if callable(field_value):
                field_value = field_value()
        except Exception:
            continue
        if field_value not in (None, ""):
            record[field_name] = field_value
    active_bundle_ids = getattr(value, "active_bundle_ids", None)
    if callable(active_bundle_ids):
        try:
            record["active_bundle_ids"] = tuple(active_bundle_ids() or ())
        except Exception:
            pass
    request_config = getattr(value, "request_config", None)
    if callable(request_config):
        try:
            record["request_config"] = request_config()
        except Exception:
            pass
    nested_client = getattr(value, "client", None)
    if nested_client is not None:
        record["provider_policy"] = _recursive_client_provider_policy(nested_client)
    return record


def _recursive_config_fingerprint(value: Any) -> str:
    if value is None:
        return ""
    try:
        record = asdict(value) if is_dataclass(value) else vars(value)
    except Exception:
        record = {
            "type": f"{type(value).__module__}.{type(value).__qualname__}",
        }
    return text_hash(
        json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            default=lambda item: f"{type(item).__module__}.{type(item).__qualname__}",
        )
    )


def _recursive_conversation_lane_paid_failure_count(
    session: MiniSession,
    *,
    include_unapplied_exposure: bool = False,
) -> int:
    def nonnegative_int(value: Any) -> int:
        try:
            return max(0, int(value or 0))
        except (TypeError, ValueError, OverflowError):
            return 0

    failure_count = nonnegative_int(
        getattr(session, "_recursive_paid_no_artifact_attempt_count", 0)
    )
    if failure_count == 0:
        records = [
            (str(key or ""), value)
            for key, value in session.model_call_deferred_static_action_metadata.items()
            if str(key or "").startswith("conversation_turn_")
        ]
        for _action_id, raw_record in records:
            record = dict(raw_record or {})
            if str(record.get("llm_failure_kind") or "").strip() not in (
                _RECURSIVE_PAID_NO_ARTIFACT_KINDS
            ):
                continue
            if not bool(record.get("llm_retryable", False)):
                continue
            completed = nonnegative_int(record.get("provider_calls_completed", 0))
            dispatched = nonnegative_int(record.get("provider_dispatches_started", 0))
            if completed > 0 or dispatched > 0:
                scheduler_retries = max(
                    (
                        nonnegative_int(value)
                        for value in (
                            *session.model_call_deferred_static_retry_counts.values(),
                            *session.model_call_deferred_frontier_retry_counts.values(),
                        )
                    ),
                    default=0,
                )
                failure_count = 1 + scheduler_retries
                break
    if include_unapplied_exposure:
        cleanup = dict(getattr(session, "_mini_recursive_cleanup_outcome", {}) or {})
        completed = max(
            nonnegative_int(getattr(session, "provider_calls_completed_total", 0)),
            nonnegative_int(cleanup.get("provider_calls_completed", 0)),
        )
        dispatched = max(
            nonnegative_int(getattr(session, "provider_dispatches_started_total", 0)),
            nonnegative_int(cleanup.get("provider_dispatches_started", 0)),
            nonnegative_int(
                getattr(
                    getattr(
                        session,
                        "_inflight_provider_exposure_tracker",
                        None,
                    ),
                    "provider_dispatches_started",
                    0,
                )
            ),
        )
        applied_completed = getattr(
            session,
            "_recursive_paid_no_artifact_provider_calls_applied",
            None,
        )
        applied_dispatched = getattr(
            session,
            "_recursive_paid_no_artifact_provider_dispatches_applied",
            None,
        )
        if applied_completed is None or applied_dispatched is None:
            # Old/restored sessions have no authenticated watermark.  Preserve
            # solving capability instead of guessing that settled historical
            # calls are a new failed attempt.
            applied_completed = completed if failure_count > 0 else 0
            applied_dispatched = dispatched if failure_count > 0 else 0
        # At most one provider request can be exposed between the last applied
        # child outcome and cleanup. Charge that final request exactly once.
        if completed > nonnegative_int(
            applied_completed
        ) or dispatched > nonnegative_int(applied_dispatched):
            failure_count += 1
    return failure_count


def _consume_sample_task_exception(task: asyncio.Task[Any]) -> None:
    """Observe a detached parallel-sample result without mutating run state."""

    if task.cancelled():
        return
    try:
        task.exception()
    except asyncio.CancelledError:
        return
    except Exception:
        return


_CONSUME_SAMPLE_TASK_EXCEPTION = mark_runtime_owned_callback(
    _consume_sample_task_exception
)


def _session_theory_promotion_enabled(session: Any) -> bool:
    return bool(
        getattr(session, "theory_promote_verified_helpers", False)
        and getattr(session, "theory_library", None) is not None
        and str(getattr(session.theory_library, "mode", "off") or "off") == "build"
    )


def _session_promotion_metadata(
    session: Any,
    source_dossier: Any = None,
) -> dict[str, Any]:
    problem = getattr(session, "problem", None)
    theorem_name = str(getattr(problem, "theorem_name", "") or "").strip()
    session_dossier = getattr(session, "dossier", None)
    root_theorem_name = str(
        getattr(session_dossier, "cache_owner_theorem_name", "")
        or getattr(source_dossier, "cache_owner_theorem_name", "")
        or theorem_name
    ).strip()
    builder = getattr(session, "theory_candidate_builder", None)
    protected_names = {
        str(item or "").strip()
        for item in (
            theorem_name,
            root_theorem_name,
            getattr(session_dossier, "theorem_name", ""),
            getattr(session_dossier, "cache_owner_theorem_name", ""),
            getattr(source_dossier, "theorem_name", ""),
            getattr(source_dossier, "cache_owner_theorem_name", ""),
        )
        if str(item or "").strip()
    }
    problem_constants = set(protected_names)
    for protected_name in tuple(protected_names):
        # The filled official-answer definition is most dangerous precisely
        # when visible-answer mode exposes it. Ban it in every mode; banning a
        # name absent from a particular project is harmless.
        problem_constants.add(f"{protected_name}_solution")
    workspace_id = str(
        getattr(session, "_theory_promotion_workspace_id", "") or ""
    ).strip()
    if not workspace_id:
        workspace_id = uuid.uuid4().hex
        session._theory_promotion_workspace_id = workspace_id
    return {
        "domain": str(
            getattr(session, "theory_domain", "general mathematics")
            or "general mathematics"
        ),
        "imports": tuple(
            getattr(session, "theory_default_imports", ()) or ("Mathlib",)
        ),
        "owner_id": str(
            getattr(
                getattr(session.theory_library, "lease_owner", None),
                "owner_id",
                "",
            )
            or ""
        ),
        "workspace_id": workspace_id,
        "generated_by_run": str(getattr(builder, "generated_by_run", "") or ""),
        "generated_by_model": str(getattr(builder, "generated_by_model", "") or ""),
        # Root provenance lets startup recovery find helpers accepted in a
        # nested obligation after a hard process loss.  The child theorem is
        # still present in ordinary session/event diagnostics.
        "source_theorem": root_theorem_name,
        "forbidden_problem_constants": tuple(sorted(problem_constants)),
    }


def _stage_session_verified_helper(
    session: Any,
    helper: Any,
    source_dossier: Any = None,
    *,
    force: bool = False,
) -> Any:
    """Write one fail-open receipt without compiling or delaying selection."""

    if not _session_theory_promotion_enabled(session):
        return None
    if not force:
        helper_name = str(getattr(helper, "name", "") or "").strip()
        persisted_fingerprints = dict(
            getattr(session, "_theory_promotion_helper_fingerprints", {}) or {}
        )
        if helper_name and persisted_fingerprints.get(
            helper_name
        ) == _helper_promotion_fingerprint(helper):
            # Workspace publication deliberately revisits every verified
            # helper. Once this exact promotion payload is durable, another
            # callback is neither new authority nor useful telemetry.
            return SimpleNamespace(
                staged=True,
                entry_id="",
                diagnostic="promotion_receipt_already_durable",
                error_kind="",
                error="",
            )
    if not force and time.monotonic() < float(
        getattr(session, "_theory_promotion_retry_after_monotonic", 0.0) or 0.0
    ):
        return SimpleNamespace(
            staged=False,
            entry_id="",
            diagnostic="promotion_receipt_retry_backoff",
            error_kind="",
            error="",
        )
    outbox = getattr(session, "_theory_promotion_outbox", None)
    result: Any = None
    if outbox is None:
        try:
            outbox = PromotionOutbox(session.theory_library)
            session._theory_promotion_outbox = outbox
        except Exception as exc:
            result = SimpleNamespace(
                staged=False,
                entry_id="",
                diagnostic="promotion_outbox_unavailable",
                error_kind=type(exc).__name__,
                error=str(exc),
            )
    if outbox is not None:
        metadata = _session_promotion_metadata(session, source_dossier)
        helper_lookup = dict(
            getattr(
                source_dossier or session.dossier,
                "verified_helpers",
                {},
            )
            or {}
        )
        reuse_equivalent = getattr(outbox, "reuse_equivalent_work", None)
        if str(
            getattr(helper, "phase", "") or ""
        ) == "proof_state_cache_seed" and callable(reuse_equivalent):
            result = reuse_equivalent(
                helper,
                **metadata,
                helper_lookup=helper_lookup,
            )
        if result is None:
            result = outbox.enqueue(
                helper,
                **metadata,
                helper_lookup=helper_lookup,
            )
    record = {
        "phase": "domain_theory_promotion_receipt",
        "helper_name": str(getattr(helper, "name", "") or ""),
        "entry_id": str(getattr(result, "entry_id", "") or ""),
        "staged": bool(getattr(result, "staged", False)),
        "diagnostic": str(getattr(result, "diagnostic", "") or ""),
        "verdict": (
            "helper_promotion_staged"
            if bool(getattr(result, "staged", False))
            else "helper_promotion_not_staged"
        ),
    }
    error = str(getattr(result, "error", "") or "")
    if error:
        record["error"] = (
            f"{str(getattr(result, 'error_kind', '') or 'Error')}: {error}"
        )
    try:
        session._record_event(record)
    except Exception:
        pass
    increment = getattr(session.dossier, "increment_tool_metric", None)
    if callable(increment):
        try:
            increment(
                (
                    "mini_theory_promotion_receipts_staged"
                    if bool(getattr(result, "staged", False))
                    else "mini_theory_promotion_receipt_failures"
                ),
                1,
            )
        except Exception:
            pass
    authority_persisted = _promotion_stage_result_is_settled(result)
    if authority_persisted:
        session._theory_promotion_persistence_failures = 0
        session._theory_promotion_retry_after_monotonic = 0.0
        name = str(getattr(helper, "name", "") or "").strip()
        if name:
            known = set(
                getattr(session, "_theory_promotion_known_helper_names", set()) or set()
            )
            known.add(name)
            session._theory_promotion_known_helper_names = known
            fingerprints = dict(
                getattr(session, "_theory_promotion_helper_fingerprints", {}) or {}
            )
            fingerprints[name] = _helper_promotion_fingerprint(helper)
            session._theory_promotion_helper_fingerprints = fingerprints
            durable_dossier = source_dossier or session.dossier
            durable_fingerprints = dict(
                getattr(
                    durable_dossier,
                    "theory_promotion_durable_helper_fingerprints",
                    {},
                )
                or {}
            )
            durable_fingerprints[name] = fingerprints[name]
            durable_dossier.theory_promotion_durable_helper_fingerprints = (
                durable_fingerprints
            )
    else:
        failures = (
            max(
                0,
                int(
                    getattr(
                        session,
                        "_theory_promotion_persistence_failures",
                        0,
                    )
                    or 0
                ),
            )
            + 1
        )
        session._theory_promotion_persistence_failures = failures
        session._theory_promotion_retry_after_monotonic = time.monotonic() + min(
            30.0,
            0.25 * (2 ** min(failures - 1, 7)),
        )
    return result


def _promotion_stage_result_is_settled(result: Any) -> bool:
    """Whether staging durably resolved this helper's promotion authority."""

    diagnostic = str(getattr(result, "diagnostic", "") or "")
    return bool(getattr(result, "staged", False)) or (
        diagnostic == "missing_helper_identity"
        or diagnostic.startswith("non_generic_")
    )


def _helper_promotion_fingerprint(helper: Any) -> tuple[Any, ...]:
    return (
        str(getattr(helper, "source_hash", "") or ""),
        str(getattr(helper, "render_policy", "") or ""),
        tuple(
            sorted(
                str(item or "") for item in getattr(helper, "quality_tags", ()) or ()
            )
        ),
        tuple(
            sorted(
                str(item or "") for item in getattr(helper, "provenance_tags", ()) or ()
            )
        ),
        tuple(str(item or "") for item in getattr(helper, "support_names", ()) or ()),
        tuple(
            sorted(
                (str(key or ""), str(value or ""))
                for key, value in dict(
                    getattr(helper, "support_source_hashes", {}) or {}
                ).items()
            )
        ),
    )


def _initialize_promotion_helper_baseline(
    session: Any,
    durable_parent_fingerprints: Optional[Mapping[str, tuple[Any, ...]]] = None,
) -> None:
    """Suppress only inherited helpers already attested durable by a parent."""

    helpers = dict(getattr(session.dossier, "verified_helpers", {}) or {})
    durable = dict(durable_parent_fingerprints or {})
    fingerprints = {
        name: _helper_promotion_fingerprint(helper)
        for name, helper in helpers.items()
        if durable.get(name) == _helper_promotion_fingerprint(helper)
    }
    # A copied fingerprint is only a claim until the current configured
    # outbox/root re-attests it. Keep locally persisted receipts separate so
    # ordinary reconciliation remains O(number of changed helpers).
    session._theory_promotion_known_helper_names = set()
    session._theory_promotion_helper_fingerprints = {}
    session._theory_promotion_inherited_helper_fingerprints = fingerprints


def _stage_all_session_verified_helpers(
    session: Any,
    *,
    force: bool = False,
) -> bool:
    if not _session_theory_promotion_enabled(session):
        return True
    if not force and time.monotonic() < float(
        getattr(session, "_theory_promotion_retry_after_monotonic", 0.0) or 0.0
    ):
        return False
    all_settled = True
    helpers = dict(getattr(session.dossier, "verified_helpers", {}) or {})
    known = set(
        getattr(session, "_theory_promotion_known_helper_names", set()) or set()
    )
    fingerprints = dict(
        getattr(session, "_theory_promotion_helper_fingerprints", {}) or {}
    )
    durable_fingerprints = dict(
        getattr(
            session.dossier,
            "theory_promotion_durable_helper_fingerprints",
            {},
        )
        or {}
    )
    inherited_fingerprints = dict(
        getattr(
            session,
            "_theory_promotion_inherited_helper_fingerprints",
            {},
        )
        or {}
    )
    claimed_durable_names: set[str] = set()
    for name, helper in helpers.items():
        fingerprint = _helper_promotion_fingerprint(helper)
        if fingerprints.get(name) != fingerprint and (
            inherited_fingerprints.get(name) == fingerprint
            or durable_fingerprints.get(name) == fingerprint
        ):
            claimed_durable_names.add(name)
    if claimed_durable_names:
        try:
            outbox = getattr(session, "_theory_promotion_outbox", None)
            if outbox is None:
                outbox = PromotionOutbox(session.theory_library)
                session._theory_promotion_outbox = outbox
            metadata = _session_promotion_metadata(session)
            attested_names = outbox.durably_attested_helpers(
                helpers,
                domain=str(metadata.get("domain") or ""),
                imports=tuple(metadata.get("imports") or ()),
                owner_id=str(metadata.get("owner_id") or ""),
                workspace_id=str(metadata.get("workspace_id") or ""),
                source_theorem=str(metadata.get("source_theorem") or ""),
                forbidden_problem_constants=tuple(
                    metadata.get("forbidden_problem_constants") or ()
                ),
                # Only helpers carrying a parent durability fingerprint reach
                # this query. Their immutable source predates this recursive
                # obligation, so a receipt guarded against the same root
                # theorem remains authoritative even though child metadata
                # adds the child's theorem constants to newly staged helpers.
                allow_inherited_root_policy=True,
            )
        except Exception:
            attested_names = set()
        # Fan-in can add a durable child receipt after the session baseline was
        # constructed. Trust it only when the current configured outbox still
        # contains an exact authoritative receipt; copied fingerprints alone
        # are not authority across roots, policy changes, or tombstones.
        for name in claimed_durable_names:
            helper = helpers[name]
            fingerprint = _helper_promotion_fingerprint(helper)
            if name in attested_names:
                known.add(name)
                fingerprints[name] = fingerprint
            else:
                known.discard(name)
                fingerprints.pop(name, None)
            inherited_fingerprints.pop(name, None)
        session._theory_promotion_inherited_helper_fingerprints = inherited_fingerprints
        # Re-attestation is itself the durable reconciliation result. Publish
        # it to the session before the no-change early return below; otherwise
        # a restored consumer repeatedly rechecks the outbox while retaining
        # an empty local baseline.
        session._theory_promotion_known_helper_names = known
        session._theory_promotion_helper_fingerprints = fingerprints
    for name, helper in tuple(helpers.items()):
        if fingerprints.get(name) != _helper_promotion_fingerprint(helper):
            try:
                result = _stage_session_verified_helper(session, helper, force=force)
            except Exception:
                all_settled = False
                continue
            if not _promotion_stage_result_is_settled(result):
                all_settled = False
    removed = known - set(helpers)
    if not removed:
        return all_settled
    outbox = getattr(session, "_theory_promotion_outbox", None)
    if outbox is None:
        try:
            outbox = PromotionOutbox(session.theory_library)
            session._theory_promotion_outbox = outbox
        except Exception:
            return False
    metadata = _session_promotion_metadata(session)
    owner_id = str(metadata.get("owner_id") or "")
    for name in sorted(removed):
        try:
            revoked = outbox.revoke(
                name,
                owner_id=owner_id,
                workspace_id=str(metadata.get("workspace_id") or ""),
                reason="helper_removed_from_authoritative_dossier",
            )
            if revoked:
                known.discard(name)
                fingerprints.pop(name, None)
                durable_fingerprints = dict(
                    getattr(
                        session.dossier,
                        "theory_promotion_durable_helper_fingerprints",
                        {},
                    )
                    or {}
                )
                durable_fingerprints.pop(name, None)
                session.dossier.theory_promotion_durable_helper_fingerprints = (
                    durable_fingerprints
                )
            else:
                all_settled = False
        except Exception:
            all_settled = False
            continue
    session._theory_promotion_known_helper_names = known
    session._theory_promotion_helper_fingerprints = fingerprints
    return all_settled


def _formal_state_search_aggregate_seconds(config: Any) -> float:
    """Total wall-clock ceiling for formal state search across all contexts.

    Derived from the search's own declared bounds -- one full quantum budget
    per permitted no-improvement quantum -- rather than a fresh constant, so
    tuning ``--formal-state-search-timeout-s`` or the no-improvement allowance
    moves the ceiling with it.  Returns 0.0 (unset) when either bound is
    disabled, preserving the previous unbounded behaviour for that config.
    """

    normalized = config.normalized() if hasattr(config, "normalized") else config
    quantum_s = max(0.0, float(getattr(normalized, "total_timeout_s", 0.0) or 0.0))
    quanta = max(0, int(getattr(normalized, "max_no_improvement_quanta", 0) or 0))
    if quantum_s <= 0.0 or quanta <= 0:
        return 0.0
    return quantum_s * float(quanta)


def _bind_answer_safe_retrieval_context(
    searcher: Any,
    *,
    problem: TheoremProblem,
    llm_preamble: str,
    lean_preamble: str,
) -> Any:
    """Expose only prompt-visible pre-target declarations to this session."""

    bind = getattr(searcher, "with_answer_safe_preamble", None)
    if callable(bind):
        searcher = bind(
            str(llm_preamble or ""),
            lean_preamble=str(lean_preamble or ""),
            theorem_name=str(getattr(problem, "theorem_name", "") or ""),
            source_path=str(getattr(problem, "path", "") or ""),
            environment_hash=text_hash(str(lean_preamble or "")),
        )
    # Binding may return a new immutable retrieval view.  Reassert the target
    # exclusion on that exact view so direct factory callers receive the same
    # held-out-source contract as the public prove_problem wrapper.
    set_excluded_target = getattr(searcher, "set_excluded_target", None)
    if callable(set_excluded_target):
        set_excluded_target(
            declaration_names=(str(getattr(problem, "theorem_name", "") or ""),),
            source_paths=(
                (str(getattr(problem, "path", "") or ""),)
                if bool(getattr(problem, "exclude_entire_source_from_retrieval", False))
                else ()
            ),
        )
    return searcher


def _mini_recursive_config_from_params(
    *,
    mini_recursive_passes: int,
    mini_recursive_max_claims: int,
    mini_recursive_turns_per_claim: int,
    mini_recursive_tactic_timeout_s: float,
    mini_recursive_tactic_max_candidates: int,
    falsification_enabled: bool = True,
    falsification_max_checks: int = 32,
    falsification_operation_timeout_s: float = (
        DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S
    ),
    falsification_engine_timeout_s: float = DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
    mini_phase_temperatures: Optional[Any] = None,
    sample_temperature: Optional[float] = None,
    planner_client: Any = None,
    refiner_client: Any = None,
) -> Any:
    from ..mini_recursive import (
        MiniRecursiveConfig,
        production_planner_deliberation_default,
    )

    return MiniRecursiveConfig(
        planner_deliberation_enabled=(production_planner_deliberation_default()),
        **_mini_recursive_planner_deadline_kwargs(planner_client),
        planner_sanity_contract_required=True,
        passes=int(mini_recursive_passes or 1),
        max_claims=int(mini_recursive_max_claims or 1),
        turns_per_claim=int(mini_recursive_turns_per_claim or 1),
        recursive_child_max_elapsed_s=_mini_recursive_child_elapsed_budget_s(
            planner_client,
            refiner_client,
            turns_per_claim=int(mini_recursive_turns_per_claim or 1),
            tactic_timeout_s=float(mini_recursive_tactic_timeout_s or 0.0),
        ),
        tactic_timeout_s=float(mini_recursive_tactic_timeout_s or 0.0),
        tactic_max_candidates=int(mini_recursive_tactic_max_candidates or 0),
        progress_continuation_passes=1,
        mini_phase_temperatures=mini_phase_temperatures,
        sample_temperature=sample_temperature,
        falsification_enabled=bool(falsification_enabled),
        falsification_max_checks=falsification_max_checks,
        falsification_operation_timeout_s=falsification_operation_timeout_s,
        falsification_engine_timeout_s=falsification_engine_timeout_s,
    )


# One-shot outer startup-lane controls. They configure
# ``prove_problem_via_session``'s pre-session fast path only and must never
# reach ``build_session_for_prove_problem`` (which has no such parameters).
_STARTUP_ROOT_FAST_LANE_SESSION_KEYS: Tuple[str, ...] = (
    "startup_root_fast_lane_enabled",
    "startup_root_fast_lane_tactic_timeout_s",
    "startup_root_fast_lane_tactic_max_candidates",
)


def _validate_supplied_dossier_problem_identity(
    problem: TheoremProblem,
    dossier: Optional[ProofDossier],
) -> None:
    """Reject a dossier bound to a different prepared theorem target.

    A theorem-project preflight may replace ``problem.statement_type`` with
    Lean's elaborated rendering.  Re-rooting an already-populated dossier is
    not safe: its graph and private proof-state projection can contain work
    whose executable target is the old rendering.  Fail at the composition
    boundary and tell programmatic callers to construct the dossier only after
    preflight (or let the factory construct it).
    """

    if dossier is None:
        return

    expected_theorem = str(getattr(problem, "theorem_name", "") or "").strip()
    expected_statement = str(getattr(problem, "statement_type", "") or "").strip()
    # Keep the executable rendering exact. Graph statement keys intentionally
    # identify aliases such as ``Nat`` and ``ℕ``; even generic whitespace
    # folding is too broad here because whitespace inside a Lean string literal
    # is semantic, while root certificates and private proof-state snapshots
    # hash the actual stripped rendering.
    expected_statement_key = expected_statement
    mismatches: List[str] = []

    dossier_theorem = str(getattr(dossier, "theorem_name", "") or "").strip()
    if dossier_theorem != expected_theorem:
        mismatches.append(
            f"dossier.theorem_name={dossier_theorem!r} (expected {expected_theorem!r})"
        )

    def check_statement(label: str, value: Any) -> None:
        statement = str(value or "").strip()
        statement_key = statement
        if not statement or statement_key != expected_statement_key:
            mismatches.append(
                f"{label}={statement[:240]!r} (expected {expected_statement[:240]!r})"
            )

    check_statement("dossier.root_statement", dossier.root_statement)
    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        mismatches.append("dossier.proof_graph is missing")
    else:
        graph_theorem = str(getattr(graph, "theorem_name", "") or "").strip()
        if graph_theorem != expected_theorem:
            mismatches.append(
                f"dossier.proof_graph.theorem_name={graph_theorem!r} "
                f"(expected {expected_theorem!r})"
            )
        check_statement(
            "dossier.proof_graph.root_statement",
            getattr(graph, "root_statement", ""),
        )
        graph_nodes = getattr(graph, "nodes", {})
        graph_root = (
            graph_nodes.get(getattr(graph, "root_node_id", "root"))
            if isinstance(graph_nodes, dict)
            else None
        )
        if graph_root is None:
            mismatches.append("dossier.proof_graph.root_node is missing")
        else:
            check_statement(
                "dossier.proof_graph.root_node.statement",
                getattr(graph_root, "statement", ""),
            )

        execution_record = getattr(graph, "_proof_state_execution_record", None)
        if isinstance(execution_record, dict):
            execution_nodes = execution_record.get("nodes")
            if not isinstance(execution_nodes, list):
                mismatches.append("dossier.proof_graph.proof_state_root is missing")
            else:
                execution_root = next(
                    (
                        item
                        for item in execution_nodes
                        if isinstance(item, dict)
                        and (
                            str(item.get("node_id") or "") == "root"
                            or str(item.get("kind") or "") == "root"
                        )
                    ),
                    None,
                )
                if execution_root is None:
                    mismatches.append("dossier.proof_graph.proof_state_root is missing")
                else:
                    check_statement(
                        "dossier.proof_graph.proof_state_root.target",
                        execution_root.get("target"),
                    )

    if mismatches:
        raise ValueError(
            "supplied ProofDossier does not match the prepared theorem target: "
            + "; ".join(mismatches)
            + ". Construct the dossier from the post-preflight TheoremProblem "
            "or omit dossier so the MiniSession factory creates it."
        )


def _strip_startup_root_fast_lane_session_kwargs(kwargs: Dict[str, Any]) -> None:
    """Remove outer startup-lane knobs from a session-construction kwargs dict."""

    for key in _STARTUP_ROOT_FAST_LANE_SESSION_KEYS:
        kwargs.pop(key, None)


def _clone_dossier_for_session(supplied: ProofDossier) -> ProofDossier:
    """Return an isolated session-scoped dossier seeded from ``supplied``.

    The factory owns the isolation boundary for MiniSession runs.  A shallow
    clone is not enough here: recursive run records contain nested dict/list
    structures, and graph state must be re-synced after verified helpers are
    seeded so a helper-dict/graph mismatch in the caller cannot silently
    propagate into the session.
    """

    from ..proof_dossier import VerifiedHelper, clone_verified_helper

    cloned_graph = (
        supplied.proof_graph.clone()
        if getattr(supplied, "proof_graph", None) is not None
        else None
    )
    dossier = ProofDossier(
        theorem_name=supplied.theorem_name,
        root_statement=supplied.root_statement,
        problem_text=supplied.problem_text,
        cache_owner_theorem_name=str(
            getattr(supplied, "cache_owner_theorem_name", "")
            or supplied.theorem_name
            or ""
        ),
        proof_cache_publish_enabled=bool(
            getattr(supplied, "proof_cache_publish_enabled", True)
        ),
        suppress_solution_placeholders=bool(
            getattr(supplied, "suppress_solution_placeholders", True)
        ),
        proof_graph=cloned_graph,
        opaque_mode=bool(getattr(supplied, "opaque_mode", True)),
        allow_official_answer_visibility=bool(
            getattr(supplied, "allow_official_answer_visibility", False)
        ),
        official_answer_payload_present=getattr(
            supplied,
            "official_answer_payload_present",
            None,
        ),
        graph_execution_projection_mode=str(
            getattr(supplied, "graph_execution_projection_mode", "off") or "off"
        ),
        graph_execution_project_environment_hash=str(
            getattr(
                supplied,
                "graph_execution_project_environment_hash",
                "",
            )
            or ""
        ),
        current_lean_environment_hash=str(
            getattr(supplied, "current_lean_environment_hash", "") or ""
        ),
        lean_environment_ancestor_hashes=copy.deepcopy(
            getattr(supplied, "lean_environment_ancestor_hashes", {}) or {}
        ),
        lean_environment_content_digests=copy.deepcopy(
            getattr(supplied, "lean_environment_content_digests", {}) or {}
        ),
        verified_helper_eviction_generation=int(
            getattr(supplied, "verified_helper_eviction_generation", 0) or 0
        ),
    )
    for name, helper in supplied.verified_helpers.items():
        if isinstance(helper, VerifiedHelper):
            dossier.verified_helpers[name] = clone_verified_helper(helper)
        else:
            dossier.verified_helpers[name] = copy.deepcopy(helper)
    dossier.superseded_verified_helper_hashes = copy.deepcopy(
        getattr(supplied, "superseded_verified_helper_hashes", {}) or {}
    )
    dossier.verified_helper_source_hash_history = copy.deepcopy(
        getattr(supplied, "verified_helper_source_hash_history", {}) or {}
    )
    dossier.theory_promotion_durable_helper_fingerprints = copy.deepcopy(
        getattr(
            supplied,
            "theory_promotion_durable_helper_fingerprints",
            {},
        )
        or {}
    )
    # Fix 1 follow-up (2026-05-22): mirror the alias propagation that
    # ``_copy_dossier_contents`` does on the return path. Without
    # seeding the session-scoped dossier with the parent's alias map,
    # the now-symmetric writeback would actively *overwrite* the
    # parent's aliases with an empty dict at session end whenever the
    # session didn't re-discover them (for example, recursive flows with
    # pre-seeded helpers). Both sides of the isolation
    # boundary must propagate this field.
    dossier.verified_helper_statement_aliases = copy.deepcopy(
        getattr(supplied, "verified_helper_statement_aliases", {}) or {}
    )
    # ``proposed_helpers`` must flow through this clone boundary so a
    # speculative session failure does not discard newly proposed work.
    # ``_copy_dossier_contents`` (sibling, below) performs the symmetric
    # deep-copy on the return path; both sides must agree.
    dossier.proposed_helpers = copy.deepcopy(
        getattr(supplied, "proposed_helpers", {}) or {}
    )
    _transfer_validated_falsification_state(dossier, supplied)
    dossier.active_root_targets = copy.deepcopy(
        getattr(supplied, "active_root_targets", []) or []
    )
    dossier.active_root_classification_preamble_hash = str(
        getattr(supplied, "active_root_classification_preamble_hash", "") or ""
    )
    supplied_failure_reason = str(
        getattr(supplied, "session_failure_reason", "") or ""
    ).strip()
    if is_terminal_session_failure_reason(supplied_failure_reason):
        setattr(dossier, "session_failure_reason", supplied_failure_reason)
        supplied_failure_kind = str(
            getattr(supplied, "session_failure_kind", "") or ""
        ).strip()
        if supplied_failure_kind:
            setattr(dossier, "session_failure_kind", supplied_failure_kind)
    sync_helpers = getattr(dossier, "_sync_legacy_helpers_to_graph", None)
    if callable(sync_helpers):
        sync_helpers()
    graph = getattr(dossier, "proof_graph", None)
    execution_snapshot = getattr(graph, "_proof_state_execution_record", None)
    if isinstance(execution_snapshot, dict):
        # Helper re-sync deliberately refreshes graph metadata after cloning.
        # It does not alter the copied scheduler state, so rebind that private
        # state to the post-sync graph rather than accidentally treating the
        # clone as a stale external mutation.
        from ..proof_state import ProofSearchState

        graph._proof_state_execution_snapshot_fingerprint = (
            ProofSearchState._graph_execution_snapshot_fingerprint(graph)
        )
    dossier.attempts = copy.deepcopy(supplied.attempts)
    dossier.scratch = copy.deepcopy(supplied.scratch)
    dossier.accepted_proof_stubs = copy.deepcopy(
        getattr(supplied, "accepted_proof_stubs", [])
    )
    dossier.tool_metrics = copy.deepcopy(getattr(supplied, "tool_metrics", {}))
    dossier.decl_applications = copy.deepcopy(supplied.decl_applications)
    dossier.mini_recursive_runs = copy.deepcopy(supplied.mini_recursive_runs)
    dossier.proof_lineage_events = copy.deepcopy(
        getattr(supplied, "proof_lineage_events", []) or []
    )
    dossier.proof_lineage_event_ids = set(
        getattr(supplied, "proof_lineage_event_ids", set()) or ()
    )
    dossier.proof_ideas = copy.deepcopy(getattr(supplied, "proof_ideas", {}) or {})
    dossier.proof_idea_singleton_child_scope = bool(
        getattr(supplied, "proof_idea_singleton_child_scope", False)
    )
    dossier.semantic_fact_registry = copy.deepcopy(
        getattr(supplied, "semantic_fact_registry", {}) or {}
    )
    dossier.action_value_observations = copy.deepcopy(
        getattr(supplied, "action_value_observations", {}) or {}
    )
    # Match ``_copy_dossier_contents`` / writeback parity for recursive and
    # theory continuity across the session isolation boundary.
    dossier.mini_theory_snapshot = copy.deepcopy(
        getattr(supplied, "mini_theory_snapshot", ()) or ()
    )
    dossier.mini_theory_context_hash = str(
        getattr(supplied, "mini_theory_context_hash", "") or ""
    )
    dossier.mini_recursive_exhausted_claim_keys = set(
        getattr(supplied, "mini_recursive_exhausted_claim_keys", set()) or ()
    )
    dossier.mini_recursive_claim_helper_bindings = copy.deepcopy(
        getattr(supplied, "mini_recursive_claim_helper_bindings", {}) or {}
    )
    dossier.parallel_sample_proof_states = copy.deepcopy(
        getattr(supplied, "parallel_sample_proof_states", [])
    )
    dossier.parallel_sample_failures = copy.deepcopy(
        getattr(supplied, "parallel_sample_failures", [])
    )
    dossier.final_proof = getattr(supplied, "final_proof", None)
    dossier.final_proof_hash = supplied.final_proof_hash
    dossier.final_replay_helpers = list(supplied.final_replay_helpers)
    dossier.root_proof_certificate = copy.deepcopy(
        getattr(supplied, "root_proof_certificate", None)
    )
    if hasattr(supplied, "proof_state_record"):
        dossier.proof_state_record = copy.deepcopy(
            getattr(supplied, "proof_state_record") or {}
        )
    return dossier


def _clear_dossier_proof_state_projection(dossier: ProofDossier) -> str:
    """Remove stale proof-state scheduler projection after init recovery."""

    graph = getattr(dossier, "proof_graph", None)
    if graph is None:
        return "no_graph"
    pruner = getattr(graph, "prune_proof_state_projection", None)
    if callable(pruner):
        try:
            pruner()
            return "pruned"
        except Exception:
            pass
    reset = getattr(dossier, "reset_proof_graph", None)
    if callable(reset):
        reset()
        sync_helpers = getattr(dossier, "_sync_legacy_helpers_to_graph", None)
        if callable(sync_helpers):
            sync_helpers()
        return "reset"
    return "unavailable"


def _snapshot_session_state_for_caller(session: MiniSession) -> None:
    """Attach the latest proof-state record before copying a session dossier."""

    conv = getattr(session, "conv", None)
    if conv is not None:
        cluster = str(getattr(session, "last_giveup_cluster", "") or "").strip()
        if cluster:
            try:
                setattr(conv, "_last_giveup_cluster", cluster)
                setattr(
                    conv,
                    "_last_giveup_match",
                    str(getattr(session, "last_giveup_match", "") or ""),
                )
            except Exception:
                pass
        terminal_reason = str(
            getattr(session, "terminal_failure_reason", "") or ""
        ).strip()
        if terminal_reason:
            try:
                setattr(conv, "_last_llm_failure_reason", terminal_reason)
                setattr(
                    conv,
                    "_last_llm_failure_kind",
                    str(getattr(session, "terminal_failure_kind", "") or ""),
                )
            except Exception:
                pass
        outcome_metadata = getattr(session, "last_action_outcome_metadata", {}) or {}
        if isinstance(outcome_metadata, dict):
            scoped_reason = str(
                outcome_metadata.get("scoped_failure_reason") or ""
            ).strip()
            if (
                not scoped_reason
                and str(outcome_metadata.get("llm_failure_scope") or "").strip()
                == "scoped"
            ):
                scoped_reason = str(
                    outcome_metadata.get("terminal_failure_reason")
                    or outcome_metadata.get("llm_failure_kind")
                    or getattr(session, "last_failure_reason", "")
                    or ""
                ).strip()
            if scoped_reason and llm_failure_scope(scoped_reason) == "scoped":
                try:
                    setattr(conv, "_last_llm_failure_reason", scoped_reason)
                    setattr(
                        conv,
                        "_last_llm_failure_kind",
                        str(
                            outcome_metadata.get("llm_failure_kind")
                            or outcome_metadata.get("terminal_failure_kind")
                            or scoped_reason
                            or ""
                        ).strip(),
                    )
                except Exception:
                    pass

    dossier = getattr(session, "dossier", None)
    if dossier is not None:
        theory_snapshot = tuple(
            dict(item) for item in getattr(session, "theory_snapshot", ()) or ()
        )
        setattr(dossier, "mini_theory_snapshot", theory_snapshot)
        setattr(
            dossier,
            "mini_theory_context_hash",
            str(
                getattr(
                    getattr(session, "theory_context_pair", None), "snapshot_hash", ""
                )
                or ""
            ),
        )
        certificate = getattr(dossier, "root_proof_certificate", None)
        if isinstance(certificate, dict) and theory_snapshot:
            certificate["mini_theory_snapshot"] = list(theory_snapshot)
            certificate["mini_theory_context_hash"] = str(
                getattr(dossier, "mini_theory_context_hash", "") or ""
            )
    proof_state = getattr(session, "proof_state", None)
    if dossier is None or proof_state is None:
        return
    to_record = getattr(proof_state, "to_record", None)
    if not callable(to_record):
        return
    try:
        dossier.proof_state_record = to_record()
    except Exception:
        return
    to_execution_record = getattr(proof_state, "to_execution_record", None)
    graph = getattr(dossier, "proof_graph", None)
    if callable(to_execution_record) and graph is not None:
        try:
            # Keep a caller snapshot executable across an in-process graph
            # clone without weakening the public dossier serialization.
            graph._proof_state_execution_record = to_execution_record()
            fingerprint = getattr(
                proof_state,
                "_graph_execution_snapshot_fingerprint",
                None,
            )
            if callable(fingerprint):
                graph._proof_state_execution_snapshot_fingerprint = fingerprint(graph)
        except Exception:
            pass


_MINI_THEORY_SNAPSHOT_KEYS = frozenset(
    {
        "bundle_id",
        "module_name",
        "source_hash",
        "compiled_artifact_hash",
        "lean_toolchain",
        "mathlib_revision",
        "policy_version",
    }
)


def _validated_dossier_theory_bundle_ids(
    dossier: ProofDossier,
    theory_library: Any,
) -> Tuple[str, ...]:
    """Recover an exact, dependency-closed theory selection or fail closed.

    A parallel sample may install additional published theory before failing.
    Its verified helpers are only executable in that exact environment.  The
    dossier snapshot is therefore an integrity contract, not a hint: every
    provenance field must still match the live library and the recorded order
    must already be the library's dependency closure.
    """

    raw_snapshot = tuple(getattr(dossier, "mini_theory_snapshot", ()) or ())
    if not raw_snapshot:
        return ()
    if theory_library is None or getattr(theory_library, "mode", "off") == "off":
        raise ValueError(
            "selected parallel sample requires Mini theory, but its library "
            "is unavailable"
        )

    recorded_snapshot: List[Dict[str, Any]] = []
    recorded_bundle_ids: List[str] = []
    for index, item in enumerate(raw_snapshot):
        if not isinstance(item, dict):
            raise ValueError(
                "selected parallel sample has a malformed Mini theory "
                f"snapshot record at index {index}"
            )
        record = dict(item)
        if frozenset(record) != _MINI_THEORY_SNAPSHOT_KEYS:
            raise ValueError(
                "selected parallel sample has an incomplete or unknown Mini "
                f"theory snapshot schema at index {index}"
            )
        bundle_id = str(record.get("bundle_id") or "").strip()
        if not bundle_id or bundle_id in recorded_bundle_ids:
            raise ValueError(
                "selected parallel sample has an empty or duplicate Mini "
                f"theory bundle id at index {index}"
            )
        record["bundle_id"] = bundle_id
        recorded_snapshot.append(record)
        recorded_bundle_ids.append(bundle_id)

    try:
        live_snapshot = tuple(
            dict(item) for item in theory_library.snapshot(tuple(recorded_bundle_ids))
        )
    except Exception as exc:
        raise ValueError(
            "selected parallel sample Mini theory snapshot is unavailable: "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    if live_snapshot != tuple(recorded_snapshot):
        raise ValueError(
            "selected parallel sample Mini theory snapshot no longer matches "
            "the dependency-closed live library"
        )
    live_bundle_ids = tuple(
        str(item.get("bundle_id") or "").strip() for item in live_snapshot
    )
    if live_bundle_ids != tuple(recorded_bundle_ids):
        raise ValueError(
            "selected parallel sample Mini theory snapshot is not in exact "
            "dependency-closed order"
        )
    return live_bundle_ids


def _route_assembly_budget_seconds(*, timeout_s: float, max_invocations: int) -> float:
    """Wall-clock budget that cannot starve configured route-root closes."""

    invocations = max(1, int(max_invocations or 1))
    timeout = max(1.0, float(timeout_s or 0.0))
    return max(30.0, float(invocations) * timeout + 30.0)


def _client_llm_turn_elapsed_budget_s(client: Any) -> float:
    cfg = getattr(client, "cfg", None)
    # Role ``timeout_s`` remains provider/request configuration in soft mode;
    # it is not an implicit whole-turn kill switch.  Only an explicit hard
    # policy opts a MiniSession conversation turn into elapsed cancellation.
    policy = str(getattr(cfg, "llm_deadline_policy", "soft") or "soft").strip().lower()
    if policy != "hard":
        return 0.0
    # Match ``OpenAICompatClient._operation_deadline`` exactly.  When an
    # explicit operation window is absent, ``timeout_s`` is one provider
    # request and the client reserves a second request window for a retry.
    # Giving ConversationTurn only the first window would cancel its tool
    # loop before the client can execute the retry it was configured to have.
    try:
        operation_timeout = float(getattr(cfg, "operation_timeout_s", 0.0) or 0.0)
    except (TypeError, ValueError):
        operation_timeout = 0.0
    if operation_timeout > 0.0:
        return operation_timeout
    try:
        request_timeout = float(getattr(cfg, "timeout_s", 0.0) or 0.0)
    except (TypeError, ValueError):
        request_timeout = 0.0
    if request_timeout > 0.0:
        return request_timeout * 2.0
    return 0.0


def _mini_recursive_planner_deadline_kwargs(client: Any) -> Dict[str, Any]:
    """Give background planning the same finite lane lease as conversation."""

    cfg = getattr(client, "cfg", None)
    try:
        request_timeout_s = float(
            getattr(cfg, "request_timeout_s", 0.0)
            or getattr(cfg, "timeout_s", 0.0)
            or 0.0
        )
    except (TypeError, ValueError):
        request_timeout_s = 0.0
    operation_timeout_s = _client_llm_turn_elapsed_budget_s(client)
    if operation_timeout_s <= 0.0:
        # Soft policy deliberately does not turn one provider response into a
        # local abort. It still needs a finite cumulative scheduler lease,
        # otherwise a background planner can retain its reservation forever.
        # Match the conversation tool loop: prefer an explicit operation
        # window, then allow one request plus one retry window.
        try:
            configured_operation_timeout_s = float(
                getattr(cfg, "operation_timeout_s", 0.0) or 0.0
            )
        except (TypeError, ValueError):
            configured_operation_timeout_s = 0.0
        operation_timeout_s = (
            configured_operation_timeout_s
            if configured_operation_timeout_s > 0.0
            else request_timeout_s * 2.0
        )
    if operation_timeout_s <= 0.0:
        return {"planner_deadlines_enabled": False}
    if request_timeout_s <= 0.0:
        request_timeout_s = operation_timeout_s
    request_timeout_s = max(1.0, request_timeout_s)
    operation_timeout_s = max(1.0, operation_timeout_s)
    return {
        "planner_deadlines_enabled": True,
        "planner_request_timeout_s": request_timeout_s,
        "planner_operation_timeout_s": operation_timeout_s,
        "planner_composite_timeout_s": operation_timeout_s,
    }


def _mini_recursive_child_elapsed_budget_s(
    *clients: Any,
    turns_per_claim: int,
    tactic_timeout_s: float,
) -> float:
    """Derive one finite whole-claim lease from its admitted work.

    A recursive claim may consume at most ``turns_per_claim`` provider
    operations across its prover/refiner handoff.  Each turn also receives one
    bounded tactic allowance.  Size every turn for the slowest admitted lane:
    the shared lease must cover either role without resetting at handoff or
    shrinking the refiner's declared solving budget.
    """

    provider_operation_s = 0.0
    for client in clients:
        planner_deadlines = _mini_recursive_planner_deadline_kwargs(client)
        try:
            candidate_operation_s = float(
                planner_deadlines.get("planner_operation_timeout_s", 0.0) or 0.0
            )
        except (TypeError, ValueError, OverflowError):
            continue
        if math.isfinite(candidate_operation_s):
            provider_operation_s = max(
                provider_operation_s,
                candidate_operation_s,
            )
    if not math.isfinite(provider_operation_s) or provider_operation_s <= 0.0:
        return 0.0
    turns = max(1, int(turns_per_claim or 1))
    try:
        tactic_s = max(0.0, float(tactic_timeout_s or 0.0))
    except (TypeError, ValueError, OverflowError):
        tactic_s = 0.0
    if not math.isfinite(tactic_s):
        tactic_s = 0.0
    return float(turns) * (provider_operation_s + tactic_s)


def _effective_compute_examples_tool_enabled(
    raw_enabled: Any,
    *,
    lean_check_tool_enabled: bool,
    try_lean_tool_enabled: bool,
    apply_decl_to_goal_tool_enabled: bool,
    searcher: Optional[MathlibApiSearcher],
) -> bool:
    """Resolve compute_examples enablement as an explicit schema opt-in."""

    del lean_check_tool_enabled, try_lean_tool_enabled
    del apply_decl_to_goal_tool_enabled, searcher
    return bool(raw_enabled)


def _kwargs_compute_examples_tool_enabled(
    kwargs: Dict[str, Any],
    *,
    searcher: Optional[MathlibApiSearcher] = None,
) -> bool:
    return _effective_compute_examples_tool_enabled(
        kwargs.get("compute_examples_tool_enabled"),
        lean_check_tool_enabled=bool(kwargs.get("lean_check_tool_enabled", True)),
        try_lean_tool_enabled=bool(kwargs.get("try_lean_tool_enabled", True)),
        apply_decl_to_goal_tool_enabled=bool(
            kwargs.get("apply_decl_to_goal_tool_enabled", True)
        ),
        searcher=searcher if searcher is not None else kwargs.get("searcher"),
    )


def _bind_theory_candidate_builder(
    builder: Optional[Any],
    cost_controller: Any,
) -> Optional[Any]:
    """Return a run-local builder meter binding when the builder supports it."""

    binder = getattr(builder, "with_cost_controller", None)
    if not callable(binder):
        return builder
    effective_controller = (
        cost_controller
        if cost_controller is not None
        else getattr(builder, "cost_controller", None)
    )
    return binder(effective_controller)


def _validate_cached_cost_budget_pricing(
    *,
    cost_controller: Any,
    role_clients: Sequence[tuple[str, Any]],
) -> None:
    """Fail synchronously before factory side effects on unpriced clients.

    Async entry points refresh OpenRouter's catalog first.  The synchronous
    factory deliberately accepts only local/direct pricing or an already
    refreshed catalog so it cannot hide network I/O inside session assembly.
    """

    if not bool(getattr(cost_controller, "budget_enabled", False)):
        return
    unknown: List[tuple[str, str, str]] = []
    seen: Set[tuple[str, str, str]] = set()
    for role, client in role_clients:
        if client is None:
            continue
        for model, base_url in reservation_pricing_targets(client):
            identity = (str(role or "llm"), str(model or ""), str(base_url or ""))
            if identity in seen:
                continue
            seen.add(identity)
            if lookup_known_token_pricing(base_url, model) is None:
                unknown.append(identity)
    if unknown:
        detail = ", ".join(
            f"{role}={model}@{base_url}" for role, model, base_url in unknown
        )
        raise ValueError(
            "enabled cost budgeting requires known token pricing before "
            f"MiniSession construction; missing: {detail}"
        )


def build_session_for_prove_problem(
    *,
    problem: TheoremProblem,
    prover_client: OpenAICompatClient,
    refiner_client: Optional[OpenAICompatClient],
    planner_escalation_client: Optional[OpenAICompatClient] = None,
    lean: LeanRunner,
    max_prove_turns: int,
    max_refine_turns: int,
    trace_prefix: str = "",
    recorder: Optional[Any] = None,
    searcher: Optional[MathlibApiSearcher] = None,
    mathematical_retrieval_enabled: bool = True,
    cost_controller: Optional[Any] = None,
    lean_check_tool_enabled: bool = True,
    try_lean_tool_enabled: bool = True,
    compute_examples_tool_enabled: Optional[bool] = None,
    apply_decl_to_goal_tool_enabled: bool = True,
    max_tool_calls_per_turn: int = 10,
    raw_feedback: bool = False,
    dossier: Optional[ProofDossier] = None,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    premise_retrieval_enabled: bool = False,
    premise_retrieval_top_k: int = PREMISE_DEFAULT_TOP_K,
    repair_retrieval_enabled: bool = True,
    proof_state_retrieval_enabled: bool = False,
    repair_retrieval_top_k: int = 6,
    parallel_samples: int = 1,
    parallel_temperatures: Sequence[float] = (),
    proof_state_engine_enabled: bool = True,
    proof_state_child_tactics_enabled: bool = True,
    proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
    proof_state_child_tactic_max_candidates: int = 32,
    proof_state_child_goal_limit: int = 3,
    proof_state_decl_application_limit: int = 6,
    proof_state_batch_parallelism: int = 1,
    formal_state_search_enabled: bool = False,
    formal_state_search_timeout_s: float = DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
    formal_state_search_operation_timeout_s: float = (
        DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S
    ),
    formal_state_search_provider_timeout_s: float = (
        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S
    ),
    formal_state_search_provider_max_tokens: int = (
        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS
    ),
    formal_state_search_provider_reasoning_effort: str = (
        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
    ),
    formal_state_search_provider_max_attempts: int = 2,
    formal_state_search_provider_retry_backoff_s: float = 5.0,
    formal_state_search_beam_width: int = 4,
    formal_state_search_max_steps: int = 8,
    formal_state_search_max_candidates: int = 6,
    formal_state_search_backtrack_limit: int = 8,
    formal_state_search_max_no_improvement_quanta: int = 6,
    falsification_enabled: bool = True,
    falsification_max_checks: int = 32,
    falsification_operation_timeout_s: float = (
        DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S
    ),
    falsification_engine_timeout_s: float = DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
    proof_state_cache_enabled: bool = False,
    proof_state_cache_path: Optional[Path] = None,
    root_tactic_prepass_enabled: bool = False,
    root_tactic_timeout_s: float = 40.0,
    root_tactic_max_candidates: int = 64,
    mini_recursive_enabled: bool = False,
    adaptive_recursive_on_stall: bool = False,
    mini_recursive_passes: int = 1,
    mini_recursive_max_claims: int = PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
    mini_recursive_turns_per_claim: int = 3,
    mini_recursive_tactic_timeout_s: float = 20.0,
    mini_recursive_tactic_max_candidates: int = 48,
    recursive_pass_budget_override: Optional[int] = None,
    adaptive_recursive_pass_budget_override: Optional[int] = None,
    llm_preamble_override: Optional[str] = None,
    lean_preamble_override: Optional[str] = None,
    initial_context: str = "",
    premise_block: str = "",
    premise_names: Sequence[str] = (),
    premise_retrieval_record: Optional[Dict[str, Any]] = None,
    premise_zero_hit_policy: str = "off",
    premise_zero_hit_suppress_library_first: bool = True,
    premise_zero_hit_max_local_turns: int = 1,
    premise_zero_hit_allow_api_grounding_after_lean_failure: bool = True,
    sample_temperature: Optional[float] = None,
    mini_phase_temperatures: Optional[Any] = None,
    proof_cache_override: Optional[MiniVerifiedLemmaCache] = None,
    session_scope: str = "problem",
    # Phase 2 (2026-05-09) — recursive helper prover.
    recursive_helper_prover_enabled: bool = False,
    recursive_helper_budget: int = 0,
    recursive_helper_max_depth: int = 3,
    recursive_helper_max_attempts_per_node: int = 2,
    recursive_helper_turns: int = 5,
    recursive_helper_refine: bool = False,
    # Fix 3 (2026-05-22) — strict-progress accounting feature flag.
    # When True, ``outcome.metadata["strong_progress"]`` is required for a
    # progress=True outcome to reset the stagnation counter; soft-only
    # progress accumulates a streak that ticks stagnation once saturated.
    # Drives recovery from the putnam_1978_b2 21-min swamp where bogus
    # contradiction-route helpers kept resetting stagnation.
    strict_progress_accounting: bool = False,
    soft_progress_streak_cap: int = 4,
    run_wall_clock_budget_s: float = 0.0,
    no_strong_progress_budget_s: float = 0.0,
    theory_library: Optional[Any] = None,
    theory_candidate_builder: Optional[Any] = None,
    theory_domain: str = "general mathematics",
    theory_bundle_ids: Sequence[str] = (),
    theory_default_imports: Sequence[str] = ("Mathlib",),
    theory_promote_verified_helpers: bool = False,
    graph_execution_projection_mode: Optional[str] = None,
    graph_execution_project_environment_hash: Optional[str] = None,
) -> MiniSession:
    """Build a ``MiniSession`` whose action registry mirrors legacy ordering.

    Action priority table follows plan §4. Frontier-first selection
    (``proof_state.work_frontier`` consultation) is wired in
    ``MiniSession.select_next_action`` itself; this factory only
    populates the static registry.
    """

    require_falsification_search_bound(
        falsification_max_checks,
        field="falsification_max_checks",
    )
    require_falsification_watchdog(
        falsification_operation_timeout_s,
        field="falsification_operation_timeout_s",
    )
    require_falsification_watchdog(
        falsification_engine_timeout_s,
        field="falsification_engine_timeout_s",
    )

    dossier_was_supplied = dossier is not None
    supplied_promotion_fingerprints = dict(
        getattr(
            dossier,
            "theory_promotion_durable_helper_fingerprints",
            {},
        )
        or {}
    )
    _validate_supplied_dossier_problem_identity(problem, dossier)

    _validate_cached_cost_budget_pricing(
        cost_controller=cost_controller,
        role_clients=(("prover", prover_client), ("refiner", refiner_client)),
    )

    # Direct factory callers receive the same production default as the public
    # prove_problem API.  The local import avoids a module import cycle; fake
    # Lean protocols remain untouched by the composition helper.
    from ..mini_prover import (
        _ensure_default_mathematical_retrieval_service,
        _external_theorem_support_roots,
        _lean_imports_from_text,
    )

    searcher = _ensure_default_mathematical_retrieval_service(
        searcher=searcher,
        lean=lean,
        theory_library=theory_library,
        enabled=bool(mathematical_retrieval_enabled),
        active_imports=_lean_imports_from_text(
            str(getattr(problem, "preamble", "") or ""),
            str(getattr(problem, "raw_text", "") or ""),
            str(lean_preamble_override or ""),
        ),
        project_roots=_external_theorem_support_roots(problem),
    )

    fork_retrieval = getattr(searcher, "fork_session_context", None)
    if callable(fork_retrieval):
        searcher = fork_retrieval()
    set_excluded_target = getattr(searcher, "set_excluded_target", None)
    if callable(set_excluded_target):
        set_excluded_target(
            declaration_names=(problem.theorem_name,),
            source_paths=(
                (getattr(problem, "path", ""),)
                if bool(getattr(problem, "exclude_entire_source_from_retrieval", False))
                else ()
            ),
        )

    problem_text = problem_docstring_text(problem)
    # Bind immutably at the session composition boundary. Reusing one builder
    # across concurrent programmatic sessions cannot redirect an in-flight call
    # to another run's meter.
    theory_candidate_builder = _bind_theory_candidate_builder(
        theory_candidate_builder,
        cost_controller,
    )
    if theory_library is not None and getattr(theory_library, "mode", "off") != "off":
        theory_library.activate_lean_runner(lean)
    supplied_projection_mode = (
        str(getattr(dossier, "graph_execution_projection_mode", "") or "")
        if dossier is not None
        else ""
    )
    supplied_projection_environment_hash = (
        str(
            getattr(
                dossier,
                "graph_execution_project_environment_hash",
                "",
            )
            or ""
        )
        if dossier is not None
        else ""
    )
    if dossier is None:
        dossier = ProofDossier(
            theorem_name=problem.theorem_name,
            root_statement=problem.statement_type,
            problem_text=problem_text,
        )
    else:
        # Adversarial-review fix #5 (2026-05-08): mirror legacy
        # ``sample_dossier`` isolation (mini_prover.py:5918-5934). When the
        # caller supplies a dossier, the session previously mutated it
        # directly — speculative graph nodes from failed attempts,
        # failed_attempts counters, and projection nodes from
        # ``sync_to_graph`` would persist in the caller's dossier even
        # after rollback or session failure. Clone the supplied dossier
        # into an isolated session-scoped workspace and seed the verified
        # helpers from the original. Callers that want to absorb wins
        # back into their dossier do so explicitly via
        # ``seed_verified_helpers`` (or similar) after the session
        # completes; the session itself never mutates state across the
        # isolation boundary.
        supplied = dossier
        dossier = _clone_dossier_for_session(supplied)
    dossier.opaque_mode = bool(opaque_mode)
    projection_mode = (
        str(
            graph_execution_projection_mode
            if graph_execution_projection_mode is not None
            else (supplied_projection_mode or "shadow")
        )
        .strip()
        .lower()
    )
    if projection_mode not in {"off", "shadow"}:
        raise ValueError("graph_execution_projection_mode must be 'off' or 'shadow'")
    dossier.graph_execution_projection_mode = projection_mode
    dossier.graph_execution_project_environment_hash = str(
        graph_execution_project_environment_hash
        if graph_execution_project_environment_hash is not None
        else supplied_projection_environment_hash
    )
    dossier.allow_official_answer_visibility = bool(allow_official_answer_visibility)

    # Proof cache mirrors legacy semantics.
    proof_cache_enabled = bool(proof_state_engine_enabled and proof_state_cache_enabled)
    proof_cache_base_path = (
        Path(proof_state_cache_path)
        if proof_state_cache_path is not None
        else MiniVerifiedLemmaCache.default_path()
    )
    proof_cache_run_id = f"{problem.theorem_name}.{uuid.uuid4().hex}"  # noqa: F841 — kept for symmetry with legacy
    proof_cache = (
        proof_cache_override
        if proof_cache_override is not None
        else _make_proof_state_cache(
            enabled=proof_cache_enabled,
            base_path=proof_cache_base_path,
            store_failure_metric_sink=dossier.increment_tool_metric,
        )
    )
    if proof_cache is not None:
        proof_cache.set_store_failure_metric_sink(dossier.increment_tool_metric)
    set_retrieval_metric_sink = getattr(searcher, "set_metric_sink", None)
    if callable(set_retrieval_metric_sink):
        set_retrieval_metric_sink(dossier.increment_tool_metric)

    # Recursive budget pools. Prepass and adaptive fallback are separate:
    # the fallback is a last-resort action and must not vanish simply because
    # an upfront recursive prepass spent its own allocation.
    configured_recursive_budget = max(0, int(mini_recursive_passes or 0))
    recursive_budget = (
        (
            max(0, int(recursive_pass_budget_override))
            if recursive_pass_budget_override is not None
            else configured_recursive_budget
        )
        if mini_recursive_enabled
        else 0
    )
    adaptive_recursive_budget = (
        (
            max(0, int(adaptive_recursive_pass_budget_override))
            if adaptive_recursive_pass_budget_override is not None
            else configured_recursive_budget
        )
        if adaptive_recursive_on_stall
        else 0
    )
    recursive_helper_invocation_budget = (
        (
            int(recursive_helper_budget)
            if int(recursive_helper_budget or 0) > 0
            else max(1, int(max_prove_turns or 1) * 2)
        )
        if recursive_helper_prover_enabled
        else 0
    )

    # Bound max_iterations by the configured action budgets plus headroom for
    # inter-turn assembly.
    max_iterations = (
        2  # premise retrieval + root tactic prepass
        + max(0, int(mini_recursive_passes or 0))
        + adaptive_recursive_budget
        + recursive_helper_invocation_budget
        + max(0, int(max_prove_turns or 0))
        + max(0, int(max_refine_turns or 0))
        + (1 if adaptive_recursive_on_stall else 0)
        + 5  # safety headroom
    )

    # Build the prove-role Conversation up front. M2 uses one conversation
    # for the whole session; the refine-role action (when registered)
    # mutates ``conv.role`` before invoking the typed conversation-turn
    # pipeline, mirroring the legacy transcript semantics.
    from ..mini_prover import (
        Conversation,
        _REPAIR_CONTINUATION,
        _format_lean_signature,
        _lean_checker_preamble_for_problem,
        _llm_visible_preamble_for_problem,
        _problem_has_official_answer_payload,
        _problem_uses_solution_placeholder_policy,
    )

    lean_signature = _format_lean_signature(problem)
    official_answer_payload_present = _problem_has_official_answer_payload(problem)
    dossier.official_answer_payload_present = bool(official_answer_payload_present)
    effective_placeholder_suppression = effective_solution_placeholder_suppression(
        suppress_solution_placeholders=(
            _problem_uses_solution_placeholder_policy(problem)
        ),
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    dossier.suppress_solution_placeholders = effective_placeholder_suppression
    llm_default_preamble = _llm_visible_preamble_for_problem(
        problem,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
    )
    llm_preamble = (
        str(llm_preamble_override)
        if llm_preamble_override is not None
        else llm_default_preamble
    )
    lean_preamble = (
        str(lean_preamble_override)
        if lean_preamble_override is not None
        else _lean_checker_preamble_for_problem(
            problem,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
        )
    )
    theory_context_pair = None
    if theory_library is not None and getattr(theory_library, "mode", "off") != "off":
        from ..mini_theory import TheoryContextPair

        theory_context_pair = TheoryContextPair.from_preambles(
            llm_preamble=llm_preamble,
            lean_preamble=lean_preamble,
        )
        if theory_bundle_ids:
            theory_context_pair = theory_library.select_context(
                theory_context_pair,
                bundle_ids=theory_bundle_ids,
            )
        # TheoryContext is the canonical parser/renderer for every theory-mode
        # preamble, including the empty-bundle base context.  Keep the
        # Conversation and retrieval surfaces byte-identical to the context
        # pair throughout the run; otherwise harmless trailing whitespace can
        # create incompatible request and verification identities.
        llm_preamble = theory_context_pair.llm.render()
        lean_preamble = theory_context_pair.lean.render()
    # The direct factory is a public composition boundary in its own right.
    # Stamp the exact checker environment here, after theory rendering, rather
    # than relying on ``prove_problem_via_session`` to have done it first.
    # Otherwise direct callers create graph/proof-state work with an empty
    # environment identity and later receipts cannot be compared safely.
    dossier.record_lean_environment(
        text_hash(lean_preamble),
        environment_source_text=lean_preamble,
    )
    searcher = _bind_answer_safe_retrieval_context(
        searcher,
        problem=problem,
        llm_preamble=llm_preamble,
        lean_preamble=lean_preamble,
    )
    if proof_cache is not None:
        set_verified_helper_cache = getattr(
            searcher,
            "set_verified_helper_cache",
            None,
        )
        if callable(set_verified_helper_cache):
            # Stamp helpers with the checker preamble hash recorded above.
            # Mathlib/project sources keep the Lake fingerprint; collapsing
            # those identities would alias distinct library and run keys.
            set_verified_helper_cache(
                proof_cache,
                environment_hash=str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ),
            )
    external_initial_context = str(initial_context or "").strip()
    external_premise_block = str(premise_block or "").strip()
    conv = Conversation(
        role="prove",
        goal_statement=problem.statement_type,
        problem_text=problem_text,
        lean_signature=lean_signature,
        preamble=llm_preamble,
        lean_preamble=lean_preamble,
        turn_budget=max_prove_turns,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
        suppress_solution_placeholders=effective_placeholder_suppression,
    )
    conv.known_premise_names = list(premise_names or ())
    if external_initial_context:
        conv.append_user(external_initial_context)
    if external_premise_block:
        conv.append_user(
            external_premise_block,
            repair_semantics=_REPAIR_CONTINUATION,
        )

    # Construct ``ProofSearchState`` and attach to the session
    # (closes the M2 deferral). Without this, ``MiniSession.select_next_action``
    # never enters the frontier-first branch (session.py:162 gates on
    # ``proof_state is not None``), and every frontier-mappable action
    # (``child_closure``, ``lemma_dag_decompose``, ``inter_turn_assembly``)
    # registers but stays unfireable. Inside ``ConversationTurnAction``,
    # proof-state-mediated recovery (``_run_pre_lean_lemma_dag_decomposition``,
    # child closures, salvaged-helper assembly) silently skips when
    # ``proof_state`` is None, leaving the session with only LLM-driven
    # conv_turn cycles. Mirrors legacy mini_prover.py:5935-5950.
    #
    # Adversarial-review fix (2026-05-08): single fence around the whole
    # block. The prior version wrapped only ``reconcile_with_dossier``
    # and ``sync_to_graph``, so:
    #   (a) ``from_graph(...)`` was OUTSIDE the guard — its failure
    #       would crash the session build despite the "defensive"
    #       wrapping suggesting otherwise.
    #   (b) ``reconcile_with_dossier`` raising MID-LOOP would leave the
    #       proof_state half-mutated, then ``sync_to_graph`` would run
    #       on that partial state and write inconsistencies to the
    #       graph.
    # Both are addressed by a single try/except that either produces a
    # fully-initialized proof_state OR falls back to None and emits a
    # recorder event so the failure is visible.
    proof_state: Optional[Any] = None
    proof_state_init_error: Optional[str] = None
    if proof_state_engine_enabled:
        from ..proof_state import ProofSearchState

        def publish_staged_projection(staged_dossier: ProofDossier) -> None:
            """Atomically publish the two fields owned by proof-state sync."""

            has_record = hasattr(staged_dossier, "proof_state_record")
            staged_record = (
                copy.deepcopy(getattr(staged_dossier, "proof_state_record") or {})
                if has_record
                else None
            )
            dossier.proof_graph = staged_dossier.proof_graph
            if has_record:
                dossier.proof_state_record = staged_record
            elif hasattr(dossier, "proof_state_record"):
                delattr(dossier, "proof_state_record")

        try:
            staged_dossier = _clone_dossier_for_session(dossier)
            candidate_state = ProofSearchState.from_graph(
                theorem_name=problem.theorem_name,
                root_statement=problem.statement_type,
                graph=staged_dossier.proof_graph,
                suppress_solution_placeholders=effective_placeholder_suppression,
                statement_environment_hash=str(
                    getattr(staged_dossier, "current_lean_environment_hash", "") or ""
                ).strip(),
            )
            candidate_state.reconcile_with_dossier(staged_dossier)
            candidate_state.sync_to_graph(
                staged_dossier,
                phase="proof_state_init",
                turn_index=0,
            )
            publish_staged_projection(staged_dossier)
            proof_state = candidate_state
        except Exception as exc:
            proof_state_init_error = f"{type(exc).__name__}: {exc}"
            if recorder is not None and hasattr(recorder, "record_turn"):
                try:
                    recorder.record_turn(
                        {
                            "phase": "session_init",
                            "verdict": "proof_state_init_failed",
                            "error": proof_state_init_error,
                        }
                    )
                except Exception:
                    pass
            try:
                recovery_dossier = _clone_dossier_for_session(dossier)
                projection_recovery = _clear_dossier_proof_state_projection(
                    recovery_dossier
                )
                recovery_state = ProofSearchState(
                    theorem_name=problem.theorem_name,
                    root_statement=problem.statement_type,
                    suppress_solution_placeholders=effective_placeholder_suppression,
                    statement_environment_hash=str(
                        getattr(
                            recovery_dossier,
                            "current_lean_environment_hash",
                            "",
                        )
                        or ""
                    ).strip(),
                )
                recovery_state.reconcile_with_dossier(recovery_dossier)
                recovery_state.sync_to_graph(
                    recovery_dossier,
                    phase="proof_state_init_recovered_fresh",
                    turn_index=0,
                )
                publish_staged_projection(recovery_dossier)
                proof_state = recovery_state
                if recorder is not None and hasattr(recorder, "record_turn"):
                    try:
                        recorder.record_turn(
                            {
                                "phase": "session_init",
                                "verdict": "proof_state_init_recovered_fresh",
                                "error": proof_state_init_error,
                                "graph_projection_recovery": projection_recovery,
                            }
                        )
                    except Exception:
                        pass
            except Exception as recovery_exc:
                proof_state = None
                if recorder is not None and hasattr(recorder, "record_turn"):
                    try:
                        recorder.record_turn(
                            {
                                "phase": "session_init",
                                "verdict": "proof_state_init_recovery_failed",
                                "error": proof_state_init_error,
                                "recovery_error": (
                                    f"{type(recovery_exc).__name__}: {recovery_exc}"
                                ),
                            }
                        )
                    except Exception:
                        pass

    session = MiniSession(
        problem=problem,
        dossier=dossier,
        proof_state=proof_state,
        proof_cache=proof_cache,
        conv=conv,
        lean=lean,
        prover_client=prover_client,
        refiner_client=refiner_client,
        searcher=searcher,
        recorder=recorder,
        cost_controller=cost_controller,
        trace_prefix=trace_prefix,
        max_iterations=max_iterations,
        recursive_pass_budget_remaining=recursive_budget,
        adaptive_recursive_pass_budget_remaining=adaptive_recursive_budget,
        scope=session_scope,
        planner_split_scheduler_owner=(
            session_scope in {"problem", "parallel_fanin_recursive"}
        ),
        strict_progress_accounting=bool(strict_progress_accounting),
        max_soft_progress_streak=max(0, int(soft_progress_streak_cap or 0)),
        run_wall_clock_budget_s=max(
            0.0,
            float(run_wall_clock_budget_s or 0.0),
        ),
        no_strong_progress_budget_s=max(
            0.0,
            float(no_strong_progress_budget_s or 0.0),
        ),
        premise_zero_hit_policy=str(premise_zero_hit_policy or "off"),
        premise_zero_hit_suppress_library_first=bool(
            premise_zero_hit_suppress_library_first
        ),
        premise_zero_hit_max_local_turns=max(
            0,
            int(premise_zero_hit_max_local_turns or 0),
        ),
        premise_zero_hit_allow_api_grounding_after_lean_failure=bool(
            premise_zero_hit_allow_api_grounding_after_lean_failure
        ),
        theory_library=theory_library,
        theory_candidate_builder=theory_candidate_builder,
        theory_context_pair=theory_context_pair,
        theory_domain=str(theory_domain or "general mathematics"),
        theory_default_imports=tuple(
            dict.fromkeys(
                str(item or "").strip()
                for item in theory_default_imports
                if str(item or "").strip()
            )
        )
        or ("Mathlib",),
        theory_imported_bundle_ids=(
            theory_context_pair.lean.bundle_ids
            if theory_context_pair is not None
            else ()
        ),
        theory_snapshot=(
            theory_library.snapshot(theory_context_pair.lean.bundle_ids)
            if theory_library is not None and theory_context_pair is not None
            else ()
        ),
    )
    # Optional stronger planner used by the recursive driver ONLY after a
    # degenerate (empty/unparseable) planning response; actions read it via
    # getattr so absence keeps existing behavior.
    session.planner_escalation_client = planner_escalation_client
    set_active_bundle_ids = getattr(searcher, "set_active_bundle_ids", None)
    if callable(set_active_bundle_ids):
        set_active_bundle_ids(session.theory_imported_bundle_ids)
    total_llm_turn_budget = max(0, int(max_prove_turns or 0)) + max(
        0,
        int(max_refine_turns or 0),
    )
    session.configure_no_applicable_recovery(total_llm_turn_budget)
    effective_compute_examples_tool_enabled = _effective_compute_examples_tool_enabled(
        compute_examples_tool_enabled,
        lean_check_tool_enabled=bool(lean_check_tool_enabled),
        try_lean_tool_enabled=bool(try_lean_tool_enabled),
        apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
        searcher=searcher,
    )
    if premise_retrieval_record:
        policy_metadata = session.observe_premise_retrieval_record(
            dict(premise_retrieval_record)
        )
        for metric_key in (
            "mini_premise_zero_hit_shadow_local_micro_theory",
            "mini_premise_zero_hit_local_micro_theory_activated",
        ):
            # Precomputed premise records are shared into sample sessions;
            # raw retrieval counters are recorded at the actual precompute
            # site so parallel samples do not multiply one search run.
            if (
                metric_key == "mini_premise_zero_hit_shadow_local_micro_theory"
                and policy_metadata.get("premise_zero_hit_shadow_recommendation")
            ):
                session._increment_dossier_metric(metric_key, 1)
            elif (
                metric_key == "mini_premise_zero_hit_local_micro_theory_activated"
                and policy_metadata.get("local_micro_theory_activated")
            ):
                session._increment_dossier_metric(metric_key, 1)

    # ---- Register actions in priority order. -------------------------
    # The order in ``session.actions`` doesn't strictly matter — the
    # session sorts by priority — but ordering by priority here makes
    # the registry self-documenting.

    if premise_retrieval_enabled and searcher is not None:
        session.register(
            PremiseRetrievalAction(top_k=int(premise_retrieval_top_k or 0))
        )
        session.set_budget(
            "premise_retrieval",
            # Retrieval and each Lean activation/recheck retain their own
            # watchdogs. Do not impose a smaller aggregate cap that can expire
            # after discovery but before the discovered premise is activated.
            ActionBudget(max_invocations=1, max_total_seconds=0.0),
        )

    if falsification_enabled:
        falsification_policy = FalsificationPolicy(
            max_candidates_per_engine=falsification_max_checks,
            max_finite_checks=falsification_max_checks,
            operation_timeout_s=falsification_operation_timeout_s,
            engine_timeout_s=falsification_engine_timeout_s,
        )
        session.register(FalsifyTargetAction(policy=falsification_policy))
        session.set_budget(
            "falsify_target",
            # One foreground veto quantum per skip key. Coverage continuation
            # is the idle lane below. -1 is not a mathematical cutoff.
            ActionBudget(max_invocations=-1, max_total_seconds=0.0),
        )
        session.register(FalsifyCoverageAction(policy=falsification_policy))
        session.set_budget(
            "falsify_coverage",
            # Resumable depth work. Never a session-wide finish line.
            ActionBudget(max_invocations=-1, max_total_seconds=0.0),
        )

    if theory_library is not None and getattr(theory_library, "mode", "off") != "off":
        session.register(DomainTheoryAction(stage="retrieve", id="domain_theory"))
        session.set_budget(
            "domain_theory",
            ActionBudget(
                max_invocations=max(1, min(4, int(max_prove_turns or 1))),
                max_total_seconds=0.0,
            ),
        )
        if getattr(theory_library, "mode", "off") == "build":
            session.register(
                DomainTheoryAction(
                    candidate_builder=theory_candidate_builder,
                    stage="build",
                    id="domain_theory_build",
                )
            )
            # NOTE: domain_theory_build runs under BUDGET_SCOPE="theory_need", so
            # set_budget() forces this budget's scope to "theory_need" and
            # ActionBudget.exhausted() then IGNORES max_total_seconds/max_invocations
            # as a session cap (exhaustion is delegated to the action's per-need
            # semantic guard). A session wall-clock cap here would be dead config.
            # Runaway theory builds are bounded instead by (1) the per-build
            # reasoning + output cap in mini_theory.builder and (2) the action's
            # per-need attempt guard (theory_attempted_need_ids + max_attempts_per_need).
            session.set_budget(
                "domain_theory_build",
                ActionBudget(
                    max_invocations=max(2, min(8, int(max_prove_turns or 1) * 2)),
                    max_total_seconds=0.0,
                ),
            )

    session.register(
        CastNormalizationAction(
            timeout_s=max(1.0, min(12.0, float(root_tactic_timeout_s or 12.0))),
            max_candidates=max(8, min(24, int(root_tactic_max_candidates or 16))),
        )
    )
    session.set_budget(
        "cast_normalization",
        ActionBudget(
            max_invocations=max(1, int(max_prove_turns or 1)),
            max_total_seconds=0.0,
        ),
    )
    session.register(
        FinsetReindexingAction(
            timeout_s=max(1.0, min(12.0, float(root_tactic_timeout_s or 12.0))),
            max_candidates=max(8, min(24, int(root_tactic_max_candidates or 18))),
        )
    )
    session.set_budget(
        "finset_reindexing",
        ActionBudget(
            max_invocations=max(1, int(max_prove_turns or 1)),
            max_total_seconds=0.0,
        ),
    )

    from ensemble_prover.mini_formal_state_search import FormalStateSearchConfig

    formal_search_config = FormalStateSearchConfig(
        enabled=bool(formal_state_search_enabled),
        total_timeout_s=float(formal_state_search_timeout_s or 0.0),
        operation_timeout_s=float(formal_state_search_operation_timeout_s or 0.0),
        provider_timeout_s=float(formal_state_search_provider_timeout_s or 0.0),
        provider_max_tokens=max(0, int(formal_state_search_provider_max_tokens or 0)),
        provider_reasoning_effort=str(
            formal_state_search_provider_reasoning_effort
            or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
        ),
        provider_max_attempts=max(
            1, int(formal_state_search_provider_max_attempts or 1)
        ),
        provider_retry_backoff_s=max(
            0.0, float(formal_state_search_provider_retry_backoff_s or 0.0)
        ),
        beam_width=max(1, int(formal_state_search_beam_width or 1)),
        max_steps=max(1, int(formal_state_search_max_steps or 1)),
        max_candidates_per_state=max(1, int(formal_state_search_max_candidates or 1)),
        backtrack_limit=max(0, int(formal_state_search_backtrack_limit or 0)),
        max_no_improvement_quanta=max(
            0, int(formal_state_search_max_no_improvement_quanta or 0)
        ),
    )

    if root_tactic_prepass_enabled or (
        formal_search_config.normalized().enabled and proof_state_engine_enabled
    ):
        session.register(
            RootTacticCloseAction(
                phase="root_tactic_prepass",
                timeout_s=float(root_tactic_timeout_s or 0.0),
                max_candidates=int(root_tactic_max_candidates or 0),
            )
        )
        session.set_budget(
            "tactic_close",
            ActionBudget(
                max_invocations=max(
                    2,
                    int(max_prove_turns or 0) + int(max_refine_turns or 0),
                ),
                max_total_seconds=60.0,
            ),
        )
    if proof_state_engine_enabled and formal_search_config.normalized().enabled:
        session.register(FormalStateSearchAction(config=formal_search_config))
        session.set_budget(
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
                max_aggregate_seconds=_formal_state_search_aggregate_seconds(
                    formal_search_config
                ),
            ),
        )

    recursive_prepass_budget = recursive_budget
    formal_callback_kwargs = {
        "proof_state_retrieval_enabled": bool(proof_state_retrieval_enabled),
        "formal_state_search_enabled": bool(formal_state_search_enabled),
        "formal_state_search_timeout_s": float(formal_state_search_timeout_s or 0.0),
        "formal_state_search_operation_timeout_s": float(
            formal_state_search_operation_timeout_s or 0.0
        ),
        "formal_state_search_provider_timeout_s": float(
            formal_state_search_provider_timeout_s or 0.0
        ),
        "formal_state_search_provider_max_tokens": max(
            0, int(formal_state_search_provider_max_tokens or 0)
        ),
        "formal_state_search_provider_reasoning_effort": str(
            formal_state_search_provider_reasoning_effort
            or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
        ),
        "formal_state_search_provider_max_attempts": max(
            1, int(formal_state_search_provider_max_attempts or 1)
        ),
        "formal_state_search_provider_retry_backoff_s": max(
            0.0, float(formal_state_search_provider_retry_backoff_s or 0.0)
        ),
        "formal_state_search_beam_width": int(formal_state_search_beam_width or 1),
        "formal_state_search_max_steps": int(formal_state_search_max_steps or 1),
        "formal_state_search_max_candidates": int(
            formal_state_search_max_candidates or 1
        ),
        "formal_state_search_backtrack_limit": int(
            formal_state_search_backtrack_limit or 0
        ),
        "formal_state_search_max_no_improvement_quanta": max(
            0, int(formal_state_search_max_no_improvement_quanta or 0)
        ),
    }
    graph_recursive_cfg = (
        _mini_recursive_config_from_params(
            mini_recursive_passes=int(mini_recursive_passes or 1),
            mini_recursive_max_claims=int(mini_recursive_max_claims or 1),
            mini_recursive_turns_per_claim=int(mini_recursive_turns_per_claim or 1),
            mini_recursive_tactic_timeout_s=float(
                mini_recursive_tactic_timeout_s or 0.0
            ),
            mini_recursive_tactic_max_candidates=int(
                mini_recursive_tactic_max_candidates or 0
            ),
            falsification_enabled=bool(falsification_enabled),
            falsification_max_checks=falsification_max_checks,
            falsification_operation_timeout_s=falsification_operation_timeout_s,
            falsification_engine_timeout_s=falsification_engine_timeout_s,
            mini_phase_temperatures=mini_phase_temperatures,
            sample_temperature=sample_temperature,
            planner_client=prover_client,
            refiner_client=refiner_client,
        )
        if configured_recursive_budget > 0
        else None
    )
    recursive_cfg = (
        graph_recursive_cfg
        if mini_recursive_enabled and recursive_prepass_budget > 0
        else None
    )

    if recursive_cfg is not None and recursive_prepass_budget > 0:
        session.register(
            RecursiveControllerAction(
                phase_label="[mini-recursive prepass]",
                config=recursive_cfg,
                run_conversation_fn=_bind_theory_parent_callback(
                    session, **formal_callback_kwargs
                ),
                max_tool_calls_per_turn=int(max_tool_calls_per_turn or 0),
                lean_check_tool_enabled=bool(lean_check_tool_enabled),
                try_lean_tool_enabled=bool(try_lean_tool_enabled),
                compute_examples_tool_enabled=effective_compute_examples_tool_enabled,
                apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
                raw_feedback=bool(raw_feedback),
                repair_retrieval_enabled=bool(repair_retrieval_enabled),
                repair_retrieval_top_k=int(repair_retrieval_top_k or 0),
                proof_state_child_tactics_enabled=bool(
                    proof_state_child_tactics_enabled
                ),
                proof_state_child_tactic_timeout_s=float(
                    proof_state_child_tactic_timeout_s or 0.0
                ),
                proof_state_child_tactic_max_candidates=int(
                    proof_state_child_tactic_max_candidates or 0
                ),
                root_tactic_timeout_s=float(root_tactic_timeout_s or 0.0),
                root_tactic_max_candidates=int(root_tactic_max_candidates or 0),
                proof_state_child_goal_limit=int(proof_state_child_goal_limit or 0),
                proof_state_decl_application_limit=int(
                    proof_state_decl_application_limit or 0
                ),
                proof_state_batch_parallelism=int(proof_state_batch_parallelism or 1),
            )
        )
        session.set_budget(
            "recursive_controller",
            ActionBudget(
                # The controller yields after each crash-safe recursive pass.
                # The explicit pass pool on the session is the mathematical
                # work budget; a one-shot action cap would strand the saved
                # pass frontier after its first quantum.
                max_invocations=-1,
                # Recursive controller calls retain provider/Lean watchdogs;
                # this session budget must not impose a cumulative wall clock
                # cutoff on persistent mathematical search.
                max_total_seconds=0.0,
            ),
        )

    if graph_recursive_cfg is not None:
        # Graph-native recursive decomposition for ``mine_missing_obligation``
        # and ``route_replan`` work items. Verified blocker (2026-05-18): the
        # mini-recursive failure path emits obligation/replan frontier items
        # that have no recursive-decomposition consumer in the default
        # pipeline — ``GraphNativeShortcutAction`` only matches against
        # already-verified helpers, and the conversation-turn fallback
        # re-invokes the same flat-LLM loop that just failed. This action
        # invokes ``run_mini_recursive_attempt`` on the obligation's smaller
        # statement and writes back via ``mark_obligation_proved_by_helper``.
        # Depth, cycle, and budget guards are inside the action.
        session.register(
            GraphRecursiveDecomposeAction(
                config=graph_recursive_cfg,
                run_conversation_fn=_bind_theory_parent_callback(
                    session, **formal_callback_kwargs
                ),
                max_tool_calls_per_turn=int(max_tool_calls_per_turn or 0),
                lean_check_tool_enabled=bool(lean_check_tool_enabled),
                try_lean_tool_enabled=bool(try_lean_tool_enabled),
                compute_examples_tool_enabled=effective_compute_examples_tool_enabled,
                apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
                raw_feedback=bool(raw_feedback),
                repair_retrieval_enabled=bool(repair_retrieval_enabled),
                repair_retrieval_top_k=int(repair_retrieval_top_k or 0),
                proof_state_child_tactics_enabled=bool(
                    proof_state_child_tactics_enabled
                ),
                proof_state_child_tactic_timeout_s=float(
                    proof_state_child_tactic_timeout_s or 0.0
                ),
                proof_state_child_tactic_max_candidates=int(
                    proof_state_child_tactic_max_candidates or 0
                ),
                root_tactic_timeout_s=float(root_tactic_timeout_s or 0.0),
                root_tactic_max_candidates=int(root_tactic_max_candidates or 0),
                proof_state_child_goal_limit=int(proof_state_child_goal_limit or 0),
                proof_state_decl_application_limit=int(
                    proof_state_decl_application_limit or 0
                ),
                proof_state_batch_parallelism=int(proof_state_batch_parallelism or 1),
            )
        )
        session.set_budget(
            "graph_recursive_decompose",
            ActionBudget(
                max_invocations=GraphRecursiveDecomposeAction.DEFAULT_MAX_INVOCATIONS,
                # This action runs bounded mini-recursive sub-passes. Its own
                # invocation/depth/internal-turn caps are the contract; a
                # session-level wall-clock cap exhausted the structural path
                # after one long but useful obligation pass and forced flat
                # LLM fallback on the remaining replans.
                max_total_seconds=0.0,
            ),
        )

    if not proof_state_child_tactics_enabled and (
        recursive_cfg is not None
        or graph_recursive_cfg is not None
        or (adaptive_recursive_on_stall and adaptive_recursive_budget > 0)
    ):
        session.register(
            GraphRouteAssemblyAction(
                max_routes=max(1, int(proof_state_child_goal_limit or 0)),
                root_tactic_timeout_s=float(root_tactic_timeout_s or 0.0),
                root_tactic_max_candidates=int(root_tactic_max_candidates or 0),
            )
        )
        session.set_budget(
            "graph_route_assembly",
            ActionBudget(
                max_invocations=10,
                max_total_seconds=_route_assembly_budget_seconds(
                    timeout_s=float(root_tactic_timeout_s or 0.0),
                    max_invocations=10,
                ),
            ),
        )
        session.register(GraphNativeShortcutAction())
        session.set_budget(
            "graph_native_shortcut",
            ActionBudget(max_invocations=20, max_total_seconds=30.0),
        )

    if adaptive_recursive_on_stall and adaptive_recursive_budget > 0:
        fallback_cfg = _mini_recursive_config_from_params(
            mini_recursive_passes=int(mini_recursive_passes or 1),
            mini_recursive_max_claims=int(mini_recursive_max_claims or 1),
            mini_recursive_turns_per_claim=int(mini_recursive_turns_per_claim or 1),
            mini_recursive_tactic_timeout_s=float(
                mini_recursive_tactic_timeout_s or 0.0
            ),
            mini_recursive_tactic_max_candidates=int(
                mini_recursive_tactic_max_candidates or 0
            ),
            falsification_enabled=bool(falsification_enabled),
            falsification_max_checks=falsification_max_checks,
            falsification_operation_timeout_s=falsification_operation_timeout_s,
            falsification_engine_timeout_s=falsification_engine_timeout_s,
            mini_phase_temperatures=mini_phase_temperatures,
            sample_temperature=sample_temperature,
            planner_client=prover_client,
            refiner_client=refiner_client,
        )
        session.register(
            RecursiveControllerAction(
                action_id="adaptive_recursive_fallback",
                priority=80,
                phase_label="[recursive fallback after prove stall]",
                config=fallback_cfg,
                run_conversation_fn=_bind_theory_parent_callback(
                    session, **formal_callback_kwargs
                ),
                max_tool_calls_per_turn=int(max_tool_calls_per_turn or 0),
                lean_check_tool_enabled=bool(lean_check_tool_enabled),
                try_lean_tool_enabled=bool(try_lean_tool_enabled),
                compute_examples_tool_enabled=effective_compute_examples_tool_enabled,
                apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
                raw_feedback=bool(raw_feedback),
                repair_retrieval_enabled=bool(repair_retrieval_enabled),
                repair_retrieval_top_k=int(repair_retrieval_top_k or 0),
                proof_state_child_tactics_enabled=bool(
                    proof_state_child_tactics_enabled
                ),
                proof_state_child_tactic_timeout_s=float(
                    proof_state_child_tactic_timeout_s or 0.0
                ),
                proof_state_child_tactic_max_candidates=int(
                    proof_state_child_tactic_max_candidates or 0
                ),
                root_tactic_timeout_s=float(root_tactic_timeout_s or 0.0),
                root_tactic_max_candidates=int(root_tactic_max_candidates or 0),
                proof_state_child_goal_limit=int(proof_state_child_goal_limit or 0),
                proof_state_decl_application_limit=int(
                    proof_state_decl_application_limit or 0
                ),
                proof_state_batch_parallelism=int(proof_state_batch_parallelism or 1),
                budget_attr="adaptive_recursive_pass_budget_remaining",
            )
        )
        session.set_budget(
            "adaptive_recursive_fallback",
            ActionBudget(
                # As above, the dedicated adaptive pass pool bounds this
                # multi-quantum action.
                max_invocations=-1,
                max_total_seconds=0.0,
            ),
        )
        session.fallback_action_ids.add("adaptive_recursive_fallback")

    # ---- M4 subactions ----------------------------------------------
    # Register helper-only-salvage / inter-turn assembly actions BEFORE
    # ConversationTurnAction so the host action can dispatch them via
    # ``session.dispatch_subaction`` and the outer loop's frontier-first
    # selector can also schedule them directly between turns when
    # ``proof_state.work_frontier()`` reports actionable work.
    #
    # Post-Lean failure handling has exactly one owner: ConversationTurnAction
    # runs the cascade inline after a rejected Lean check and charges the
    # ``post_lean_failure`` budget bucket below. Keeping a schedulable
    # PostLeanFailureAction registered here let stale ``last_lean_verdict``
    # state re-run a cascade; the action class remains importable for direct
    # replay/unit tests, but is not part of the normal scheduler registry.
    if proof_state_child_tactics_enabled:
        session.register(
            InterTurnAssemblyAction(
                timeout_s=float(proof_state_child_tactic_timeout_s or 0.0),
                max_nodes=max(1, int(proof_state_child_goal_limit or 0)),
            )
        )
        session.set_budget(
            "inter_turn_assembly",
            ActionBudget(max_invocations=10, max_total_seconds=90.0),
        )
        session.register(
            GraphRouteAssemblyAction(
                max_routes=max(1, int(proof_state_child_goal_limit or 0)),
                root_tactic_timeout_s=float(root_tactic_timeout_s or 0.0),
                root_tactic_max_candidates=int(root_tactic_max_candidates or 0),
            )
        )
        session.set_budget(
            "graph_route_assembly",
            ActionBudget(
                max_invocations=10,
                max_total_seconds=_route_assembly_budget_seconds(
                    timeout_s=float(root_tactic_timeout_s or 0.0),
                    max_invocations=10,
                ),
            ),
        )
        session.register(GraphNativeShortcutAction())
        session.set_budget(
            "graph_native_shortcut",
            ActionBudget(max_invocations=20, max_total_seconds=30.0),
        )
        session.register(
            HelperOnlySalvageAction(
                timeout_s=float(proof_state_child_tactic_timeout_s or 0.0),
                max_nodes=int(proof_state_child_goal_limit or 0),
                batch_parallelism=int(proof_state_batch_parallelism or 1),
            )
        )
        session.set_budget(
            "helper_only_salvage",
            ActionBudget(
                max_invocations=max(1, int(max_prove_turns or 1)),
                max_total_seconds=120.0,
            ),
        )
        session.set_budget(
            "post_lean_failure",
            ActionBudget(
                max_invocations=max(
                    1, int(max_prove_turns or 1) + int(max_refine_turns or 0)
                ),
                max_total_seconds=300.0,
            ),
        )
        # Frontier-mappable workhorses also registered for the outer
        # loop's _map_work_item_to_action: ProofStateRetrievalAction,
        # ChildClosureAction, and
        # LemmaDagDecomposeAction. M2 already registers them implicitly
        # via the cascade; M4 makes them explicit on the session so the
        # frontier-first selector can dispatch them.
        # ``proof_state_retrieval`` precedes root repair in the scheduler's
        # static prepass set, so it is opt-in: ``repair_retrieval_enabled``
        # stays free to govern in-turn LLM retrieval on its own.
        if (
            proof_state_retrieval_enabled
            and repair_retrieval_enabled
            and int(repair_retrieval_top_k or 0) > 0
        ):
            session.register(
                ProofStateRetrievalAction(
                    max_nodes=int(proof_state_child_goal_limit or 0),
                    max_results=int(repair_retrieval_top_k or 0),
                )
            )
            session.set_budget(
                "proof_state_retrieval",
                ActionBudget(
                    max_invocations=max(1, int(max_prove_turns or 1)),
                    max_total_seconds=60.0,
                ),
            )
        child_closure_action = ChildClosureAction(
            timeout_s=float(proof_state_child_tactic_timeout_s or 0.0),
            max_candidates=int(proof_state_child_tactic_max_candidates or 0),
            max_nodes=int(proof_state_child_goal_limit or 0),
            max_decl_applications=int(proof_state_decl_application_limit or 0),
            batch_parallelism=int(proof_state_batch_parallelism or 1),
            formal_search_config=None,
        )
        session.register(child_closure_action)
        session.set_budget(
            "child_closure",
            ActionBudget(
                max_invocations=max(
                    child_closure_action.minimum_invocation_budget(),
                    int(max_prove_turns or 1),
                ),
                # Invocation/iteration bounds govern this lane. A cumulative
                # wall-clock cap can strand a paid parent stub when its typed
                # residual replay legitimately needs the verifier's 300s
                # operation quantum, especially with a small tactic timeout.
                max_total_seconds=0.0,
            ),
        )
        session.register(
            LemmaDagDecomposeAction(
                timeout_s=float(proof_state_child_tactic_timeout_s or 0.0),
                max_parent_stub_goals=int(proof_state_child_goal_limit or 0),
                root_tactic_max_candidates=int(
                    proof_state_child_tactic_max_candidates or 0
                ),
            )
        )
        session.set_budget(
            "lemma_dag_decompose",
            ActionBudget(
                max_invocations=max(1, int(max_prove_turns or 1)),
                # Parent-stub decomposition can hand off to the mandatory
                # 300-second typed-residual verifier. An unrelated 120-second
                # cumulative action cap used to cancel that hard operation
                # before it could publish its receipt. Invocation count bounds
                # this lane; verifier operations retain their own generous,
                # recoverable deadlines.
                max_total_seconds=0.0,
            ),
        )

    # Phase 2 (2026-05-09): RecursiveHelperProverAction. Registered when
    # the caller opts in; the CLI operational profile now supplies that opt-in
    # by default. Priority 35 — before conv_turn=50.
    # Depth bound enforced by the action's is_applicable + the
    # session.recursion_depth field.
    if recursive_helper_prover_enabled and proof_state_engine_enabled:
        session.register(
            RecursiveHelperProverAction(
                max_attempts_per_node=int(
                    recursive_helper_max_attempts_per_node
                    if recursive_helper_max_attempts_per_node is not None
                    else 2
                ),
                helper_turns=int(recursive_helper_turns or 5),
                refine_enabled=bool(recursive_helper_refine),
            )
        )
        budget_invocations = recursive_helper_invocation_budget
        session.set_budget(
            "recursive_helper_prover",
            ActionBudget(
                max_invocations=budget_invocations,
                max_total_seconds=0.0,
            ),
        )
        # Phase 2: propagate the depth cap to the session so the
        # give-up nudge fires the depth-aware framing in child
        # sessions.
        raw_max_depth = recursive_helper_max_depth
        session.max_recursion_depth = max(
            0,
            int(raw_max_depth if raw_max_depth is not None else 3),
        )

    # Conversation prove — the workhorse.
    # CRITICAL: pass ``max_turns_for_budget=max_prove_turns`` so the
    # post-failure cascade's budget footer reads "Turn N of {prove_turns}".
    # When the factory omits this, the action's default is 1, the LLM
    # sees "Turn 2 of 1" → "0 turns remain" → gives up at turn 2.
    # Bug surfaced on putnam_1998_b1 run at 23:08 — LLM said
    # "I can't submit another Lean attempt because the turn budget is
    # exhausted (0 turns remain)" after only one rejection.
    session.register(
        ConversationTurnAction(
            role="prove",
            client=prover_client,
            sample_temperature=sample_temperature,
            mini_phase_temperatures=mini_phase_temperatures,
            searcher_override=searcher,
            lean_check_tool_enabled=bool(lean_check_tool_enabled),
            try_lean_tool_enabled=bool(try_lean_tool_enabled),
            compute_examples_tool_enabled=effective_compute_examples_tool_enabled,
            apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
            max_tool_calls_per_turn=int(max_tool_calls_per_turn or 0),
            raw_feedback=bool(raw_feedback),
            repair_retrieval_enabled=bool(repair_retrieval_enabled),
            repair_retrieval_top_k=int(repair_retrieval_top_k or 0),
            proof_state_child_tactics_enabled=bool(proof_state_child_tactics_enabled),
            proof_state_child_tactic_timeout_s=float(
                proof_state_child_tactic_timeout_s or 0.0
            ),
            proof_state_child_tactic_max_candidates=int(
                proof_state_child_tactic_max_candidates or 0
            ),
            proof_state_child_goal_limit=int(proof_state_child_goal_limit or 0),
            proof_state_decl_application_limit=int(
                proof_state_decl_application_limit or 0
            ),
            proof_state_batch_parallelism=int(proof_state_batch_parallelism or 1),
            max_turns_for_budget=max(1, int(max_prove_turns or 1)),
            llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(prover_client),
            formalization_llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(
                prover_client
            ),
        )
    )
    session.set_budget(
        "conversation_turn_prove",
        ActionBudget(
            max_invocations=max(0, int(max_prove_turns or 0)),
            # Conversation turn budgets are count-based CLI contracts.
            # A slow model call should consume one turn, not silently burn
            # several turns' worth of aggregate wall-clock budget. Per-call
            # prover/refiner timeouts still bound individual LLM requests.
            max_total_seconds=0.0,
        ),
    )

    if refiner_client is not None and int(max_refine_turns or 0) > 0:
        session.register(
            ConversationTurnAction(
                role="refine",
                client=refiner_client,
                sample_temperature=sample_temperature,
                mini_phase_temperatures=mini_phase_temperatures,
                searcher_override=searcher,
                lean_check_tool_enabled=bool(lean_check_tool_enabled),
                try_lean_tool_enabled=bool(try_lean_tool_enabled),
                compute_examples_tool_enabled=effective_compute_examples_tool_enabled,
                apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
                max_tool_calls_per_turn=int(max_tool_calls_per_turn or 0),
                raw_feedback=bool(raw_feedback),
                repair_retrieval_enabled=bool(repair_retrieval_enabled),
                repair_retrieval_top_k=int(repair_retrieval_top_k or 0),
                proof_state_child_tactics_enabled=bool(
                    proof_state_child_tactics_enabled
                ),
                proof_state_child_tactic_timeout_s=float(
                    proof_state_child_tactic_timeout_s or 0.0
                ),
                proof_state_child_tactic_max_candidates=int(
                    proof_state_child_tactic_max_candidates or 0
                ),
                proof_state_child_goal_limit=int(proof_state_child_goal_limit or 0),
                proof_state_decl_application_limit=int(
                    proof_state_decl_application_limit or 0
                ),
                proof_state_batch_parallelism=int(proof_state_batch_parallelism or 1),
                max_turns_for_budget=max(1, int(max_refine_turns or 1)),
                llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(refiner_client),
                formalization_llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(
                    refiner_client
                ),
            )
        )
        # ``ConversationTurnAction`` uses role-suffixed id, so prove and
        # refine have distinct budgets.
        session.set_budget(
            "conversation_turn_refine",
            ActionBudget(
                max_invocations=int(max_refine_turns or 0),
                # Same count-based contract as prove turns; see above.
                max_total_seconds=0.0,
            ),
        )

    session.theory_promote_verified_helpers = bool(theory_promote_verified_helpers)
    if _session_theory_promotion_enabled(session):
        # Keep runtime capabilities on MiniSession, never on ProofDossier.
        # Hard-deadline conversation work deep-copies dossiers; capturing the
        # library's RLock there would make every workspace clone fail.
        session.theory_verified_helper_accept_callback = partial(
            _stage_session_verified_helper,
            session,
        )
        from ..proof_state_executor import register_verified_helper_accept_session

        register_verified_helper_accept_session(session.dossier, session)
        session.theory_verified_helper_reconcile_callback = partial(
            _stage_all_session_verified_helpers,
            session,
        )
        if dossier_was_supplied:
            # A supplied dossier has no implicit durability contract. Stage
            # its existing verified helpers now so a crash before the first
            # action cannot strand them.
            _initialize_promotion_helper_baseline(
                session,
                durable_parent_fingerprints=supplied_promotion_fingerprints,
            )
            _stage_all_session_verified_helpers(session, force=True)
    session.expand_max_iterations_to_action_budgets(headroom=5)
    return session


def _is_complex_for_m2(
    *,
    problem: TheoremProblem,
    parallel_samples: int,
    opaque_mode: bool,
) -> Tuple[bool, str]:
    """Historical M2 detector retained for compatibility with old tests/tools.

    M5 no longer uses this to delegate; container cases are handled by
    ``prove_problem_via_session`` below.
    """

    if int(parallel_samples or 0) > 1:
        return True, "parallel_samples_gt_one"
    return False, ""


async def prove_problem_via_session(
    **kwargs: Any,
) -> Tuple[bool, Optional[str]]:
    """Drive ``prove_problem`` through ``MiniSession``.

    Parallel samples create isolated child sessions, then copy the winning
    dossier back to the caller.  When verified-helper promotion is enabled,
    accepted helpers are durably staged here but never compiled on the proof
    result path.  Direct callers should invoke
    ``run_verified_helper_promotion_maintenance(theory_library)`` only after
    they have committed the proof outcome.
    """
    retired_options = sorted(
        {
            "use_mini_session",
            "direct_root_author_enabled",
            "startup_root_fast_lane_author_timeout_s",
            "startup_root_fast_lane_author_max_tokens",
            "startup_root_fast_lane_author_max_tool_calls",
        }.intersection(kwargs)
    )
    if retired_options:
        joined = ", ".join(retired_options)
        raise TypeError(
            f"prove_problem_via_session() received retired option(s): {joined}"
        )

    # This function is also a public direct entry point.  Do not rely on the
    # outer ``prove_problem`` selector or the later session builder to validate
    # these values: theory-builder binding, retrieval construction, ready
    # callbacks, and startup proof lanes all occur before session assembly and
    # some can return successfully without ever reaching it.
    require_falsification_search_bound(
        kwargs.get("falsification_max_checks", 32),
        field="falsification_max_checks",
    )
    require_falsification_watchdog(
        kwargs.get(
            "falsification_operation_timeout_s",
            DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
        ),
        field="falsification_operation_timeout_s",
    )
    require_falsification_watchdog(
        kwargs.get(
            "falsification_engine_timeout_s",
            DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
        ),
        field="falsification_engine_timeout_s",
    )
    worker_ready_callback = kwargs.pop("worker_ready_callback", None)
    worker_ready_signaled = False

    def _signal_worker_ready_once() -> None:
        nonlocal worker_ready_signaled
        if worker_ready_signaled or not callable(worker_ready_callback):
            return
        worker_ready_callback()
        worker_ready_signaled = True

    problem = kwargs.get("problem")
    if problem is None:
        raise TypeError("prove_problem_via_session requires problem")
    _validate_supplied_dossier_problem_identity(problem, kwargs.get("dossier"))
    sample_count = max(1, int(kwargs.get("parallel_samples", 1) or 1))

    # Bind once for the entire container, including post-sample MiniRecursive
    # controllers and child sessions that read the outer kwargs directly.
    # This intentionally follows structural argument validation: a custom
    # builder binder may allocate resources and must not run for a rejected
    # persistent-parallel shape.
    kwargs["theory_candidate_builder"] = _bind_theory_candidate_builder(
        kwargs.get("theory_candidate_builder"),
        kwargs.get("cost_controller"),
    )

    from ..mini_prover import (
        Conversation,
        _PARALLEL_SAMPLE_CANCEL_DRAIN_TIMEOUT_S,
        _REPAIR_CONTINUATION,
        _ensure_default_mathematical_retrieval_service,
        _external_theorem_support_roots,
        _format_lean_signature,
        _lean_checker_preamble_for_problem,
        _lean_imports_from_text,
        _record_visible_answer_active_root_targets,
        _try_root_tactic_close,
        _trace,
        _llm_visible_preamble_for_problem,
        _official_answer_visible_to_llm,
        _problem_has_official_answer_payload,
        _problem_uses_solution_placeholder_policy,
    )
    from ..mini_recursive import (
        MiniRecursiveConfig,
        production_planner_deliberation_default,
        run_mini_recursive_attempt,
    )
    from ..premise_retrieval import (
        format_premise_block,
        record_premise_retrieval_metrics,
    )

    prover_client = kwargs.get("prover_client")
    lean = kwargs.get("lean")
    recorder = kwargs.get("recorder")
    searcher = kwargs.get("searcher")
    from ..mathematical_retrieval.async_runtime import run_sync_abandonment_safe

    searcher = await run_sync_abandonment_safe(
        lambda: _ensure_default_mathematical_retrieval_service(
            searcher=searcher,
            lean=lean,
            theory_library=kwargs.get("theory_library"),
            enabled=bool(kwargs.get("mathematical_retrieval_enabled", True)),
            active_imports=_lean_imports_from_text(
                str(getattr(problem, "preamble", "") or ""),
                str(getattr(problem, "raw_text", "") or ""),
                str(kwargs.get("lean_preamble_override") or ""),
            ),
            project_roots=_external_theorem_support_roots(problem),
        ),
        timeout_s=float("inf"),
    )
    kwargs["searcher"] = searcher
    fork_retrieval = getattr(searcher, "fork_session_context", None)
    if callable(fork_retrieval):
        searcher = fork_retrieval()
        kwargs["searcher"] = searcher
    set_excluded_target = getattr(searcher, "set_excluded_target", None)
    if callable(set_excluded_target):
        set_excluded_target(
            declaration_names=(problem.theorem_name,),
            source_paths=(
                (getattr(problem, "path", ""),)
                if bool(getattr(problem, "exclude_entire_source_from_retrieval", False))
                else ()
            ),
        )
    trace_prefix = str(kwargs.get("trace_prefix") or "")
    opaque_mode = bool(kwargs.get("opaque_mode", True))
    allow_official_answer_visibility = bool(
        kwargs.get("allow_official_answer_visibility", False)
    )
    premise_retrieval_enabled = bool(kwargs.get("premise_retrieval_enabled", False))
    premise_retrieval_top_k = int(
        kwargs.get("premise_retrieval_top_k", PREMISE_DEFAULT_TOP_K) or 0
    )
    premise_zero_hit_policy = str(kwargs.get("premise_zero_hit_policy", "off") or "off")
    premise_zero_hit_suppress_library_first = bool(
        kwargs.get("premise_zero_hit_suppress_library_first", True)
    )
    premise_zero_hit_max_local_turns = int(
        kwargs.get("premise_zero_hit_max_local_turns", 1) or 0
    )
    premise_zero_hit_allow_api_grounding_after_lean_failure = bool(
        kwargs.get("premise_zero_hit_allow_api_grounding_after_lean_failure", True)
    )
    proof_state_engine_enabled = bool(kwargs.get("proof_state_engine_enabled", True))
    compute_examples_enabled_for_kwargs = _kwargs_compute_examples_tool_enabled(
        dict(kwargs),
        searcher=searcher,
    )
    proof_state_cache_enabled = bool(kwargs.get("proof_state_cache_enabled", False))
    proof_cache_enabled = bool(proof_state_engine_enabled and proof_state_cache_enabled)
    proof_cache_base_path = (
        Path(kwargs.get("proof_state_cache_path"))
        if kwargs.get("proof_state_cache_path") is not None
        else MiniVerifiedLemmaCache.default_path()
    )
    proof_cache_run_id = f"{problem.theorem_name}.{uuid.uuid4().hex}"
    shared_proof_cache = _make_proof_state_cache(
        enabled=proof_cache_enabled,
        base_path=proof_cache_base_path,
    )
    recursive_pass_budget_remaining = (
        max(
            0,
            int(kwargs.get("mini_recursive_passes", 1) or 0),
        )
        if bool(kwargs.get("mini_recursive_enabled", False))
        else 0
    )
    adaptive_recursive_pass_budget_remaining = (
        max(0, int(kwargs.get("mini_recursive_passes", 1) or 0))
        if bool(kwargs.get("adaptive_recursive_on_stall", False))
        else 0
    )

    problem_text = problem_docstring_text(problem)
    lean_signature = _format_lean_signature(problem)
    llm_default_preamble = _llm_visible_preamble_for_problem(
        problem,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
    )
    llm_preamble = (
        str(kwargs.get("llm_preamble_override"))
        if kwargs.get("llm_preamble_override") is not None
        else llm_default_preamble
    )
    lean_preamble = (
        str(kwargs.get("lean_preamble_override"))
        if kwargs.get("lean_preamble_override") is not None
        else _lean_checker_preamble_for_problem(
            problem,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
        )
    )
    theory_library = kwargs.get("theory_library")
    container_theory_context = None
    if theory_library is not None and getattr(theory_library, "mode", "off") != "off":
        from ..mini_theory import TheoryContextPair

        theory_library.activate_lean_runner(lean)
        container_theory_context = TheoryContextPair.from_preambles(
            llm_preamble=llm_preamble,
            lean_preamble=lean_preamble,
        )
        explicit_bundle_ids = tuple(kwargs.get("theory_bundle_ids") or ())
        if explicit_bundle_ids:
            container_theory_context = theory_library.select_context(
                container_theory_context,
                bundle_ids=explicit_bundle_ids,
            )
        llm_preamble = container_theory_context.llm.render()
        lean_preamble = container_theory_context.lean.render()
    searcher = _bind_answer_safe_retrieval_context(
        searcher,
        problem=problem,
        llm_preamble=llm_preamble,
        lean_preamble=lean_preamble,
    )
    kwargs["searcher"] = searcher
    dossier = kwargs.get("dossier")
    if dossier is None:
        dossier = ProofDossier(
            theorem_name=problem.theorem_name,
            root_statement=problem.statement_type,
            problem_text=problem_text,
        )
    dossier.opaque_mode = bool(opaque_mode)
    dossier.allow_official_answer_visibility = bool(allow_official_answer_visibility)
    dossier.record_lean_environment(
        text_hash(lean_preamble),
        environment_source_text=lean_preamble,
    )
    kwargs["dossier"] = dossier

    official_answer_payload_present = _problem_has_official_answer_payload(problem)
    dossier.official_answer_payload_present = bool(official_answer_payload_present)
    effective_placeholder_suppression = effective_solution_placeholder_suppression(
        suppress_solution_placeholders=(
            _problem_uses_solution_placeholder_policy(problem)
        ),
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    dossier.suppress_solution_placeholders = effective_placeholder_suppression
    official_answer_visible = _official_answer_visible_to_llm(
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )
    if official_answer_visible:
        _trace(
            trace_prefix,
            "=== visible-answer mode: LLM-facing preamble uses filled "
            "PutnamBench solution definitions ===",
        )
        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(
                {
                    "phase": "answer_visibility",
                    "opaque_mode": False,
                    "allow_official_answer_visibility": True,
                    "official_answer_payload_present": True,
                    "verdict": "official_answer_visible_to_llm",
                }
            )
    elif allow_official_answer_visibility and not official_answer_payload_present:
        _trace(
            trace_prefix,
            "=== visible-answer mode requested but no official answer payload "
            "is present; using ordinary proof-development prompt ===",
        )
        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(
                {
                    "phase": "answer_visibility",
                    "opaque_mode": bool(opaque_mode),
                    "allow_official_answer_visibility": bool(
                        allow_official_answer_visibility
                    ),
                    "official_answer_payload_present": False,
                    "reason": "official_answer_visibility_not_applicable",
                    "verdict": "official_answer_not_applicable",
                }
            )
    elif recorder is not None and hasattr(recorder, "record_turn"):
        recorder.record_turn(
            {
                "phase": "answer_visibility",
                "opaque_mode": bool(opaque_mode),
                "allow_official_answer_visibility": bool(
                    allow_official_answer_visibility
                ),
                "official_answer_payload_present": bool(
                    official_answer_payload_present
                ),
                "reason": (
                    "opaque_mode"
                    if opaque_mode
                    else "official_answer_visibility_not_allowed"
                ),
                "verdict": "official_answer_hidden_from_llm",
            }
        )
    visible_answer_root_receipt: Dict[str, Any] = {}
    await _record_visible_answer_active_root_targets(
        dossier=dossier,
        lean=lean,
        root_statement=problem.statement_type,
        preamble=llm_preamble,
        official_answer_visible=official_answer_visible,
        timeout_s=float(kwargs.get("mini_recursive_tactic_timeout_s", 20.0) or 0.0),
        recorder=recorder,
        trace_prefix=trace_prefix,
        accepted_root_proof_out=visible_answer_root_receipt,
    )
    visible_answer_root_proof = str(
        visible_answer_root_receipt.get("proof") or ""
    ).strip()
    if visible_answer_root_proof:
        dossier.mark_solved(
            visible_answer_root_proof,
            replay_helpers=dossier.verified_helper_blocks(),
            root_certificate_metadata={
                "phase": "visible_answer_active_target",
                "source": "kernel_accepted_simplification_probe",
                "solution_names": list(
                    visible_answer_root_receipt.get("solution_names") or ()
                ),
            },
        )
        dossier.increment_tool_metric(
            "mini_visible_answer_probe_root_solved",
            1,
        )
        _signal_worker_ready_once()
        return True, visible_answer_root_proof
    premise_goal_statement = (
        active_root_target_statement(
            dossier,
            require_single=True,
            require_no_hypotheses=False,
            include_hypotheses=True,
        )
        or problem.statement_type
    )

    async def _retrieve_startup_premise_context(
        *,
        target_dossier: ProofDossier,
        target_searcher: Any,
        goal_statement: str,
        event_recorder: Any,
        event_trace_prefix: str,
    ) -> Tuple[str, List[str], Dict[str, Any]]:
        """Compute advisory premises for one freshly constructed environment."""

        if not premise_retrieval_enabled or target_searcher is None:
            return "", [], {}
        try:
            from ensemble_prover.premise_retrieval import (
                retrieve_premise_record_async,
            )

            premise_record = await retrieve_premise_record_async(
                target_searcher,
                goal_statement=goal_statement,
                exploration=None,
                top_k=premise_retrieval_top_k,
                timeout_s=float(
                    getattr(target_searcher, "operation_timeout_s", 30.0) or 30.0
                ),
            )
            record = premise_record.metadata()
            record_premise_retrieval_metrics(
                getattr(target_dossier, "increment_tool_metric", None),
                record,
            )
            premises = list(premise_record.hits or ())
            names = [premise.name for premise in premises if premise.name]
            block = format_premise_block(premises)
            if block:
                _trace(
                    event_trace_prefix,
                    f"=== premise retrieval {problem.theorem_name} "
                    f"({len(premises)} candidates) ===",
                )
            return block, names, record
        except Exception as exc:  # noqa: BLE001 - retrieval is advisory
            record = {
                "enabled": True,
                "error": f"{type(exc).__name__}: {exc}",
                "failure_kind": "precompute_exception",
                "raw_hit_count": 0,
                "filtered_hit_count": 0,
            }
            increment = getattr(target_dossier, "increment_tool_metric", None)
            if callable(increment):
                increment("mini_premise_retrieval_precompute_failures", 1)
            if event_recorder is not None and hasattr(event_recorder, "record_turn"):
                event_recorder.record_turn(
                    {
                        "phase": "premise_retrieval",
                        "goal_statement": goal_statement,
                        "top_k": int(premise_retrieval_top_k or 0),
                        "premise_retrieval_error": record["error"],
                        "verdict": "premise_retrieval_precompute_failed",
                    }
                )
            _trace(
                event_trace_prefix,
                "=== premise retrieval failed; continuing without precomputed "
                f"premises: {record['error']} ===",
            )
            return "", [], record

    async def _run_startup_root_fast_lane() -> Tuple[bool, Optional[str]]:
        enabled = bool(kwargs.get("startup_root_fast_lane_enabled", False))
        if not enabled:
            return False, None
        if (
            int(
                dossier.tool_metrics.get(
                    "mini_startup_root_fast_lane_completed",
                    0,
                )
                or 0
            )
            > 0
        ):
            return False, None
        dossier.increment_tool_metric(
            "mini_startup_root_fast_lane_attempts",
            1,
        )
        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(
                {
                    "phase": "startup_root_fast_lane",
                    "stage": "started",
                    "tactic_timeout_s": float(
                        kwargs.get(
                            "startup_root_fast_lane_tactic_timeout_s",
                            300.0,
                        )
                        or 0.0
                    ),
                    "verdict": "fast_lane_started",
                }
            )
        tactic_timeout_s = max(
            0.1,
            float(
                kwargs.get(
                    "startup_root_fast_lane_tactic_timeout_s",
                    300.0,
                )
                or 0.1
            ),
        )
        tactic_dossier = _clone_dossier_for_session(dossier)
        tactic_recorder = QuarantinedTurnRecorder(recorder)
        try:
            tactic_ok, tactic_proof = await await_with_strict_deadline(
                _try_root_tactic_close(
                    phase="startup_root_fast_lane_tactic",
                    theorem_name=problem.theorem_name,
                    goal_statement=problem.statement_type,
                    preamble=lean_preamble,
                    lean=lean,
                    dossier=tactic_dossier,
                    recorder=tactic_recorder,
                    trace_prefix=trace_prefix,
                    timeout_s=tactic_timeout_s,
                    max_candidates=max(
                        1,
                        int(
                            kwargs.get(
                                "startup_root_fast_lane_tactic_max_candidates",
                                12,
                            )
                            or 1
                        ),
                    ),
                ),
                timeout_s=tactic_timeout_s,
                operation_label="mini_startup_root_fast_lane_tactic",
                operation_ownership="result_only",
            )
        except asyncio.TimeoutError:
            tactic_recorder.discard()
            tactic_ok, tactic_proof = False, None
            dossier.increment_tool_metric(
                "mini_startup_root_fast_lane_tactic_timeouts",
                1,
            )
            if recorder is not None and hasattr(recorder, "record_turn"):
                recorder.record_turn(
                    {
                        "phase": "startup_root_fast_lane",
                        "stage": "deterministic_root_tactic",
                        "timeout_s": tactic_timeout_s,
                        "verdict": "root_tactic_deadline_exhausted",
                    }
                )
        else:
            tactic_recorder.commit()
            if tactic_ok:
                _copy_dossier_contents(dossier, tactic_dossier)
        if tactic_ok:
            dossier.increment_tool_metric(
                "mini_startup_root_fast_lane_tactic_solved",
                1,
            )
            dossier.increment_tool_metric(
                "mini_startup_root_fast_lane_completed",
                1,
            )
            return True, tactic_proof
        dossier.increment_tool_metric(
            "mini_startup_root_fast_lane_completed",
            1,
        )
        dossier.increment_tool_metric(
            "mini_startup_root_fast_lane_unsolved",
            1,
        )
        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(
                {
                    "phase": "startup_root_fast_lane",
                    "stage": "completed",
                    "solved": False,
                    "verdict": "fast_lane_exhausted",
                }
            )
        return False, None

    # READY is a process-startup handshake, so publish it before any proof
    # search (including the startup fast lane). Durable
    # restore/merge work below has its own supervisor-enforced operation lease.
    _signal_worker_ready_once()
    ok, proof = await _run_startup_root_fast_lane()
    if ok:
        return True, proof
    # The one-shot lane has finished. Drop its knobs from the shared kwargs so
    # every later sample / post-fanin ``build_session_for_prove_problem`` call
    # cannot TypeError on unexpected startup_* keywords.
    _strip_startup_root_fast_lane_session_kwargs(kwargs)

    async def _run_attempt(
        *,
        llm_preamble: str,
        lean_preamble: str,
        attempt_dossier: ProofDossier,
        branch_label: str = "",
        initial_context: str = "",
        premise_block: str = "",
        premise_names: Sequence[str] = (),
        premise_retrieval_record: Optional[Dict[str, Any]] = None,
    ) -> Tuple[bool, Optional[str]]:
        nonlocal recursive_pass_budget_remaining
        nonlocal adaptive_recursive_pass_budget_remaining
        terminal_llm_failure_reason = ""
        terminal_llm_failure_kind = ""
        if shared_proof_cache is not None:
            shared_proof_cache.set_store_failure_metric_sink(
                attempt_dossier.increment_tool_metric
            )

        def _remember_terminal_llm_failure(
            reason: str,
            *,
            kind: str = "",
        ) -> None:
            nonlocal terminal_llm_failure_reason
            nonlocal terminal_llm_failure_kind
            clean_reason = str(reason or "").strip()
            if not is_terminal_llm_failure_reason(clean_reason):
                return
            if not terminal_llm_failure_reason:
                terminal_llm_failure_reason = clean_reason
            if kind and not terminal_llm_failure_kind:
                terminal_llm_failure_kind = str(kind or "").strip()
            try:
                setattr(
                    attempt_dossier,
                    "session_failure_reason",
                    terminal_llm_failure_reason,
                )
                if terminal_llm_failure_kind:
                    setattr(
                        attempt_dossier,
                        "session_failure_kind",
                        terminal_llm_failure_kind,
                    )
            except Exception:
                pass

        def _current_terminal_llm_failure_reason() -> str:
            reason = (
                terminal_llm_failure_reason
                or str(getattr(attempt_dossier, "session_failure_reason", "") or "")
            ).strip()
            return reason if is_terminal_llm_failure_reason(reason) else ""

        def _increment_attempt_metric(key: str, amount: int = 1) -> None:
            increment = getattr(attempt_dossier, "increment_tool_metric", None)
            if callable(increment):
                try:
                    increment(key, amount)
                    return
                except Exception:
                    pass
            metrics = getattr(attempt_dossier, "tool_metrics", None)
            if isinstance(metrics, dict):
                metrics[key] = int(metrics.get(key, 0) or 0) + int(amount or 0)

        def _record_recursive_fallback_suppressed(
            *,
            phase_label: str,
            adaptive_fallback: bool,
        ) -> None:
            reason = _current_terminal_llm_failure_reason()
            if not reason:
                return
            metric_key = (
                "mini_adaptive_recursive_fallback_suppressed_terminal_failure"
                if adaptive_fallback
                else "mini_recursive_followup_suppressed_terminal_failure"
            )
            _increment_attempt_metric(metric_key, 1)
            _trace(
                trace_prefix,
                "=== mini recursive skipped "
                f"{phase_label}: terminal LLM failure already recorded ({reason}) ===",
            )
            if recorder is not None and hasattr(recorder, "record_turn"):
                recorder.record_turn(
                    {
                        "phase": "mini_recursive_fallback_policy",
                        "branch_label": f"{branch_label} {phase_label}".strip(),
                        "adaptive_fallback": bool(adaptive_fallback),
                        "terminal_failure_reason": reason,
                        "verdict": (
                            "adaptive_fallback_suppressed_terminal_failure"
                            if adaptive_fallback
                            else "recursive_followup_suppressed_terminal_failure"
                        ),
                    }
                )

        def _record_prove_followup_suppressed(
            *,
            phase_label: str,
            followup_kind: str,
        ) -> None:
            reason = _current_terminal_llm_failure_reason()
            if not reason:
                return
            _increment_attempt_metric(
                "mini_prove_followup_suppressed_terminal_failure",
                1,
            )
            _trace(
                trace_prefix,
                "=== mini prove follow-up skipped "
                f"{phase_label}: terminal LLM failure already recorded ({reason}) ===",
            )
            if recorder is not None and hasattr(recorder, "record_turn"):
                recorder.record_turn(
                    {
                        "phase": "mini_terminal_llm_followup_policy",
                        "branch_label": f"{branch_label} {phase_label}".strip(),
                        "followup_kind": str(followup_kind or ""),
                        "terminal_failure_reason": reason,
                        "verdict": "prove_followup_suppressed_terminal_failure",
                    }
                )

        async def _run_recursive_controller(
            *,
            phase_label: str,
            adaptive_fallback: bool = False,
        ) -> Tuple[bool, Optional[str]]:
            nonlocal recursive_pass_budget_remaining
            nonlocal adaptive_recursive_pass_budget_remaining
            nonlocal llm_preamble
            nonlocal lean_preamble
            nonlocal container_theory_context
            remaining = (
                adaptive_recursive_pass_budget_remaining
                if adaptive_fallback
                else recursive_pass_budget_remaining
            )
            if remaining <= 0:
                _trace(
                    trace_prefix,
                    f"=== mini recursive skipped {phase_label}: "
                    "pass budget exhausted ===",
                )
                if recorder is not None and hasattr(recorder, "record_turn"):
                    recorder.record_turn(
                        {
                            "phase": "mini_recursive_budget",
                            "branch_label": (f"{branch_label} {phase_label}".strip()),
                            "passes_remaining": 0,
                            "budget_kind": (
                                "adaptive_recursive_fallback"
                                if adaptive_fallback
                                else "recursive_prepass"
                            ),
                            "terminal": False,
                            "skip_reason": "pass_budget_exhausted",
                            "verdict": "recursive_pass_budget_exhausted",
                        }
                    )
                return False, None

            passes_for_run = min(
                max(1, int(kwargs.get("mini_recursive_passes", 1) or 1)),
                remaining,
            )
            remaining = max(0, remaining - passes_for_run)
            if adaptive_fallback:
                adaptive_recursive_pass_budget_remaining = remaining
            else:
                recursive_pass_budget_remaining = remaining

            # Retry/liveness authority exists even when mini-theory is off.
            # Every child callback in this recursive attempt shares it.
            recursive_attempt_lane_owner = SimpleNamespace()
            recursive_theory_parent = None
            if (
                theory_library is not None
                and getattr(theory_library, "mode", "off") != "off"
            ):
                from ..mini_theory import TheoryContextPair

                snapshot_ids = tuple(
                    str(item.get("bundle_id") or "").strip()
                    for item in tuple(
                        getattr(attempt_dossier, "mini_theory_snapshot", ()) or ()
                    )
                    if isinstance(item, dict)
                    and str(item.get("bundle_id") or "").strip()
                )
                inherited_ids = tuple(
                    dict.fromkeys(
                        (
                            *snapshot_ids,
                            *tuple(
                                getattr(
                                    getattr(container_theory_context, "lean", None),
                                    "bundle_ids",
                                    (),
                                )
                                or ()
                            ),
                        )
                    )
                )
                recursive_theory_context = TheoryContextPair.from_preambles(
                    llm_preamble=llm_preamble,
                    lean_preamble=lean_preamble,
                )
                inherited_parent_environment_hash = str(
                    attempt_dossier.current_lean_environment_hash or ""
                )
                if inherited_ids:
                    recursive_theory_context = theory_library.select_context(
                        recursive_theory_context,
                        bundle_ids=inherited_ids,
                    )
                    llm_preamble = recursive_theory_context.llm.render()
                    lean_preamble = recursive_theory_context.lean.render()
                    attempt_dossier.record_lean_environment(
                        text_hash(lean_preamble),
                        extends_environment_hash=(inherited_parent_environment_hash),
                        environment_source_text=lean_preamble,
                    )
                recursive_theory_parent = SimpleNamespace(
                    theory_library=theory_library,
                    theory_candidate_builder=kwargs.get("theory_candidate_builder"),
                    theory_context_pair=recursive_theory_context,
                    theory_domain=str(
                        kwargs.get("theory_domain") or "general mathematics"
                    ),
                    theory_default_imports=tuple(
                        kwargs.get("theory_default_imports") or ("Mathlib",)
                    ),
                    theory_imported_bundle_ids=inherited_ids,
                    theory_snapshot=(
                        theory_library.snapshot(inherited_ids) if inherited_ids else ()
                    ),
                    # This is the authoritative retrieval view used by the
                    # recursive driver and its root-close followups.  Theory
                    # metadata without matching active search visibility is a
                    # split environment: Lean can import a committed bundle
                    # while premise retrieval remains pinned to the parent
                    # snapshot.
                    searcher=searcher,
                )

                def _install_recursive_theory(bundle_ids: Sequence[str]) -> bool:
                    nonlocal recursive_theory_context
                    nonlocal llm_preamble
                    nonlocal lean_preamble
                    nonlocal container_theory_context
                    selected = tuple(
                        dict.fromkeys(
                            (
                                *recursive_theory_parent.theory_imported_bundle_ids,
                                *tuple(bundle_ids),
                            )
                        )
                    )
                    if selected == recursive_theory_parent.theory_imported_bundle_ids:
                        return False
                    previous_environment_hash = str(
                        attempt_dossier.current_lean_environment_hash or ""
                    )
                    recursive_theory_context = theory_library.select_context(
                        recursive_theory_context,
                        bundle_ids=selected,
                    )
                    recursive_theory_parent.theory_context_pair = (
                        recursive_theory_context
                    )
                    container_theory_context = recursive_theory_context
                    recursive_theory_parent.theory_imported_bundle_ids = selected
                    recursive_theory_parent.theory_snapshot = theory_library.snapshot(
                        selected
                    )
                    llm_preamble = recursive_theory_context.llm.render()
                    lean_preamble = recursive_theory_context.lean.render()
                    attempt_dossier.record_lean_environment(
                        text_hash(lean_preamble),
                        extends_environment_hash=previous_environment_hash,
                        environment_source_text=lean_preamble,
                    )
                    attempt_dossier.mini_theory_snapshot = (
                        recursive_theory_parent.theory_snapshot
                    )
                    attempt_dossier.mini_theory_context_hash = (
                        recursive_theory_context.snapshot_hash
                    )
                    set_active_bundle_ids = getattr(
                        recursive_theory_parent.searcher,
                        "set_active_bundle_ids",
                        None,
                    )
                    if callable(set_active_bundle_ids):
                        set_active_bundle_ids(selected)
                    return True

                recursive_theory_parent.install_theory_bundles = (
                    _install_recursive_theory
                )

                def _capture_recursive_theory_installation_state() -> dict[str, Any]:
                    active_bundle_ids = tuple(
                        recursive_theory_parent.theory_imported_bundle_ids or ()
                    )
                    active_getter = getattr(
                        getattr(recursive_theory_parent, "searcher", None),
                        "active_bundle_ids",
                        None,
                    )
                    if callable(active_getter):
                        active_bundle_ids = tuple(active_getter() or ())
                    return {
                        "recursive_theory_context": recursive_theory_context,
                        "llm_preamble": llm_preamble,
                        "lean_preamble": lean_preamble,
                        "container_theory_context": container_theory_context,
                        "theory_context_pair": (
                            recursive_theory_parent.theory_context_pair
                        ),
                        "theory_imported_bundle_ids": tuple(
                            recursive_theory_parent.theory_imported_bundle_ids or ()
                        ),
                        "theory_snapshot": copy.deepcopy(
                            tuple(recursive_theory_parent.theory_snapshot or ())
                        ),
                        "dossier_mini_theory_snapshot": copy.deepcopy(
                            tuple(
                                getattr(
                                    attempt_dossier,
                                    "mini_theory_snapshot",
                                    (),
                                )
                                or ()
                            )
                        ),
                        "dossier_mini_theory_context_hash": str(
                            getattr(
                                attempt_dossier,
                                "mini_theory_context_hash",
                                "",
                            )
                            or ""
                        ),
                        "dossier_current_lean_environment_hash": str(
                            attempt_dossier.current_lean_environment_hash or ""
                        ),
                        "dossier_lean_environment_ancestor_hashes": copy.deepcopy(
                            attempt_dossier.lean_environment_ancestor_hashes
                        ),
                        "searcher_active_bundle_ids": active_bundle_ids,
                    }

                def _restore_recursive_theory_installation_state(
                    state: dict[str, Any],
                ) -> None:
                    nonlocal recursive_theory_context
                    nonlocal llm_preamble
                    nonlocal lean_preamble
                    nonlocal container_theory_context
                    recursive_theory_context = state["recursive_theory_context"]
                    llm_preamble = str(state.get("llm_preamble") or "")
                    lean_preamble = str(state.get("lean_preamble") or "")
                    container_theory_context = state.get("container_theory_context")
                    recursive_theory_parent.theory_context_pair = state.get(
                        "theory_context_pair"
                    )
                    recursive_theory_parent.theory_imported_bundle_ids = tuple(
                        state.get("theory_imported_bundle_ids") or ()
                    )
                    recursive_theory_parent.theory_snapshot = copy.deepcopy(
                        tuple(state.get("theory_snapshot") or ())
                    )
                    attempt_dossier.mini_theory_snapshot = copy.deepcopy(
                        tuple(state.get("dossier_mini_theory_snapshot") or ())
                    )
                    attempt_dossier.mini_theory_context_hash = str(
                        state.get("dossier_mini_theory_context_hash") or ""
                    )
                    attempt_dossier.current_lean_environment_hash = str(
                        state.get("dossier_current_lean_environment_hash") or ""
                    )
                    attempt_dossier.lean_environment_ancestor_hashes = copy.deepcopy(
                        state.get("dossier_lean_environment_ancestor_hashes") or {}
                    )
                    set_active_bundle_ids = getattr(
                        getattr(recursive_theory_parent, "searcher", None),
                        "set_active_bundle_ids",
                        None,
                    )
                    if callable(set_active_bundle_ids):
                        set_active_bundle_ids(
                            tuple(state.get("searcher_active_bundle_ids") or ())
                        )

                recursive_theory_parent._capture_theory_installation_state = (
                    _capture_recursive_theory_installation_state
                )
                recursive_theory_parent._restore_theory_installation_state = (
                    _restore_recursive_theory_installation_state
                )

            async def _recursive_run_conversation(
                **conv_kwargs: Any,
            ) -> Tuple[bool, Optional[str]]:
                # The recursive driver must replay the child proof before it
                # commits any newly built theory bundle into this attempt.
                conv_kwargs["defer_theory_promotion"] = True
                if conv_kwargs.get("temperature_override") is None:
                    conv_kwargs["temperature_override"] = kwargs.get(
                        "sample_temperature"
                    )
                conv_kwargs.setdefault("proof_cache", shared_proof_cache)
                conv_kwargs.setdefault("cost_controller", kwargs.get("cost_controller"))
                conv_kwargs.setdefault(
                    "proof_state_batch_parallelism",
                    kwargs.get("proof_state_batch_parallelism", 1),
                )
                conv_kwargs.setdefault(
                    "proof_state_child_tactics_enabled",
                    kwargs.get("proof_state_child_tactics_enabled", True),
                )
                conv_kwargs.setdefault(
                    "proof_state_child_tactic_timeout_s",
                    kwargs.get(
                        "proof_state_child_tactic_timeout_s",
                        DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                    ),
                )
                conv_kwargs.setdefault(
                    "proof_state_child_tactic_max_candidates",
                    kwargs.get("proof_state_child_tactic_max_candidates", 32),
                )
                conv_kwargs.setdefault(
                    "proof_state_child_goal_limit",
                    kwargs.get("proof_state_child_goal_limit", 3),
                )
                conv_kwargs.setdefault(
                    "proof_state_decl_application_limit",
                    kwargs.get("proof_state_decl_application_limit", 6),
                )
                for formal_key, formal_default in (
                    ("formal_state_search_enabled", False),
                    (
                        "formal_state_search_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                    ),
                    (
                        "formal_state_search_operation_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
                    ),
                    (
                        "formal_state_search_provider_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
                    ),
                    (
                        "formal_state_search_provider_max_tokens",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
                    ),
                    (
                        "formal_state_search_provider_reasoning_effort",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
                    ),
                    ("formal_state_search_provider_max_attempts", 2),
                    ("formal_state_search_provider_retry_backoff_s", 5.0),
                    ("formal_state_search_beam_width", 4),
                    ("formal_state_search_max_steps", 8),
                    ("formal_state_search_max_candidates", 6),
                    ("formal_state_search_backtrack_limit", 8),
                    ("formal_state_search_max_no_improvement_quanta", 6),
                ):
                    conv_kwargs.setdefault(
                        formal_key,
                        kwargs.get(formal_key, formal_default),
                    )
                conv_kwargs.setdefault(
                    "proof_state_retrieval_enabled",
                    kwargs.get("proof_state_retrieval_enabled", False),
                )
                conv_kwargs.setdefault(
                    "repair_retrieval_enabled",
                    kwargs.get("repair_retrieval_enabled", True),
                )
                conv_kwargs.setdefault(
                    "repair_retrieval_top_k",
                    kwargs.get("repair_retrieval_top_k", 6),
                )
                return await _mini_session_run_conversation_callback(
                    theory_parent_session=recursive_theory_parent,
                    recursive_lane_owner=recursive_attempt_lane_owner,
                    **conv_kwargs,
                )

            recursive_result = await run_mini_recursive_attempt(
                theorem_name=problem.theorem_name,
                root_statement=problem.statement_type,
                problem_text=problem_text,
                lean_signature=lean_signature,
                prover_client=prover_client,
                refiner_client=kwargs.get("refiner_client"),
                planner_escalation_client=kwargs.get("planner_escalation_client"),
                lean=lean,
                llm_preamble=llm_preamble,
                lean_preamble=lean_preamble,
                attempt_dossier=attempt_dossier,
                conversation_cls=Conversation,
                run_conversation_fn=_recursive_run_conversation,
                max_tool_calls_per_turn=int(
                    kwargs.get("max_tool_calls_per_turn", 10) or 0
                ),
                lean_check_tool_enabled=bool(
                    kwargs.get("lean_check_tool_enabled", True)
                ),
                try_lean_tool_enabled=bool(kwargs.get("try_lean_tool_enabled", True)),
                compute_examples_tool_enabled=compute_examples_enabled_for_kwargs,
                apply_decl_to_goal_tool_enabled=bool(
                    kwargs.get("apply_decl_to_goal_tool_enabled", True)
                ),
                raw_feedback=bool(kwargs.get("raw_feedback", False)),
                repair_retrieval_enabled=bool(
                    kwargs.get("repair_retrieval_enabled", True)
                ),
                repair_retrieval_top_k=int(
                    kwargs.get("repair_retrieval_top_k", 6) or 0
                ),
                proof_state_child_tactics_enabled=bool(
                    kwargs.get("proof_state_child_tactics_enabled", True)
                ),
                proof_state_child_tactic_timeout_s=float(
                    kwargs.get(
                        "proof_state_child_tactic_timeout_s",
                        DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                    )
                    or 0.0
                ),
                proof_state_child_tactic_max_candidates=int(
                    kwargs.get("proof_state_child_tactic_max_candidates", 32) or 0
                ),
                root_tactic_timeout_s=float(
                    kwargs.get("root_tactic_timeout_s", 40.0) or 0.0
                ),
                root_tactic_max_candidates=int(
                    kwargs.get("root_tactic_max_candidates", 64) or 0
                ),
                proof_state_child_goal_limit=int(
                    kwargs.get("proof_state_child_goal_limit", 3) or 0
                ),
                proof_state_decl_application_limit=int(
                    kwargs.get("proof_state_decl_application_limit", 6) or 0
                ),
                proof_state_batch_parallelism=int(
                    kwargs.get("proof_state_batch_parallelism", 1) or 1
                ),
                recorder=recorder,
                searcher=searcher,
                proof_cache=shared_proof_cache,
                cache_owner_theorem_name=str(
                    getattr(attempt_dossier, "cache_owner_theorem_name", "")
                    or problem.theorem_name
                    or ""
                ),
                cost_controller=kwargs.get("cost_controller"),
                trace_prefix=trace_prefix,
                trace=lambda msg: _trace(trace_prefix, msg),
                branch_label=(f"{branch_label} {phase_label}".strip()),
                opaque_mode=opaque_mode,
                allow_official_answer_visibility=allow_official_answer_visibility,
                official_answer_payload_present=getattr(
                    attempt_dossier,
                    "official_answer_payload_present",
                    None,
                ),
                adaptive_fallback=adaptive_fallback,
                budget_kind=(
                    "adaptive_recursive_fallback"
                    if adaptive_fallback
                    else "recursive_prepass"
                ),
                config=MiniRecursiveConfig(
                    planner_deliberation_enabled=(
                        production_planner_deliberation_default()
                    ),
                    **_mini_recursive_planner_deadline_kwargs(prover_client),
                    planner_sanity_contract_required=True,
                    passes=passes_for_run,
                    max_claims=max(
                        1,
                        int(
                            kwargs.get(
                                "mini_recursive_max_claims",
                                PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
                            )
                            or 1
                        ),
                    ),
                    turns_per_claim=max(
                        1,
                        int(kwargs.get("mini_recursive_turns_per_claim", 3) or 1),
                    ),
                    recursive_child_max_elapsed_s=(
                        _mini_recursive_child_elapsed_budget_s(
                            prover_client,
                            kwargs.get("refiner_client"),
                            turns_per_claim=max(
                                1,
                                int(
                                    kwargs.get(
                                        "mini_recursive_turns_per_claim", 3
                                    )
                                    or 1
                                ),
                            ),
                            tactic_timeout_s=max(
                                1.0,
                                float(
                                    kwargs.get(
                                        "mini_recursive_tactic_timeout_s", 20.0
                                    )
                                    or 1.0
                                ),
                            ),
                        )
                    ),
                    tactic_timeout_s=max(
                        1.0,
                        float(
                            kwargs.get("mini_recursive_tactic_timeout_s", 20.0) or 1.0
                        ),
                    ),
                    tactic_max_candidates=max(
                        1,
                        int(
                            kwargs.get("mini_recursive_tactic_max_candidates", 48) or 1
                        ),
                    ),
                    progress_continuation_passes=1,
                    mini_phase_temperatures=kwargs.get("mini_phase_temperatures"),
                    sample_temperature=kwargs.get("sample_temperature"),
                    falsification_enabled=bool(
                        kwargs.get("falsification_enabled", True)
                    ),
                    falsification_max_checks=kwargs.get("falsification_max_checks", 32),
                    falsification_operation_timeout_s=kwargs.get(
                        "falsification_operation_timeout_s",
                        DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
                    ),
                    falsification_engine_timeout_s=kwargs.get(
                        "falsification_engine_timeout_s",
                        DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
                    ),
                ),
                verified_helper_accept_callback=getattr(
                    recursive_theory_parent,
                    "theory_verified_helper_accept_callback",
                    None,
                ),
            )
            if getattr(recursive_result, "ok", False) and getattr(
                recursive_result, "proof", None
            ):
                return True, recursive_result.proof
            _remember_terminal_llm_failure(
                str(getattr(recursive_result, "failure_reason", "") or "")
            )
            return False, None

        async def _run_root_tactic_prepass(
            *,
            effective_lean_preamble: Optional[str] = None,
        ) -> Tuple[bool, Optional[str]]:
            if not bool(kwargs.get("root_tactic_prepass_enabled", False)):
                return False, None
            return await _try_root_tactic_close(
                phase="root_tactic_prepass",
                theorem_name=problem.theorem_name,
                goal_statement=problem.statement_type,
                preamble=(
                    str(effective_lean_preamble)
                    if effective_lean_preamble is not None
                    else lean_preamble
                ),
                lean=lean,
                dossier=attempt_dossier,
                recorder=recorder,
                trace_prefix=trace_prefix,
                timeout_s=float(kwargs.get("root_tactic_timeout_s", 40.0) or 0.0),
                max_candidates=int(kwargs.get("root_tactic_max_candidates", 64) or 0),
            )

        pre_sample_root_tactic_ran = False
        if bool(kwargs.get("root_tactic_prepass_enabled", False)):
            pre_sample_root_tactic_ran = True
            ok, proof = await _run_root_tactic_prepass()
            if ok:
                return True, proof

        if _current_terminal_llm_failure_reason():
            if bool(kwargs.get("adaptive_recursive_on_stall", False)):
                _record_recursive_fallback_suppressed(
                    phase_label="[adaptive recursive after terminal prepass failure]",
                    adaptive_fallback=True,
                )
            else:
                _record_prove_followup_suppressed(
                    phase_label="[prove sample after terminal prepass failure]",
                    followup_kind="sample_session",
                )
            return False, None

        sample_temps = _stratify_sample_temperatures(
            sample_count,
            tuple(float(t) for t in (kwargs.get("parallel_temperatures") or ())),
        )
        post_fanin_theory_bundle_ids = tuple(
            getattr(
                getattr(container_theory_context, "lean", None),
                "bundle_ids",
                (),
            )
            or ()
        )
        post_fanin_llm_preamble = llm_preamble
        post_fanin_lean_preamble = lean_preamble
        post_fanin_theory_context_hash = str(
            getattr(container_theory_context, "snapshot_hash", "") or ""
        )
        post_fanin_recorded_theory_snapshot: Tuple[Dict[str, Any], ...] = ()

        def _resolve_post_fanin_theory_environment() -> None:
            """Materialize the selected failed sample's exact theory context."""

            nonlocal post_fanin_theory_bundle_ids
            nonlocal post_fanin_llm_preamble
            nonlocal post_fanin_lean_preamble
            nonlocal post_fanin_theory_context_hash
            nonlocal post_fanin_recorded_theory_snapshot

            raw_snapshot = tuple(
                getattr(attempt_dossier, "mini_theory_snapshot", ()) or ()
            )
            if raw_snapshot:
                post_fanin_theory_bundle_ids = _validated_dossier_theory_bundle_ids(
                    attempt_dossier,
                    theory_library,
                )
                post_fanin_recorded_theory_snapshot = tuple(
                    dict(item) for item in raw_snapshot
                )
            if not post_fanin_theory_bundle_ids:
                return
            if (
                theory_library is None
                or getattr(theory_library, "mode", "off") == "off"
            ):
                raise ValueError(
                    "parallel fan-in theory context requires an available "
                    "Mini theory library"
                )

            from ..mini_theory import TheoryContextPair

            pair = TheoryContextPair.from_preambles(
                llm_preamble=llm_preamble,
                lean_preamble=lean_preamble,
            )
            selected = theory_library.select_context(
                pair,
                bundle_ids=post_fanin_theory_bundle_ids,
            )
            selected_ids = tuple(
                getattr(getattr(selected, "lean", None), "bundle_ids", ()) or ()
            )
            if selected_ids != post_fanin_theory_bundle_ids:
                raise ValueError(
                    "parallel fan-in Mini theory selection changed the exact "
                    "dependency-closed bundle order"
                )
            selected_hash = str(getattr(selected, "snapshot_hash", "") or "")
            recorded_hash = str(
                getattr(attempt_dossier, "mini_theory_context_hash", "") or ""
            )
            if post_fanin_recorded_theory_snapshot and (
                not recorded_hash or selected_hash != recorded_hash
            ):
                raise ValueError(
                    "selected parallel sample Mini theory context hash is "
                    "missing or no longer reproducible"
                )
            post_fanin_llm_preamble = selected.llm.render()
            post_fanin_lean_preamble = selected.lean.render()
            post_fanin_theory_context_hash = selected_hash
            recorded_environment_hash = str(
                getattr(attempt_dossier, "current_lean_environment_hash", "") or ""
            )
            if post_fanin_recorded_theory_snapshot and (
                not recorded_environment_hash
                or recorded_environment_hash != text_hash(post_fanin_lean_preamble)
            ):
                raise ValueError(
                    "selected parallel sample Lean environment hash is missing "
                    "or no longer reproducible "
                    f"(recorded={recorded_environment_hash or '<missing>'}, "
                    f"reconstructed={text_hash(post_fanin_lean_preamble)})"
                )

        def _build_post_fanin_recursive_session() -> MiniSession:
            """Build the sole lifecycle owner of merged parallel recursive work."""

            container_kwargs = dict(kwargs)
            container_kwargs.update(
                {
                    "problem": problem,
                    "dossier": attempt_dossier,
                    "recorder": recorder,
                    "trace_prefix": trace_prefix + "  [parallel-fanin] ",
                    "premise_retrieval_enabled": False,
                    "root_tactic_prepass_enabled": False,
                    "parallel_samples": 1,
                    "parallel_temperatures": (),
                    "llm_preamble_override": llm_preamble,
                    "lean_preamble_override": lean_preamble,
                    "theory_bundle_ids": post_fanin_theory_bundle_ids,
                    "initial_context": initial_context,
                    "premise_block": "",
                    "premise_names": (),
                    "recursive_pass_budget_override": (recursive_pass_budget_remaining),
                    "adaptive_recursive_pass_budget_override": (
                        adaptive_recursive_pass_budget_remaining
                    ),
                    "session_scope": "parallel_fanin_recursive",
                }
            )
            for key in ("parallel_late_sample_grace_s",):
                container_kwargs.pop(key, None)
            _strip_startup_root_fast_lane_session_kwargs(container_kwargs)
            container = build_session_for_prove_problem(**container_kwargs)
            if str(getattr(container.conv, "preamble", "") or "") != str(
                post_fanin_llm_preamble
            ):
                raise ValueError(
                    "parallel fan-in Mini theory model context was not "
                    "reconstructed exactly"
                )
            if str(getattr(container.conv, "lean_preamble", "") or "") != str(
                post_fanin_lean_preamble
            ):
                raise ValueError(
                    "parallel fan-in Mini theory Lean context was not "
                    "reconstructed exactly"
                )
            if tuple(getattr(container, "theory_imported_bundle_ids", ()) or ()) != (
                post_fanin_theory_bundle_ids
            ):
                raise ValueError(
                    "parallel fan-in Mini theory imports do not match the "
                    "selected sample"
                )
            if (
                post_fanin_recorded_theory_snapshot
                and tuple(
                    dict(item)
                    for item in getattr(container, "theory_snapshot", ()) or ()
                )
                != post_fanin_recorded_theory_snapshot
            ):
                raise ValueError(
                    "parallel fan-in Mini theory provenance changed during "
                    "session construction"
                )
            if (
                post_fanin_recorded_theory_snapshot
                and str(
                    getattr(
                        getattr(container, "theory_context_pair", None),
                        "snapshot_hash",
                        "",
                    )
                    or ""
                )
                != post_fanin_theory_context_hash
            ):
                raise ValueError(
                    "parallel fan-in Mini theory context identity changed "
                    "during session construction"
                )
            active_bundle_ids = getattr(container.searcher, "active_bundle_ids", None)
            if post_fanin_theory_bundle_ids and not callable(active_bundle_ids):
                raise ValueError(
                    "parallel fan-in retrieval cannot attest active Mini "
                    "theory visibility"
                )
            if callable(active_bundle_ids) and tuple(active_bundle_ids()) != (
                post_fanin_theory_bundle_ids
            ):
                raise ValueError(
                    "parallel fan-in retrieval visibility does not match the "
                    "selected Mini theory environment"
                )
            owner_ids = {"recursive_controller", "adaptive_recursive_fallback"}
            container.actions = [
                action for action in container.actions if action.id in owner_ids
            ]
            container.budgets = {
                action_id: budget
                for action_id, budget in container.budgets.items()
                if action_id in owner_ids
            }
            container.fallback_action_ids.intersection_update(owner_ids)
            container.max_iterations = max(4, len(container.actions) * 3 + 2)
            container.parallel_fanin_container = True
            return container

        async def _run_post_fanin_recursive_session() -> Tuple[bool, Optional[str]]:
            nonlocal recursive_pass_budget_remaining
            nonlocal adaptive_recursive_pass_budget_remaining
            container = _build_post_fanin_recursive_session()
            try:
                ok, proof = await container.run()
            finally:
                # The post-fanin container is a full helper-producing lane.
                # Stage before any cancellation can leave this scope.
                _stage_all_session_verified_helpers(container, force=True)
                # The container owns the live recursive dossier and pass pools.
                # Preserve committed work even when cancellation or an
                # infrastructure exception prevents ``run`` from returning.
                recursive_pass_budget_remaining = int(
                    getattr(container, "recursive_pass_budget_remaining", 0) or 0
                )
                adaptive_recursive_pass_budget_remaining = int(
                    getattr(
                        container,
                        "adaptive_recursive_pass_budget_remaining",
                        0,
                    )
                    or 0
                )
                _copy_dossier_contents(attempt_dossier, container.dossier)
                failure_reason = str(
                    getattr(container, "last_failure_reason", "") or ""
                )
                if is_terminal_llm_failure_reason(failure_reason):
                    _remember_terminal_llm_failure(
                        failure_reason,
                        kind=str(getattr(container, "terminal_failure_kind", "") or ""),
                    )
            return bool(ok), proof

        parallel_observability_baseline = (
            _parallel_observability_snapshot(attempt_dossier)
            if sample_count > 1
            else {}
        )
        parallel_sample_cache_paths: Dict[int, Path] = {}
        # Keep the producing object as well as its path.  A cache can detect
        # that deadline rollback could not persist a fail-closed marker; in
        # that incident its JSONL source is not safe to merge merely because
        # the path still exists.
        parallel_sample_caches: Dict[int, Any] = {}
        parallel_cache_integrity_incidents: Dict[int, str] = {}
        completed_sample_indices: Set[int] = set()
        sample_guards: Dict[int, _SampleAbandonGuard] = {}
        parallel_live_sample_dossiers: Dict[int, ProofDossier] = {}

        async def _run_one_sample(
            sample_index: int,
            sample_temperature: Optional[float],
        ) -> Tuple[
            bool,
            Optional[str],
            ProofDossier,
            Optional[int],
            Optional[int],
            bool,
            bool,
        ]:
            # For a single sample, let that same session own the root
            # mini-recursive prepass. Otherwise the sample burns all ordinary
            # prove turns and the outer controller only sees the recursive
            # budget after root proving has already stalled.
            sample_recursive_prepass_enabled = (
                sample_count == 1
                and bool(kwargs.get("mini_recursive_enabled", False))
                and recursive_pass_budget_remaining > 0
            )
            sample_adaptive_recursive_enabled = (
                bool(kwargs.get("adaptive_recursive_on_stall", False))
                and sample_count == 1
                and adaptive_recursive_pass_budget_remaining > 0
            )
            sample_label = (
                f"[s{sample_index + 1}/{sample_count}"
                + (
                    f" T={sample_temperature:.2f}"
                    if sample_temperature is not None
                    else ""
                )
                + "]"
                if sample_count > 1
                else ""
            )
            sample_trace_prefix = trace_prefix + (
                f"  {sample_label} " if sample_label else "  "
            )
            sample_proof_cache = (
                shared_proof_cache
                if sample_count == 1
                else _make_proof_state_cache(
                    enabled=proof_cache_enabled,
                    base_path=proof_cache_base_path,
                    sample_index=sample_index,
                    sample_count=sample_count,
                    run_id=proof_cache_run_id,
                    validated_seed=shared_proof_cache,
                )
            )
            if sample_count > 1 and sample_proof_cache is not None:
                parallel_sample_cache_paths[sample_index] = sample_proof_cache.path
                parallel_sample_caches[sample_index] = sample_proof_cache
            sample_guard = _SampleAbandonGuard()
            sample_guards[sample_index] = sample_guard
            guarded_proof_cache = (
                _GuardedProofCache(sample_proof_cache, sample_guard)
                if sample_count > 1 and sample_proof_cache is not None
                else sample_proof_cache
            )
            guarded_recorder = (
                _GuardedRecorder(recorder, sample_guard)
                if sample_count > 1 and recorder is not None
                else recorder
            )

            sample_dossier = _clone_dossier_for_session(attempt_dossier)
            parallel_live_sample_dossiers[sample_index] = sample_dossier
            if sample_count > 1:
                _clear_parallel_sample_observability(sample_dossier)
                _install_parallel_monotonic_metric_sink(
                    sample_dossier,
                    attempt_dossier,
                )
            if sample_proof_cache is not None:
                sample_proof_cache.set_store_failure_metric_sink(
                    sample_dossier.increment_tool_metric
                )

            suffix = f" {branch_label}" if branch_label else ""
            _trace(
                trace_prefix,
                f"=== prove {problem.theorem_name}{suffix}{sample_label} ===",
            )

            session_kwargs = dict(kwargs)
            sample_searcher = searcher
            if sample_count > 1:
                from .searcher_context import fork_searcher_context

                sample_searcher = fork_searcher_context(
                    sample_searcher,
                    theory_enabled=bool(
                        kwargs.get("theory_library") is not None
                        and str(
                            getattr(kwargs.get("theory_library"), "mode", "off")
                            or "off"
                        )
                        != "off"
                    ),
                )
            session_kwargs.update(
                {
                    "problem": problem,
                    "dossier": sample_dossier,
                    "recorder": guarded_recorder,
                    "searcher": sample_searcher,
                    "trace_prefix": sample_trace_prefix,
                    "premise_retrieval_enabled": False,
                    "root_tactic_prepass_enabled": False,
                    "mini_recursive_enabled": bool(
                        kwargs.get("mini_recursive_enabled", False)
                    ),
                    "adaptive_recursive_on_stall": sample_adaptive_recursive_enabled,
                    "recursive_pass_budget_override": (
                        recursive_pass_budget_remaining
                        if sample_recursive_prepass_enabled
                        else 0
                    ),
                    "adaptive_recursive_pass_budget_override": (
                        adaptive_recursive_pass_budget_remaining
                    ),
                    "parallel_samples": 1,
                    "parallel_temperatures": (),
                    "llm_preamble_override": llm_preamble,
                    "lean_preamble_override": lean_preamble,
                    "theory_bundle_ids": tuple(
                        getattr(
                            getattr(container_theory_context, "lean", None),
                            "bundle_ids",
                            (),
                        )
                        or ()
                    ),
                    "initial_context": initial_context,
                    "premise_block": "",
                    "premise_names": (),
                    "premise_retrieval_record": premise_retrieval_record,
                    "premise_zero_hit_policy": premise_zero_hit_policy,
                    "premise_zero_hit_suppress_library_first": (
                        premise_zero_hit_suppress_library_first
                    ),
                    "premise_zero_hit_max_local_turns": (
                        premise_zero_hit_max_local_turns
                    ),
                    "premise_zero_hit_allow_api_grounding_after_lean_failure": (
                        premise_zero_hit_allow_api_grounding_after_lean_failure
                    ),
                    "sample_temperature": sample_temperature,
                    "mini_phase_temperatures": kwargs.get("mini_phase_temperatures"),
                    "proof_cache_override": guarded_proof_cache,
                    "session_scope": str(
                        kwargs.get(
                            "session_scope",
                            "sample" if sample_count > 1 else "problem",
                        )
                        or ("sample" if sample_count > 1 else "problem")
                    ),
                    # Fix 3 (2026-05-22): turn on strict-progress accounting
                    # for the production prove path. Soft-only progress
                    # (bogus contradiction-route helpers, statement-duplicate
                    # helpers from the 1962_a5 5×Icc→range cascade) no
                    # longer resets the stagnation counter, so the
                    # adaptive_recursive_fallback can fire before an extended
                    # no-progress swamp.
                    # Tests and direct ``build_session_for_prove_problem``
                    # callers retain the legacy default of False.
                    "strict_progress_accounting": bool(
                        kwargs.get("strict_progress_accounting", True)
                    ),
                    "soft_progress_streak_cap": int(
                        kwargs.get("soft_progress_streak_cap", 4) or 0
                    ),
                }
            )
            session_kwargs.pop("parallel_late_sample_grace_s", None)
            # Defense in depth: shared kwargs are stripped after the outer
            # startup lane, but sample construction still drops the knobs
            # locally so a future caller that reintroduces them cannot crash.
            _strip_startup_root_fast_lane_session_kwargs(session_kwargs)
            session = build_session_for_prove_problem(**session_kwargs)
            # The builder may clone the supplied dossier. Register the exact
            # object MiniSession will mutate before its first awaited action.
            parallel_live_sample_dossiers[sample_index] = session.dossier
            effective_premise_block = str(premise_block or "").strip()
            effective_premise_names = list(premise_names or ())
            if effective_premise_block:
                session.conv.append_user(
                    effective_premise_block,
                    repair_semantics=_REPAIR_CONTINUATION,
                )
                known_names = list(
                    getattr(session.conv, "known_premise_names", []) or []
                )
                seen_names = set(known_names)
                for name in effective_premise_names:
                    name_str = str(name or "").strip()
                    if name_str and name_str not in seen_names:
                        known_names.append(name_str)
                        seen_names.add(name_str)
                session.conv.known_premise_names = known_names
            try:
                ok, proof = await session.run()
            finally:
                # A receipt is a bounded local write, not Lean work. Stage in
                # ``finally`` so cancellation preserves committed helpers,
                # while leaving compilation until after winner/fan-in choice.
                _stage_all_session_verified_helpers(session, force=True)
                _snapshot_session_state_for_caller(session)
                if sample_count == 1:
                    try:
                        _copy_dossier_contents(attempt_dossier, session.dossier)
                    except Exception:
                        pass
            sample_recursive_remaining: Optional[int] = None
            if sample_recursive_prepass_enabled:
                sample_recursive_remaining = max(
                    0,
                    int(getattr(session, "recursive_pass_budget_remaining", 0) or 0),
                )
            sample_adaptive_recursive_remaining: Optional[int] = None
            if bool(session_kwargs.get("adaptive_recursive_on_stall", False)):
                sample_adaptive_recursive_remaining = max(
                    0,
                    int(
                        getattr(
                            session,
                            "adaptive_recursive_pass_budget_remaining",
                            0,
                        )
                        or 0
                    ),
                )
            failure_reason = str(getattr(session, "last_failure_reason", "") or "")
            if is_terminal_llm_failure_reason(failure_reason):
                _remember_terminal_llm_failure(
                    failure_reason,
                    kind=str(getattr(session, "terminal_failure_kind", "") or ""),
                )
                try:
                    setattr(
                        session.dossier,
                        "session_failure_reason",
                        failure_reason,
                    )
                except Exception:
                    pass
            return (
                bool(ok),
                proof,
                session.dossier,
                sample_recursive_remaining,
                sample_adaptive_recursive_remaining,
                sample_recursive_prepass_enabled,
                sample_adaptive_recursive_enabled,
            )

        def _merge_parallel_sample_caches() -> None:
            if (
                not proof_cache_enabled
                or sample_count <= 1
                or not parallel_sample_cache_paths
            ):
                return
            base_cache = shared_proof_cache or MiniVerifiedLemmaCache(
                proof_cache_base_path
            )
            merged = 0
            completed_samples = sorted(
                (index, path)
                for index, path in parallel_sample_cache_paths.items()
                if index in completed_sample_indices
            )
            for sample_index, sample_path in completed_samples:
                sample_cache = parallel_sample_caches.get(sample_index)
                if bool(
                    getattr(
                        sample_cache,
                        "deadline_publication_integrity_unrecoverable",
                        False,
                    )
                ):
                    message = (
                        f"{sample_path}: skipped sample cache after unrecoverable "
                        "deadline-publication integrity incident"
                    )
                    base_cache.last_merge_errors.append(message)
                    _trace(trace_prefix, f"proof-state cache: CRITICAL {message}")
                    parallel_cache_integrity_incidents[sample_index] = message
                    continue
                merged += base_cache.merge_records_from_path(sample_path)
                for error in getattr(base_cache, "last_merge_errors", [])[:5]:
                    _trace(
                        trace_prefix,
                        f"proof-state cache: merge warning: {error}",
                    )
            # B3 fix (2026-05-11): surface store failures alongside
            # merge failures (parallel to mini_prover.py's summary).
            store_failures = int(getattr(base_cache, "total_store_failures", 0) or 0)
            if store_failures:
                _trace(
                    trace_prefix,
                    f"proof-state cache: {store_failures} store failure(s); "
                    "cross-problem reuse may have been lost for those helpers",
                )
                for error in getattr(base_cache, "last_store_errors", [])[:5]:
                    _trace(
                        trace_prefix,
                        f"proof-state cache: store warning: {error}",
                    )
            ingest_migrated = int(
                getattr(base_cache, "total_ingest_schema_migrated", 0) or 0
            )
            ingest_advisory = int(
                getattr(base_cache, "total_ingest_schema_advisory", 0) or 0
            )
            ingest_rejected = int(
                getattr(base_cache, "total_ingest_schema_rejected", 0) or 0
            )
            ingest_quality = int(
                getattr(base_cache, "total_ingest_quality_rejected", 0) or 0
            )
            ingest_projection = int(
                getattr(base_cache, "total_ingest_projection_rejected", 0) or 0
            )
            ingest_policy = int(
                getattr(base_cache, "total_ingest_policy_rejected", 0) or 0
            )
            ingest_field = int(
                getattr(base_cache, "total_ingest_field_rejected", 0) or 0
            )
            ingest_deduped = int(
                getattr(base_cache, "total_ingest_owner_deduped", 0) or 0
            )
            if (
                ingest_migrated
                or ingest_advisory
                or ingest_rejected
                or ingest_quality
                or ingest_projection
                or ingest_policy
                or ingest_field
                or ingest_deduped
            ):
                _trace(
                    trace_prefix,
                    "proof-state cache: ingest "
                    f"migrated={ingest_migrated} advisory={ingest_advisory} "
                    f"schema_rejected={ingest_rejected} "
                    f"quality_rejected={ingest_quality} "
                    f"projection_rejected={ingest_projection} "
                    f"policy_rejected={ingest_policy} "
                    f"field_rejected={ingest_field} owner_deduped={ingest_deduped}",
                )
                for error in getattr(base_cache, "last_ingest_rejections", [])[:5]:
                    _trace(
                        trace_prefix,
                        f"proof-state cache: ingest warning: {error}",
                    )
            if bool(
                getattr(
                    base_cache, "deadline_publication_integrity_unrecoverable", False
                )
            ):
                _trace(
                    trace_prefix,
                    "proof-state cache: CRITICAL deadline-publication recovery "
                    "could not persist a fail-closed marker; quarantine storage "
                    "before reusing this cache path.",
                )
            if merged:
                _trace(
                    trace_prefix,
                    f"proof-state cache: merged {merged} parallel sample helper(s)",
                )

        def _restore_parallel_cache_integrity_observability() -> None:
            """Reapply fan-in cache incidents after dossier copy/restore."""

            if not parallel_cache_integrity_incidents:
                return
            metric_name = "mini_lemma_cache_deadline_integrity_unrecoverable"
            baseline_metrics = dict(
                parallel_observability_baseline.get("tool_metrics") or {}
            )
            baseline_count = int(baseline_metrics.get(metric_name, 0) or 0)
            required_count = baseline_count + len(parallel_cache_integrity_incidents)
            current_count = int(
                getattr(attempt_dossier, "tool_metrics", {}).get(metric_name, 0) or 0
            )
            increment = getattr(attempt_dossier, "increment_tool_metric", None)
            if callable(increment) and current_count < required_count:
                try:
                    increment(metric_name, required_count - current_count)
                except Exception:
                    pass
            try:
                attempt_dossier.cache_integrity_unrecoverable = True
                previous = list(
                    getattr(
                        attempt_dossier,
                        "cache_integrity_incident_sources",
                        [],
                    )
                    or []
                )
                attempt_dossier.cache_integrity_incident_sources = list(
                    dict.fromkeys(
                        [*previous, *parallel_cache_integrity_incidents.values()]
                    )
                )
            except Exception:
                pass

        if sample_count == 1:
            (
                ok,
                proof,
                sample_dossier,
                sample_recursive_remaining,
                sample_adaptive_recursive_remaining,
                sample_recursive_prepass_owned,
                sample_adaptive_recursive_owned,
            ) = await _run_one_sample(
                0,
                sample_temps[0],
            )
            if sample_recursive_remaining is not None:
                recursive_pass_budget_remaining = min(
                    recursive_pass_budget_remaining,
                    sample_recursive_remaining,
                )
            if sample_adaptive_recursive_remaining is not None:
                adaptive_recursive_pass_budget_remaining = min(
                    adaptive_recursive_pass_budget_remaining,
                    sample_adaptive_recursive_remaining,
                )
            _copy_dossier_contents(attempt_dossier, sample_dossier)
            if (
                not ok
                and bool(kwargs.get("adaptive_recursive_on_stall", False))
                and _current_terminal_llm_failure_reason()
                and int(
                    getattr(attempt_dossier, "tool_metrics", {}).get(
                        "mini_adaptive_recursive_fallback_suppressed_terminal_failure",
                        0,
                    )
                    or 0
                )
                <= 0
            ):
                _record_recursive_fallback_suppressed(
                    phase_label="[adaptive recursive owned by sample session]",
                    adaptive_fallback=True,
                )
            if not ok and not pre_sample_root_tactic_ran:
                ok, proof = await _run_root_tactic_prepass()
                if ok:
                    return True, proof
            # The single-sample MiniSession owns both recursive actions.  In
            # particular, no-applicable recovery arms an available adaptive
            # fallback before the session commits quiescence.  Running either
            # recursive driver here would happen after the session has ended,
            # leaving helpers, cost, and even a solved proof outside its owner.
            return ok, proof

        _trace(
            trace_prefix,
            f"=== parallel sampling {problem.theorem_name}"
            + (f" {branch_label}" if branch_label else "")
            + f" ({sample_count} samples; temps={list(sample_temps)}) ===",
        )
        tasks: List[asyncio.Task] = []
        task_index: Dict[asyncio.Task, int] = {}
        for i in range(sample_count):
            task = asyncio.create_task(
                _run_one_sample(i, sample_temps[i]),
                name=f"prove_sample_{i}",
            )
            tasks.append(task)
            task_index[task] = i

        winning_index = -1
        winning_proof: Optional[str] = None
        winning_dossier: Optional[ProofDossier] = None
        completed_dossiers: List[ProofDossier] = []
        completed_sample_records: List[Tuple[int, ProofDossier]] = []
        inflight_disproof_snapshots: Dict[int, ProofDossier] = {}
        inflight_proof_snapshots: Dict[int, ProofDossier] = {}
        inflight_conflict_snapshots: Dict[int, ProofDossier] = {}
        terminal_sample_detected = False
        failed_sample_indices: Set[int] = set()
        sample_failures: List[Dict[str, Any]] = []
        late_sample_grace_s = max(
            0.0,
            float(kwargs.get("parallel_late_sample_grace_s", 0.0) or 0.0),
        )
        late_sample_candidates_preserved = 0
        late_sample_successes_preserved = 0
        late_sample_abandoned = 0
        late_sample_grace_timeouts = 0

        def _capture_inflight_disproofs(*, exclude_index: int = -1) -> None:
            for live_index, live_dossier in tuple(
                parallel_live_sample_dossiers.items()
            ):
                if (
                    live_index == exclude_index
                    or live_index in completed_sample_indices
                ):
                    continue
                snapshot = _snapshot_parallel_live_root_disproof(live_dossier)
                if snapshot is not None:
                    inflight_disproof_snapshots[live_index] = snapshot
                proof_snapshot = _snapshot_parallel_live_root_proof(live_dossier)
                if proof_snapshot is not None:
                    inflight_proof_snapshots[live_index] = proof_snapshot
                conflict_snapshot = _snapshot_parallel_live_proof_disproof_conflict(
                    live_dossier
                )
                if conflict_snapshot is not None:
                    inflight_conflict_snapshots[live_index] = conflict_snapshot

        def _increment_parallel_metric(key: str, amount: int = 1) -> None:
            increment = getattr(attempt_dossier, "increment_tool_metric", None)
            if callable(increment):
                try:
                    increment(key, int(amount or 0))
                except Exception:
                    return

        first_completed_dossier: Optional[ProofDossier] = None
        first_completed_index = -1
        pending: Set[asyncio.Task] = set(tasks)
        try:
            while pending:
                done, pending = await asyncio.wait(
                    pending,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                for task in sorted(done, key=lambda item: task_index[item]):
                    if task.cancelled():
                        continue
                    try:
                        (
                            ok,
                            proof,
                            sample_dossier,
                            _sample_recursive_remaining,
                            _sample_adaptive_recursive_remaining,
                            _sample_recursive_prepass_owned,
                            _sample_adaptive_recursive_owned,
                        ) = task.result()
                    except Exception as exc:
                        sample_index = task_index.get(task, -1)
                        _capture_inflight_disproofs(exclude_index=winning_index)
                        if sample_index >= 0:
                            failed_sample_indices.add(sample_index)
                        sample_failures.append(
                            record_parallel_sample_failure(
                                attempt_dossier,
                                sample_index=sample_index,
                                error_kind=type(exc).__name__,
                                error=str(exc),
                                stage="result",
                            )
                        )
                        _trace(
                            trace_prefix,
                            f"sample {task.get_name()} raised: "
                            f"{type(exc).__name__}: {exc}",
                        )
                        proof_snapshot = inflight_proof_snapshots.get(sample_index)
                        conflict_snapshot = inflight_conflict_snapshots.get(
                            sample_index
                        )
                        disproof_snapshot = inflight_disproof_snapshots.get(
                            sample_index
                        )
                        if (
                            conflict_snapshot is None
                            and proof_snapshot is not None
                            and winning_dossier is None
                        ):
                            winning_index = sample_index
                            winning_proof = proof_snapshot.final_proof
                            winning_dossier = proof_snapshot
                            pending = set()
                            break
                        if (
                            conflict_snapshot is not None
                            or disproof_snapshot is not None
                        ):
                            terminal_sample_detected = True
                            pending = set()
                            break
                        continue
                    sample_index = task_index[task]
                    completed_dossiers.append(sample_dossier)
                    completed_sample_records.append((sample_index, sample_dossier))
                    completed_sample_indices.add(sample_index)
                    if first_completed_dossier is None:
                        first_completed_dossier = sample_dossier
                        first_completed_index = sample_index
                    if ok and winning_dossier is None:
                        winning_index = sample_index
                        winning_proof = proof
                        winning_dossier = sample_dossier
                        _capture_inflight_disproofs(exclude_index=winning_index)
                        pending = set()
                        break
                    if (
                        winning_dossier is None
                        and _parallel_sample_has_finalized_root_proof(sample_dossier)
                    ):
                        winning_index = sample_index
                        winning_proof = sample_dossier.final_proof
                        winning_dossier = sample_dossier
                        _capture_inflight_disproofs(exclude_index=winning_index)
                        pending = set()
                        break
                    if active_root_disproof_certificate_is_valid(
                        sample_dossier
                    ) or _parallel_sample_has_proof_disproof_conflict(sample_dossier):
                        terminal_sample_detected = True
                        _capture_inflight_disproofs(exclude_index=sample_index)
                        pending = set()
                        break
        finally:

            def _abandon_sample_tasks(sample_tasks) -> None:
                for task in sample_tasks:
                    guard = sample_guards.get(task_index.get(task, -1))
                    if guard is not None:
                        guard.abandoned = True

            current = asyncio.current_task()
            if current is not None and current.cancelling():
                _abandon_sample_tasks(tasks)
            if (
                (winning_dossier is not None or terminal_sample_detected)
                and late_sample_grace_s > 0.0
                and not (current is not None and current.cancelling())
            ):
                late_pending = {task for task in tasks if not task.done()}
                if late_pending:
                    try:
                        _done_late, pending_late = await asyncio.wait(
                            late_pending,
                            timeout=late_sample_grace_s,
                        )
                    except asyncio.CancelledError:
                        _abandon_sample_tasks(tasks)
                        for pending_task in tasks:
                            if not pending_task.done():
                                pending_task.add_done_callback(
                                    _CONSUME_SAMPLE_TASK_EXCEPTION
                                )
                                pending_task.cancel()
                        raise
                    if pending_late:
                        late_sample_grace_timeouts += 1
                        _increment_parallel_metric(
                            "mini_parallel_late_sample_grace_timeouts",
                            1,
                        )
                        _trace(
                            trace_prefix,
                            f"parallel sampling: late-sample grace expired with "
                            f"{len(pending_late)} sibling task(s) still running",
                        )
            _capture_inflight_disproofs(exclude_index=winning_index)
            for task in tasks:
                if not task.done():
                    task.cancel()
            try:
                done_drain, pending_drain = await asyncio.wait(
                    set(tasks),
                    timeout=_PARALLEL_SAMPLE_CANCEL_DRAIN_TIMEOUT_S,
                )
            except asyncio.CancelledError:
                _abandon_sample_tasks(tasks)
                for task in tasks:
                    if not task.done():
                        task.add_done_callback(_CONSUME_SAMPLE_TASK_EXCEPTION)
                        task.cancel()
                raise
            for task in done_drain:
                try:
                    result = await task
                    sample_index = task_index.get(task, -1)
                    if (
                        sample_index >= 0
                        and sample_index not in completed_sample_indices
                        and isinstance(result, tuple)
                        and len(result) >= 5
                    ):
                        (
                            ok,
                            proof,
                            sample_dossier,
                            _sample_recursive_remaining,
                            _sample_adaptive_recursive_remaining,
                            _sample_recursive_prepass_owned,
                            _sample_adaptive_recursive_owned,
                        ) = result[:7]
                        completed_dossiers.append(sample_dossier)
                        completed_sample_records.append((sample_index, sample_dossier))
                        completed_sample_indices.add(sample_index)
                        if first_completed_dossier is None:
                            first_completed_dossier = sample_dossier
                            first_completed_index = sample_index
                        if (
                            winning_dossier is not None
                            and sample_index != winning_index
                        ):
                            late_sample_candidates_preserved += 1
                            _increment_parallel_metric(
                                "mini_parallel_late_sample_candidates_preserved",
                                1,
                            )
                            if ok:
                                late_sample_successes_preserved += 1
                                _increment_parallel_metric(
                                    "mini_parallel_late_sample_successes_preserved",
                                    1,
                                )
                        if ok and winning_dossier is None:
                            winning_index = sample_index
                            winning_proof = proof
                            winning_dossier = sample_dossier
                except asyncio.CancelledError:
                    if current is not None and current.cancelling():
                        _abandon_sample_tasks(tasks)
                        for pending_task in tasks:
                            if not pending_task.done():
                                pending_task.add_done_callback(
                                    _CONSUME_SAMPLE_TASK_EXCEPTION
                                )
                                pending_task.cancel()
                        raise
                except Exception as exc:
                    sample_index = task_index.get(task, -1)
                    if (
                        sample_index not in completed_sample_indices
                        and sample_index not in failed_sample_indices
                    ):
                        if sample_index >= 0:
                            failed_sample_indices.add(sample_index)
                        sample_failures.append(
                            record_parallel_sample_failure(
                                attempt_dossier,
                                sample_index=sample_index,
                                error_kind=type(exc).__name__,
                                error=str(exc),
                                stage="drain",
                            )
                        )
                    _trace(
                        trace_prefix,
                        f"sample drain raised: {type(exc).__name__}: {exc}",
                    )
            # A sibling may commit audited terminal evidence while handling
            # the first cancellation and then resist beyond the bounded
            # drain. Snapshot at the exact event-loop ownership cutoff before
            # its guard is marked abandoned and a second cancellation lands.
            _capture_inflight_disproofs(exclude_index=winning_index)
            if pending_drain:
                if winning_dossier is not None or terminal_sample_detected:
                    late_sample_abandoned += len(pending_drain)
                    _increment_parallel_metric(
                        "mini_parallel_late_sample_abandoned",
                        len(pending_drain),
                    )
                for task in pending_drain:
                    _abandon_sample_tasks((task,))
                    task.add_done_callback(_CONSUME_SAMPLE_TASK_EXCEPTION)
                    task.cancel()
                    sample_failures.append(
                        record_parallel_sample_failure(
                            attempt_dossier,
                            sample_index=task_index.get(task, -1),
                            error_kind="Cancelled",
                            error="sample task abandoned after cancellation drain grace",
                            stage="abandoned_after_drain",
                        )
                    )
                _trace(
                    trace_prefix,
                    f"parallel sampling: abandoned {len(pending_drain)} "
                    "cancelled sample task(s) after drain grace",
                )

        _merge_parallel_sample_caches()

        if winning_dossier is not None:
            parallel_root_disproof_certificate_hashes = (
                _parallel_completed_root_disproof_certificate_hashes(
                    completed_sample_records
                )
                | _parallel_completed_root_disproof_certificate_hashes(
                    tuple(sorted(inflight_disproof_snapshots.items()))
                )
            )
            parallel_conflict_certificate_hashes: Set[str] = set()
            for _sample_index, sample_dossier in (
                *completed_sample_records,
                *tuple(sorted(inflight_conflict_snapshots.items())),
            ):
                parallel_conflict_certificate_hashes.update(
                    _parallel_proof_disproof_conflict_certificate_hashes(sample_dossier)
                )
            parallel_terminal_certificate_hashes = (
                parallel_root_disproof_certificate_hashes
                | parallel_conflict_certificate_hashes
            )
            parallel_proof_disproof_conflict = bool(
                parallel_terminal_certificate_hashes
                or any(
                    _parallel_sample_has_proof_disproof_conflict(sample_dossier)
                    for _sample_index, sample_dossier in completed_sample_records
                )
            )
            mirrored_attempt_metrics = _parallel_monotonic_metric_snapshot(
                attempt_dossier
            )
            _copy_dossier_contents(attempt_dossier, winning_dossier)
            _restore_parallel_observability_snapshot(
                attempt_dossier,
                parallel_observability_baseline,
            )
            _restore_parallel_monotonic_metric_snapshot(
                attempt_dossier,
                mirrored_attempt_metrics,
            )
            _restore_parallel_cache_integrity_observability()
            for failure in sample_failures:
                record_parallel_sample_failure(
                    attempt_dossier,
                    sample_index=int(failure.get("sample_index", -1)),
                    error_kind=str(failure.get("error_kind", "")),
                    error=str(failure.get("error", "")),
                    stage=str(failure.get("stage", "")),
                )
            _begin_parallel_falsification_conflict_receipt_scope(
                attempt_dossier,
                parallel_terminal_certificate_hashes,
            )
            retained_terminal_indices = set(inflight_disproof_snapshots) | set(
                inflight_conflict_snapshots
            )
            for sample_index, sample_dossier in completed_sample_records:
                if sample_dossier is not winning_dossier:
                    _merge_dossier_helpers(
                        attempt_dossier,
                        sample_dossier,
                        include_accepted_stubs=False,
                    )
                record = (
                    None
                    if sample_index in retained_terminal_indices
                    else _parallel_sample_proof_state_record(sample_dossier)
                )
                if record:
                    attempt_dossier.record_parallel_sample_proof_state(
                        record,
                        sample_index=sample_index,
                        role=(
                            "winner"
                            if sample_dossier is winning_dossier
                            else "completed_sibling"
                        ),
                        selected=sample_dossier is winning_dossier,
                    )
            retained_terminal_records = _parallel_authoritative_failure_records(
                (),
                disproof_snapshots=inflight_disproof_snapshots,
                conflict_snapshots=inflight_conflict_snapshots,
            )
            for sample_index, sample_dossier in retained_terminal_records:
                if sample_dossier is not winning_dossier:
                    _merge_dossier_helpers(
                        attempt_dossier,
                        sample_dossier,
                        include_accepted_stubs=False,
                    )
                record = _parallel_sample_proof_state_record(sample_dossier)
                if record:
                    attempt_dossier.record_parallel_sample_proof_state(
                        record,
                        sample_index=sample_index,
                        role="retained_terminal_sibling",
                        selected=False,
                    )
            if parallel_proof_disproof_conflict:
                conflict_recorded_by_sibling_merge = (
                    _consume_parallel_falsification_conflict_receipts(
                        attempt_dossier,
                        parallel_terminal_certificate_hashes,
                    )
                )
                _mark_parallel_proof_disproof_conflict(
                    attempt_dossier,
                    increment_metric=not conflict_recorded_by_sibling_merge,
                    certificate_hashes=tuple(parallel_terminal_certificate_hashes),
                )
            if recorder is not None and hasattr(recorder, "record_turn"):
                recorder.record_turn(
                    {
                        "phase": "parallel_sample_complete",
                        "branch_label": branch_label,
                        "samples_attempted": sample_count,
                        "samples_completed": len(completed_sample_records),
                        "terminal_evidence_retained": len(retained_terminal_records),
                        "sample_failure_count": len(sample_failures),
                        "sample_failures": list(sample_failures[:8]),
                        "late_sample_grace_s": late_sample_grace_s,
                        "late_sample_candidates_preserved": (
                            late_sample_candidates_preserved
                        ),
                        "late_sample_successes_preserved": (
                            late_sample_successes_preserved
                        ),
                        "late_sample_abandoned": late_sample_abandoned,
                        "late_sample_grace_timeouts": late_sample_grace_timeouts,
                        "winning_sample_index": winning_index,
                        "winning_temperature": (
                            sample_temps[winning_index]
                            if 0 <= winning_index < len(sample_temps)
                            else None
                        ),
                        "verdict": (
                            "parallel_sample_proof_disproof_conflict"
                            if parallel_proof_disproof_conflict
                            else "parallel_sample_won"
                        ),
                    }
                )
            if parallel_proof_disproof_conflict:
                _trace(
                    trace_prefix,
                    "=== parallel sampling: proof/disproof conflict ===",
                )
                return False, None
            _trace(
                trace_prefix,
                f"=== parallel sampling won by sample {winning_index + 1}/{sample_count} ===",
            )
            return True, winning_proof

        selected_failed_index = -1
        selected_failed_dossier = None
        selected_failed_score: Tuple[int, int, int, int, int, int] = (
            0,
            0,
            0,
            0,
            0,
            0,
        )
        authoritative_failure_records = _parallel_authoritative_failure_records(
            completed_sample_records,
            proof_snapshots=inflight_proof_snapshots,
            disproof_snapshots=inflight_disproof_snapshots,
            conflict_snapshots=inflight_conflict_snapshots,
        )
        finalized_failure_proof_by_index: Dict[int, ProofDossier] = {}
        for sample_index, sample_dossier in (
            *completed_sample_records,
            *tuple(sorted(inflight_proof_snapshots.items())),
        ):
            if _parallel_sample_has_finalized_root_proof(sample_dossier):
                finalized_failure_proof_by_index[sample_index] = sample_dossier
        finalized_failure_proof_records = sorted(
            finalized_failure_proof_by_index.items()
        )
        all_fail_negative_certificate_hashes = (
            _parallel_completed_root_disproof_certificate_hashes(
                authoritative_failure_records
            )
        )
        for _sample_index, sample_dossier in authoritative_failure_records:
            all_fail_negative_certificate_hashes.update(
                _parallel_proof_disproof_conflict_certificate_hashes(sample_dossier)
            )
        all_fail_opposite_authority_conflict = bool(
            finalized_failure_proof_records and all_fail_negative_certificate_hashes
        )
        retained_terminal_indices = (
            set(inflight_proof_snapshots)
            | set(inflight_disproof_snapshots)
            | set(inflight_conflict_snapshots)
        )
        if authoritative_failure_records:
            if finalized_failure_proof_records:
                (
                    selected_failed_index,
                    selected_failed_dossier,
                ) = min(finalized_failure_proof_records, key=lambda item: item[0])
                selected_failed_score = _parallel_failure_sample_score(
                    selected_failed_dossier
                )
            else:
                (
                    selected_failed_index,
                    selected_failed_dossier,
                    selected_failed_score,
                ) = _select_parallel_failure_primary(authoritative_failure_records)
            if selected_failed_dossier is None:
                selected_failed_index = first_completed_index
                selected_failed_dossier = first_completed_dossier
                selected_failed_score = _parallel_failure_sample_score(
                    selected_failed_dossier
                )
            mirrored_attempt_metrics = _parallel_monotonic_metric_snapshot(
                attempt_dossier
            )
            _copy_dossier_contents(attempt_dossier, selected_failed_dossier)
            _remember_terminal_llm_failure(
                terminal_llm_failure_reason,
                kind=terminal_llm_failure_kind,
            )
            _restore_parallel_observability_snapshot(
                attempt_dossier,
                parallel_observability_baseline,
            )
            _restore_parallel_monotonic_metric_snapshot(
                attempt_dossier,
                mirrored_attempt_metrics,
            )
            _restore_parallel_cache_integrity_observability()
            for failure in sample_failures:
                record_parallel_sample_failure(
                    attempt_dossier,
                    sample_index=int(failure.get("sample_index", -1)),
                    error_kind=str(failure.get("error_kind", "")),
                    error=str(failure.get("error", "")),
                    stage=str(failure.get("stage", "")),
                )
            for sample_index, sample_dossier in authoritative_failure_records:
                record = _parallel_sample_proof_state_record(sample_dossier)
                if record:
                    attempt_dossier.record_parallel_sample_proof_state(
                        record,
                        sample_index=sample_index,
                        role=(
                            "all_fail_primary"
                            if sample_dossier is selected_failed_dossier
                            else (
                                "retained_terminal_sibling"
                                if sample_index in retained_terminal_indices
                                else "all_fail_sibling"
                            )
                        ),
                        selected=sample_dossier is selected_failed_dossier,
                    )
            structural_fanin: List[Dict[str, Any]] = []
            for sample_index, sample_dossier in completed_sample_records:
                if sample_dossier is selected_failed_dossier:
                    continue
                _merge_dossier_helpers(
                    attempt_dossier,
                    sample_dossier,
                    include_accepted_stubs=False,
                    include_proof_ideas=False,
                )
                structural_record = _merge_parallel_sample_structural_progress(
                    attempt_dossier,
                    sample_dossier,
                    sample_index=sample_index,
                )
                if any(int(value or 0) for value in structural_record.values()):
                    structural_fanin.append(
                        {
                            "sample_index": int(sample_index),
                            **structural_record,
                        }
                    )
            for sample_index, sample_dossier in authoritative_failure_records:
                if (
                    sample_dossier is selected_failed_dossier
                    or sample_index not in retained_terminal_indices
                ):
                    continue
                _merge_dossier_helpers(
                    attempt_dossier,
                    sample_dossier,
                    include_accepted_stubs=False,
                    include_proof_ideas=False,
                )
            if all_fail_opposite_authority_conflict:
                _mark_parallel_proof_disproof_conflict(
                    attempt_dossier,
                    certificate_hashes=tuple(
                        sorted(all_fail_negative_certificate_hashes)
                    ),
                )
        else:
            record_parallel_samples_zero_completed(attempt_dossier)
            structural_fanin = []

        parallel_root_terminal_kind = _resolve_parallel_root_disproof_terminal_state(
            attempt_dossier
        )
        parallel_root_disproved = parallel_root_terminal_kind == "mathematical_disproof"
        parallel_recovered_root_proof = bool(
            not parallel_root_terminal_kind
            and _parallel_sample_has_finalized_root_proof(attempt_dossier)
        )

        if recorder is not None and hasattr(recorder, "record_turn"):
            recorder.record_turn(
                {
                    "phase": "parallel_sample_complete",
                    "branch_label": branch_label,
                    "samples_attempted": sample_count,
                    "samples_completed": len(completed_sample_records),
                    "terminal_evidence_retained": len(retained_terminal_indices),
                    "zero_task_results": not completed_sample_records,
                    "sample_failure_count": len(sample_failures),
                    "sample_failures": list(sample_failures[:8]),
                    "zero_completed": not authoritative_failure_records,
                    "winning_sample_index": -1,
                    "winning_temperature": None,
                    "selected_failed_sample_index": selected_failed_index,
                    "selected_failed_score": list(selected_failed_score),
                    "structural_fanin": list(structural_fanin[:8]),
                    "verdict": (
                        "parallel_sample_disproved"
                        if parallel_root_disproved
                        else (
                            "parallel_sample_proof_disproof_conflict"
                            if parallel_root_terminal_kind == "proof_disproof_conflict"
                            else (
                                "parallel_sample_recovered_root_proof"
                                if parallel_recovered_root_proof
                                else "parallel_sample_all_failed"
                            )
                        )
                    ),
                }
            )
        if parallel_root_terminal_kind:
            _trace(
                trace_prefix,
                (
                    "=== parallel sampling: root disproved by audited Lean certificate ==="
                    if parallel_root_disproved
                    else "=== parallel sampling: proof/disproof conflict ==="
                ),
            )
            return False, None
        if parallel_recovered_root_proof:
            _trace(
                trace_prefix,
                "=== parallel sampling: recovered finalized root proof from failed sample ===",
            )
            return True, str(attempt_dossier.final_proof or "")
        _trace(
            trace_prefix,
            f"=== parallel sampling: all {sample_count} samples failed ===",
        )
        _resolve_post_fanin_theory_environment()
        if not pre_sample_root_tactic_ran:
            ok, proof = await _run_root_tactic_prepass(
                effective_lean_preamble=post_fanin_lean_preamble,
            )
            if ok:
                return True, proof
        post_fanin_primary_recursive_enabled = bool(
            bool(kwargs.get("mini_recursive_enabled", False))
            and recursive_pass_budget_remaining > 0
        )
        post_fanin_adaptive_recursive_enabled = bool(
            bool(kwargs.get("adaptive_recursive_on_stall", False))
            and adaptive_recursive_pass_budget_remaining > 0
        )
        post_fanin_recursive_enabled = bool(
            post_fanin_primary_recursive_enabled
            or post_fanin_adaptive_recursive_enabled
        )
        if post_fanin_recursive_enabled:
            if _current_terminal_llm_failure_reason():
                _record_recursive_fallback_suppressed(
                    phase_label="[parallel fan-in recursive container]",
                    adaptive_fallback=bool(
                        post_fanin_adaptive_recursive_enabled
                        and not post_fanin_primary_recursive_enabled
                    ),
                )
            else:
                ok, proof = await _run_post_fanin_recursive_session()
                if ok:
                    return True, proof
        return False, None

    premise_block = ""
    premise_names: List[str] = []
    premise_retrieval_record: Dict[str, Any] = {}
    (
        premise_block,
        premise_names,
        premise_retrieval_record,
    ) = await _retrieve_startup_premise_context(
        target_dossier=dossier,
        target_searcher=searcher,
        goal_statement=premise_goal_statement,
        event_recorder=recorder,
        event_trace_prefix=trace_prefix,
    )

    ok, proof = await _run_attempt(
        llm_preamble=llm_preamble,
        lean_preamble=lean_preamble,
        attempt_dossier=dossier,
        initial_context="",
        premise_block=premise_block,
        premise_names=premise_names,
        premise_retrieval_record=premise_retrieval_record,
    )
    if ok:
        return True, proof
    return False, None


def _register_child_session_tactic_actions(
    session: MiniSession,
    *,
    max_turns: int,
    kwargs: Dict[str, Any],
) -> None:
    timeout_s = float(
        kwargs.get(
            "proof_state_child_tactic_timeout_s",
            DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        )
        or 0.0
    )
    max_nodes = int(kwargs.get("proof_state_child_goal_limit", 3) or 0)
    max_candidates = int(kwargs.get("proof_state_child_tactic_max_candidates", 32) or 0)
    max_decl_applications = int(
        kwargs.get("proof_state_decl_application_limit", 6) or 0
    )
    batch_parallelism = int(kwargs.get("proof_state_batch_parallelism", 1) or 1)
    repair_top_k = int(kwargs.get("repair_retrieval_top_k", 6) or 0)
    budget_turns = max(1, int(max_turns or 1))

    session.register(
        CastNormalizationAction(
            timeout_s=max(1.0, min(12.0, timeout_s or 12.0)),
            max_candidates=max(8, min(24, max_candidates or 16)),
        )
    )
    session.set_budget(
        "cast_normalization",
        ActionBudget(max_invocations=budget_turns, max_total_seconds=0.0),
    )
    session.register(
        FinsetReindexingAction(
            timeout_s=max(1.0, min(12.0, timeout_s or 12.0)),
            max_candidates=max(8, min(24, max_candidates or 18)),
        )
    )
    session.set_budget(
        "finset_reindexing",
        ActionBudget(max_invocations=budget_turns, max_total_seconds=0.0),
    )
    if (
        bool(kwargs.get("formal_state_search_enabled", False))
        and float(
            kwargs.get(
                "formal_state_search_timeout_s",
                DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
            )
            or 0.0
        )
        > 0.0
        and session.registered_action("tactic_close") is None
    ):
        session.register(
            RootTacticCloseAction(
                phase="root_tactic_prepass",
                timeout_s=float(kwargs.get("root_tactic_timeout_s", timeout_s) or 0.0),
                max_candidates=int(
                    kwargs.get("root_tactic_max_candidates", max_candidates) or 0
                ),
            )
        )
        session.set_budget(
            "tactic_close",
            ActionBudget(
                max_invocations=max(2, budget_turns * 2),
                max_total_seconds=60.0,
            ),
        )
    session.register(InterTurnAssemblyAction(timeout_s=timeout_s, max_nodes=max_nodes))
    session.set_budget(
        "inter_turn_assembly",
        ActionBudget(max_invocations=max(2, budget_turns * 2), max_total_seconds=90.0),
    )
    session.register(
        GraphRouteAssemblyAction(
            max_routes=max_nodes,
            root_tactic_timeout_s=float(
                kwargs.get("root_tactic_timeout_s", timeout_s) or 0.0
            ),
            root_tactic_max_candidates=int(
                kwargs.get("root_tactic_max_candidates", max_candidates) or 0
            ),
        )
    )
    session.set_budget(
        "graph_route_assembly",
        ActionBudget(
            max_invocations=max(2, budget_turns * 2),
            max_total_seconds=_route_assembly_budget_seconds(
                timeout_s=float(kwargs.get("root_tactic_timeout_s", timeout_s) or 0.0),
                max_invocations=max(2, budget_turns * 2),
            ),
        ),
    )
    session.register(GraphNativeShortcutAction())
    session.set_budget(
        "graph_native_shortcut",
        ActionBudget(max_invocations=max(2, budget_turns * 2), max_total_seconds=30.0),
    )
    session.register(
        HelperOnlySalvageAction(
            timeout_s=timeout_s,
            max_nodes=max_nodes,
            batch_parallelism=batch_parallelism,
        )
    )
    session.set_budget(
        "helper_only_salvage",
        ActionBudget(max_invocations=budget_turns, max_total_seconds=120.0),
    )
    # Post-failure cascade is owned by ConversationTurnAction. Child sessions
    # keep the budget bucket because the inline cascade charges it directly.
    session.set_budget(
        "post_lean_failure",
        ActionBudget(max_invocations=budget_turns, max_total_seconds=300.0),
    )
    if (
        bool(kwargs.get("proof_state_retrieval_enabled", False))
        and bool(kwargs.get("repair_retrieval_enabled", True))
        and repair_top_k > 0
    ):
        session.register(
            ProofStateRetrievalAction(
                max_nodes=max_nodes,
                max_results=repair_top_k,
            )
        )
        session.set_budget(
            "proof_state_retrieval",
            ActionBudget(max_invocations=budget_turns, max_total_seconds=60.0),
        )
    from ensemble_prover.mini_formal_state_search import FormalStateSearchConfig

    formal_search_config = FormalStateSearchConfig(
        enabled=bool(kwargs.get("formal_state_search_enabled", False)),
        total_timeout_s=float(
            kwargs.get(
                "formal_state_search_timeout_s",
                DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
            )
            or 0.0
        ),
        operation_timeout_s=float(
            kwargs.get(
                "formal_state_search_operation_timeout_s",
                DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
            )
            or 0.0
        ),
        provider_timeout_s=float(
            kwargs.get(
                "formal_state_search_provider_timeout_s",
                DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
            )
            or 0.0
        ),
        provider_max_tokens=max(
            0,
            int(
                kwargs.get(
                    "formal_state_search_provider_max_tokens",
                    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
                )
                or 0
            ),
        ),
        provider_reasoning_effort=str(
            kwargs.get(
                "formal_state_search_provider_reasoning_effort",
                DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
            )
            or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
        ),
        provider_max_attempts=max(
            1,
            int(kwargs.get("formal_state_search_provider_max_attempts", 2) or 1),
        ),
        provider_retry_backoff_s=max(
            0.0,
            float(
                kwargs.get("formal_state_search_provider_retry_backoff_s", 5.0) or 0.0
            ),
        ),
        beam_width=max(1, int(kwargs.get("formal_state_search_beam_width", 4) or 1)),
        max_steps=max(1, int(kwargs.get("formal_state_search_max_steps", 8) or 1)),
        max_candidates_per_state=max(
            1, int(kwargs.get("formal_state_search_max_candidates", 6) or 1)
        ),
        backtrack_limit=max(
            0, int(kwargs.get("formal_state_search_backtrack_limit", 8) or 0)
        ),
        max_no_improvement_quanta=max(
            0,
            int(kwargs.get("formal_state_search_max_no_improvement_quanta", 6) or 0),
        ),
    )

    child_closure_action = ChildClosureAction(
        timeout_s=timeout_s,
        max_candidates=max_candidates,
        max_nodes=max_nodes,
        max_decl_applications=max_decl_applications,
        batch_parallelism=batch_parallelism,
        formal_search_config=None,
    )
    session.register(child_closure_action)
    session.set_budget(
        "child_closure",
        ActionBudget(
            max_invocations=max(
                child_closure_action.minimum_invocation_budget(),
                budget_turns,
            ),
            max_total_seconds=0.0,
        ),
    )
    if formal_search_config.normalized().enabled:
        session.register(FormalStateSearchAction(config=formal_search_config))
        session.set_budget(
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
                max_aggregate_seconds=_formal_state_search_aggregate_seconds(
                    formal_search_config
                ),
            ),
        )
    session.register(
        LemmaDagDecomposeAction(
            timeout_s=timeout_s,
            root_tactic_max_candidates=max_candidates,
        )
    )
    session.set_budget(
        "lemma_dag_decompose",
        ActionBudget(max_invocations=budget_turns, max_total_seconds=0.0),
    )


def _register_child_graph_recursive_decompose_action(
    session: MiniSession,
    *,
    max_turns: int,
    kwargs: Dict[str, Any],
    max_recursion_depth: int,
) -> None:
    cfg = kwargs.get("config")
    if cfg is None or session.proof_state is None:
        return
    current_depth = max(0, int(getattr(session, "recursion_depth", 0) or 0))
    if max_recursion_depth > 0 and current_depth >= max_recursion_depth:
        return
    remaining_depth = (
        max(1, max_recursion_depth - current_depth)
        if max_recursion_depth > 0
        else GraphRecursiveDecomposeAction.DEFAULT_MAX_INVOCATIONS
    )
    max_invocations = max(
        1,
        min(
            GraphRecursiveDecomposeAction.DEFAULT_MAX_INVOCATIONS,
            max(1, int(max_turns or 1)),
        ),
    )
    session.register(
        GraphRecursiveDecomposeAction(
            config=cfg,
            run_conversation_fn=_bind_theory_parent_callback(
                session,
                formal_state_search_enabled=bool(
                    kwargs.get("formal_state_search_enabled", False)
                ),
                formal_state_search_timeout_s=float(
                    kwargs.get(
                        "formal_state_search_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                    )
                    or 0.0
                ),
                formal_state_search_operation_timeout_s=float(
                    kwargs.get(
                        "formal_state_search_operation_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
                    )
                    or 0.0
                ),
                formal_state_search_provider_timeout_s=float(
                    kwargs.get(
                        "formal_state_search_provider_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
                    )
                    or 0.0
                ),
                formal_state_search_provider_max_tokens=max(
                    0,
                    int(
                        kwargs.get(
                            "formal_state_search_provider_max_tokens",
                            DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
                        )
                        or 0
                    ),
                ),
                formal_state_search_provider_reasoning_effort=str(
                    kwargs.get(
                        "formal_state_search_provider_reasoning_effort",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
                    )
                    or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
                ),
                formal_state_search_provider_max_attempts=max(
                    1,
                    int(
                        kwargs.get("formal_state_search_provider_max_attempts", 2) or 1
                    ),
                ),
                formal_state_search_provider_retry_backoff_s=max(
                    0.0,
                    float(
                        kwargs.get(
                            "formal_state_search_provider_retry_backoff_s",
                            5.0,
                        )
                        or 0.0
                    ),
                ),
                formal_state_search_beam_width=int(
                    kwargs.get("formal_state_search_beam_width", 4) or 1
                ),
                formal_state_search_max_steps=int(
                    kwargs.get("formal_state_search_max_steps", 8) or 1
                ),
                formal_state_search_max_candidates=int(
                    kwargs.get("formal_state_search_max_candidates", 6) or 1
                ),
                formal_state_search_backtrack_limit=int(
                    kwargs.get("formal_state_search_backtrack_limit", 8) or 0
                ),
                formal_state_search_max_no_improvement_quanta=max(
                    0,
                    int(
                        kwargs.get("formal_state_search_max_no_improvement_quanta", 6)
                        or 0
                    ),
                ),
            ),
            max_tool_calls_per_turn=int(kwargs.get("max_tool_calls_per_turn", 10) or 0),
            lean_check_tool_enabled=bool(kwargs.get("lean_check_tool_enabled", True)),
            try_lean_tool_enabled=bool(kwargs.get("try_lean_tool_enabled", True)),
            compute_examples_tool_enabled=_kwargs_compute_examples_tool_enabled(kwargs),
            apply_decl_to_goal_tool_enabled=bool(
                kwargs.get("apply_decl_to_goal_tool_enabled", True)
            ),
            raw_feedback=bool(kwargs.get("raw_feedback", False)),
            repair_retrieval_enabled=bool(kwargs.get("repair_retrieval_enabled", True)),
            repair_retrieval_top_k=int(kwargs.get("repair_retrieval_top_k", 6) or 0),
            proof_state_child_tactics_enabled=bool(
                kwargs.get("proof_state_child_tactics_enabled", False)
            ),
            proof_state_child_tactic_timeout_s=float(
                kwargs.get(
                    "proof_state_child_tactic_timeout_s",
                    DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                )
                or 0.0
            ),
            proof_state_child_tactic_max_candidates=int(
                kwargs.get("proof_state_child_tactic_max_candidates", 32) or 0
            ),
            root_tactic_timeout_s=float(
                kwargs.get("root_tactic_timeout_s", 40.0) or 0.0
            ),
            root_tactic_max_candidates=int(
                kwargs.get("root_tactic_max_candidates", 64) or 0
            ),
            proof_state_child_goal_limit=int(
                kwargs.get("proof_state_child_goal_limit", 3) or 0
            ),
            proof_state_decl_application_limit=int(
                kwargs.get("proof_state_decl_application_limit", 6) or 0
            ),
            proof_state_batch_parallelism=int(
                kwargs.get("proof_state_batch_parallelism", 1) or 1
            ),
            max_recursion_depth=remaining_depth,
            max_invocations=max_invocations,
        )
    )
    session.set_budget(
        "graph_recursive_decompose",
        ActionBudget(max_invocations=max_invocations, max_total_seconds=0.0),
    )


class _DeferredTheoryPromotion:
    """Idempotent commit handle for a recursively discovered theory context.

    The child callback prepares only immutable provenance.  The recursive
    driver owns the acceptance transaction: first replay the candidate proof
    in the child's exact Lean preamble, then invoke this handle, then admit
    the helper. Keeping the handle synchronous and lock-free also avoids
    introducing another fragile runtime object.
    """

    __slots__ = (
        "_before",
        "_bundle_ids",
        "_called",
        "_committed",
        "_parent",
        "_rolled_back",
    )

    def __init__(self, parent: Any, bundle_ids: Sequence[str]) -> None:
        self._parent = parent
        self._bundle_ids = tuple(
            dict.fromkeys(
                str(bundle_id or "").strip()
                for bundle_id in bundle_ids
                if str(bundle_id or "").strip()
            )
        )
        self._called = False
        self._committed = False
        self._rolled_back = False
        self._before: Any = None

    def __copy__(self) -> "_DeferredTheoryPromotion":
        return self

    def __deepcopy__(
        self,
        memo: Dict[int, Any],
    ) -> "_DeferredTheoryPromotion":
        # This object is the single transaction authority for one prepared
        # theory promotion.  A workspace copy must neither walk into the live
        # parent session nor duplicate the commit/rollback state.
        memo[id(self)] = self
        return self

    def _capture(self) -> Any:
        capture = getattr(
            self._parent,
            "_capture_theory_installation_state",
            None,
        )
        if callable(capture):
            return ("native", capture())
        conv = getattr(self._parent, "conv", None)
        dossier = getattr(self._parent, "dossier", None)
        searcher = getattr(self._parent, "searcher", None)
        active_ids = tuple(
            getattr(self._parent, "theory_imported_bundle_ids", ()) or ()
        )
        active_getter = getattr(searcher, "active_bundle_ids", None)
        if callable(active_getter):
            try:
                active_ids = tuple(active_getter() or ())
            except Exception:
                pass
        return (
            "generic",
            {
                "theory_context_pair": getattr(
                    self._parent, "theory_context_pair", None
                ),
                "theory_imported_bundle_ids": tuple(
                    getattr(
                        self._parent,
                        "theory_imported_bundle_ids",
                        (),
                    )
                    or ()
                ),
                "theory_snapshot": copy.deepcopy(
                    tuple(getattr(self._parent, "theory_snapshot", ()) or ())
                ),
                "conv_preamble": str(getattr(conv, "preamble", "") or ""),
                "conv_lean_preamble": str(getattr(conv, "lean_preamble", "") or ""),
                "dossier_current_lean_environment_hash": str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ),
                "dossier_lean_environment_ancestor_hashes": copy.deepcopy(
                    getattr(
                        dossier,
                        "lean_environment_ancestor_hashes",
                        {},
                    )
                    or {}
                ),
                "searcher_active_bundle_ids": active_ids,
            },
        )

    def _restore(self) -> None:
        if self._before is None:
            return
        kind, state = self._before
        if kind == "native":
            restore = getattr(
                self._parent,
                "_restore_theory_installation_state",
                None,
            )
            if not callable(restore):
                raise RuntimeError("theory promotion rollback hook disappeared")
            restore(state)
            return
        self._parent.theory_context_pair = state.get("theory_context_pair")
        self._parent.theory_imported_bundle_ids = tuple(
            state.get("theory_imported_bundle_ids") or ()
        )
        self._parent.theory_snapshot = copy.deepcopy(
            tuple(state.get("theory_snapshot") or ())
        )
        conv = getattr(self._parent, "conv", None)
        if conv is not None:
            conv.preamble = str(state.get("conv_preamble") or "")
            conv.lean_preamble = str(state.get("conv_lean_preamble") or "")
        dossier = getattr(self._parent, "dossier", None)
        if dossier is not None:
            dossier.current_lean_environment_hash = str(
                state.get("dossier_current_lean_environment_hash") or ""
            )
            dossier.lean_environment_ancestor_hashes = copy.deepcopy(
                state.get("dossier_lean_environment_ancestor_hashes") or {}
            )
        set_active_bundle_ids = getattr(
            getattr(self._parent, "searcher", None),
            "set_active_bundle_ids",
            None,
        )
        if callable(set_active_bundle_ids):
            set_active_bundle_ids(tuple(state.get("searcher_active_bundle_ids") or ()))

    def __call__(self) -> bool:
        if self._called:
            return self._committed
        self._called = True
        self._before = self._capture()
        installer = getattr(self._parent, "install_theory_bundles", None)
        if not callable(installer):
            self._restore()
            self._rolled_back = True
            return False
        try:
            result = installer(self._bundle_ids)
        except Exception as install_error:
            try:
                self._restore()
            except BaseException as rollback_error:
                install_error.add_note(
                    "theory installation rollback also failed: "
                    f"{type(rollback_error).__name__}: {rollback_error}"
                )
                raise install_error from rollback_error
            self._rolled_back = True
            return False
        if result is not False:
            self._committed = True
            return True
        # ``MiniSession.install_theory_bundles`` returns ``False`` both for a
        # real preparation failure and for an already-current snapshot.  The
        # latter is a successful idempotent commit, not a proof rejection.
        active = {
            str(bundle_id or "").strip()
            for bundle_id in tuple(
                getattr(self._parent, "theory_imported_bundle_ids", ()) or ()
            )
            if str(bundle_id or "").strip()
        }
        self._committed = all(bundle_id in active for bundle_id in self._bundle_ids)
        if not self._committed:
            self._restore()
            self._rolled_back = True
        return self._committed

    def rollback(self) -> bool:
        """Undo a successful commit if later helper admission aborts."""

        if self._rolled_back or not self._called:
            return True
        self._restore()
        self._rolled_back = True
        self._committed = False
        return True


async def _mini_session_run_conversation_callback(
    **kwargs: Any,
) -> Tuple[bool, Optional[str]]:
    """Run a mini-recursive child conversation through MiniSession actions."""

    conv = kwargs.get("conv")
    client = kwargs.get("client") or kwargs.get("prover_client")
    lean = kwargs.get("lean")
    if conv is None or client is None or lean is None:
        return False, None
    theory_parent_session = kwargs.get("theory_parent_session")
    from .searcher_context import fork_searcher_context

    theory_library = getattr(theory_parent_session, "theory_library", None)
    parent_searcher = kwargs.get("searcher")
    if parent_searcher is None:
        parent_searcher = getattr(theory_parent_session, "searcher", None)
    child_searcher = fork_searcher_context(
        parent_searcher,
        theory_enabled=bool(
            theory_library is not None
            and getattr(theory_library, "mode", "off") != "off"
        ),
    )

    max_turns = max(1, int(kwargs.get("max_turns", 1) or 1))
    recursive_max_elapsed_s = max(
        0.0,
        float(kwargs.get("recursive_conversation_max_elapsed_s", 0.0) or 0.0),
    )
    speculative_operational_probe = bool(
        kwargs.get("speculative_root_close_operational_probe", False)
    )
    raw_child_tool_cap = max(
        0,
        int(kwargs.get("recursive_conversation_max_tool_calls", 10) or 0),
    )
    child_tool_calls_per_turn = max(
        0,
        int(kwargs.get("max_tool_calls_per_turn", 10) or 0),
    )
    if raw_child_tool_cap > 0 and child_tool_calls_per_turn > 0:
        child_tool_calls_per_turn = min(
            child_tool_calls_per_turn,
            raw_child_tool_cap,
        )
    dossier = kwargs.get("dossier")
    role = str(getattr(conv, "role", "") or "prove")
    theorem_name = (
        str(getattr(dossier, "theorem_name", "") or "").strip()
        or f"mini_recursive_{role}"
    )
    raw_max_recursion_depth = kwargs.get("recursive_helper_max_depth", 3)
    max_recursion_depth = max(
        0,
        int(raw_max_recursion_depth if raw_max_recursion_depth is not None else 3),
    )
    problem = SimpleNamespace(
        theorem_name=theorem_name,
        statement_type=str(getattr(conv, "goal_statement", "") or ""),
        docstring=str(getattr(conv, "problem_text", "") or ""),
        preamble=str(getattr(conv, "preamble", "") or ""),
        lean_preamble=str(
            getattr(conv, "lean_preamble", None) or getattr(conv, "preamble", "") or ""
        ),
        solution_comment="",
    )
    session = MiniSession(
        problem=problem,
        dossier=dossier,
        proof_state=kwargs.get("proof_state"),
        proof_cache=kwargs.get("proof_cache"),
        conv=conv,
        lean=lean,
        prover_client=client,
        refiner_client=kwargs.get("refiner_client"),
        searcher=child_searcher,
        recorder=kwargs.get("recorder"),
        cost_controller=kwargs.get("cost_controller"),
        trace_prefix=str(kwargs.get("trace_prefix") or ""),
        max_iterations=max(4, max_turns * 6 + 4),
        recursive_pass_budget_remaining=0,
        recursion_depth=max(0, int(kwargs.get("recursion_depth", 0) or 0)),
        max_recursion_depth=max_recursion_depth,
        scope="subgoal",
        planner_split_scheduler_owner=False,
        parent=(
            theory_parent_session
            if isinstance(theory_parent_session, MiniSession)
            else None
        ),
        # Inherit parent's strict-progress accounting so recursive
        # children share the soft-progress streak semantics. Without
        # this, deep decomposition chains (where the swamp pathology
        # actually lives) would silently run with strict mode off.
        # Match the top-level default in prove_problem_via_session (True).
        strict_progress_accounting=bool(kwargs.get("strict_progress_accounting", True)),
        max_soft_progress_streak=max(
            0, int(kwargs.get("soft_progress_streak_cap", 4) or 0)
        ),
        theory_library=theory_library,
        theory_candidate_builder=getattr(
            theory_parent_session, "theory_candidate_builder", None
        ),
        theory_context_pair=getattr(theory_parent_session, "theory_context_pair", None),
        theory_domain=str(
            getattr(
                theory_parent_session,
                "theory_domain",
                "general mathematics",
            )
            or "general mathematics"
        ),
        theory_default_imports=tuple(
            getattr(theory_parent_session, "theory_default_imports", ("Mathlib",))
            or ("Mathlib",)
        ),
        theory_imported_bundle_ids=tuple(
            getattr(theory_parent_session, "theory_imported_bundle_ids", ()) or ()
        ),
        theory_snapshot=tuple(
            getattr(theory_parent_session, "theory_snapshot", ()) or ()
        ),
        # Recursive claim turns are an explicitly bounded action.  Repair and
        # recovery paths may preserve state, but cannot mint extra turns.
        conversation_budget_topups_enabled=False,
    )
    session._recursive_paid_no_artifact_attempt_count = 0
    session._recursive_paid_no_artifact_provider_calls_applied = 0
    session._recursive_paid_no_artifact_provider_dispatches_applied = 0
    recursive_session_ref = weakref.ref(session)

    def _observe_recursive_paid_no_artifact(outcome: Any) -> None:
        observed_session = recursive_session_ref()
        if observed_session is None:
            return
        metadata = dict(getattr(outcome, "metadata", {}) or {})
        completed = max(0, int(metadata.get("provider_calls_completed", 0) or 0))
        dispatched = max(
            0,
            int(metadata.get("provider_dispatches_started", 0) or 0),
        )
        # Mark all provider exposure represented by this about-to-be-applied
        # outcome. Cooperative quantum yields and productive turns are not
        # failed attempts, but their settled calls must not masquerade as a
        # later cancellation-time dispatch.
        observed_session._recursive_paid_no_artifact_provider_calls_applied = (
            max(
                0,
                int(
                    getattr(
                        observed_session,
                        "provider_calls_completed_total",
                        0,
                    )
                    or 0
                ),
            )
            + completed
        )
        observed_session._recursive_paid_no_artifact_provider_dispatches_applied = (
            max(
                0,
                int(
                    getattr(
                        observed_session,
                        "provider_dispatches_started_total",
                        0,
                    )
                    or 0
                ),
            )
            + dispatched
        )
        if not str(getattr(outcome, "action_id", "") or "").startswith(
            "conversation_turn_"
        ):
            return
        if str(metadata.get("llm_failure_kind") or "").strip() not in (
            _RECURSIVE_PAID_NO_ARTIFACT_KINDS
        ):
            return
        if not bool(metadata.get("llm_retryable", False)):
            return
        if completed <= 0 and dispatched <= 0:
            return
        observed_session._recursive_paid_no_artifact_attempt_count += 1

    session._recursive_paid_no_artifact_observer = _observe_recursive_paid_no_artifact
    recursive_lane_owner = kwargs.get("recursive_lane_owner") or theory_parent_session
    if recursive_lane_owner is not None:
        session._static_action_receipt_authority = recursive_lane_owner
        session._recursive_lane_authority = recursive_lane_owner
    lane_ledger = _recursive_conversation_lane_ledger(recursive_lane_owner)
    lane_token = ""
    lane_allowance = 0
    lane_key = ""

    def _record_lane_exhausted() -> Tuple[bool, Optional[str]]:
        record = {
            "phase": "recursive_conversation_lane",
            "role": role,
            "theorem_name": theorem_name,
            "lane_key_hash": lane_key,
            "verdict": "recursive_conversation_lane_exhausted_before_dispatch",
        }
        event = getattr(recursive_lane_owner, "_record_event", None)
        if callable(event):
            try:
                event(record)
            except Exception:
                pass
        recorder = kwargs.get("recorder")
        record_turn = getattr(recorder, "record_turn", None)
        if callable(record_turn):
            try:
                record_turn(record)
            except Exception:
                pass
        setattr(conv, "_last_run_turns_used", 0)
        return False, None

    if lane_ledger is not None:
        lane_key = _recursive_conversation_lane_key(
            conv=conv,
            client=client,
            lean=lean,
            dossier=dossier,
            role=role,
            max_tool_calls_per_turn=child_tool_calls_per_turn,
            max_turns=max_turns,
            temperature_override=kwargs.get("temperature_override"),
            mini_phase_temperatures=kwargs.get("mini_phase_temperatures"),
            recursive_max_elapsed_s=recursive_max_elapsed_s,
            execution_policy={
                "lean_check_tool_enabled": bool(
                    kwargs.get("lean_check_tool_enabled", True)
                ),
                "try_lean_tool_enabled": bool(
                    kwargs.get("try_lean_tool_enabled", True)
                ),
                "compute_examples_tool_enabled": (
                    _kwargs_compute_examples_tool_enabled(kwargs)
                ),
                "apply_decl_to_goal_tool_enabled": bool(
                    kwargs.get("apply_decl_to_goal_tool_enabled", True)
                ),
                "proof_state_child_tactics_enabled": bool(
                    kwargs.get("proof_state_child_tactics_enabled", False)
                ),
                "proof_state_child_tactic_timeout_s": float(
                    kwargs.get(
                        "proof_state_child_tactic_timeout_s",
                        DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                    )
                    or 0.0
                ),
                "proof_state_child_tactic_max_candidates": int(
                    kwargs.get("proof_state_child_tactic_max_candidates", 32) or 0
                ),
                "proof_state_child_goal_limit": int(
                    kwargs.get("proof_state_child_goal_limit", 3) or 0
                ),
                "proof_state_decl_application_limit": int(
                    kwargs.get("proof_state_decl_application_limit", 6) or 0
                ),
                "proof_state_batch_parallelism": int(
                    kwargs.get("proof_state_batch_parallelism", 1) or 1
                ),
                "proof_state_retrieval_enabled": bool(
                    kwargs.get("proof_state_retrieval_enabled", False)
                ),
                "root_tactic_timeout_s": float(
                    kwargs.get(
                        "root_tactic_timeout_s",
                        kwargs.get(
                            "proof_state_child_tactic_timeout_s",
                            DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                        ),
                    )
                    or 0.0
                ),
                "root_tactic_max_candidates": int(
                    kwargs.get(
                        "root_tactic_max_candidates",
                        kwargs.get(
                            "proof_state_child_tactic_max_candidates",
                            32,
                        ),
                    )
                    or 0
                ),
                "formal_state_search_enabled": bool(
                    kwargs.get("formal_state_search_enabled", False)
                ),
                "speculative_root_close_operational_probe": (
                    speculative_operational_probe
                ),
                "provider_dispatch_limit": (
                    1 if speculative_operational_probe else 0
                ),
                "formal_state_search_timeout_s": float(
                    kwargs.get(
                        "formal_state_search_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                    )
                    or 0.0
                ),
                "formal_state_search_operation_timeout_s": float(
                    kwargs.get(
                        "formal_state_search_operation_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
                    )
                    or 0.0
                ),
                "formal_state_search_provider_timeout_s": float(
                    kwargs.get(
                        "formal_state_search_provider_timeout_s",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
                    )
                    or 0.0
                ),
                "formal_state_search_provider_max_tokens": max(
                    0,
                    int(
                        kwargs.get(
                            "formal_state_search_provider_max_tokens",
                            DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
                        )
                        or 0
                    ),
                ),
                "formal_state_search_provider_reasoning_effort": str(
                    kwargs.get(
                        "formal_state_search_provider_reasoning_effort",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
                    )
                    or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
                ),
                "formal_state_search_provider_max_attempts": max(
                    1,
                    int(
                        kwargs.get(
                            "formal_state_search_provider_max_attempts",
                            2,
                        )
                        or 1
                    ),
                ),
                "formal_state_search_provider_retry_backoff_s": max(
                    0.0,
                    float(
                        kwargs.get(
                            "formal_state_search_provider_retry_backoff_s",
                            5.0,
                        )
                        or 0.0
                    ),
                ),
                "formal_state_search_beam_width": max(
                    1,
                    int(kwargs.get("formal_state_search_beam_width", 4) or 1),
                ),
                "formal_state_search_max_steps": max(
                    1,
                    int(kwargs.get("formal_state_search_max_steps", 8) or 1),
                ),
                "formal_state_search_max_candidates": max(
                    1,
                    int(kwargs.get("formal_state_search_max_candidates", 6) or 1),
                ),
                "formal_state_search_backtrack_limit": max(
                    0,
                    int(kwargs.get("formal_state_search_backtrack_limit", 8) or 0),
                ),
                "formal_state_search_max_no_improvement_quanta": max(
                    0,
                    int(
                        kwargs.get(
                            "formal_state_search_max_no_improvement_quanta",
                            6,
                        )
                        or 0
                    ),
                ),
                "recursive_helper_prover_enabled": bool(
                    kwargs.get("recursive_helper_prover_enabled", False)
                ),
                "recursive_helper_budget": int(
                    kwargs.get("recursive_helper_budget", 0) or 0
                ),
                "recursive_helper_max_depth": max_recursion_depth,
                "recursive_helper_max_attempts_per_node": int(
                    kwargs.get("recursive_helper_max_attempts_per_node", 2)
                    if kwargs.get("recursive_helper_max_attempts_per_node", 2)
                    is not None
                    else 2
                ),
                "recursive_helper_turns": int(
                    kwargs.get("recursive_helper_turns", max_turns) or max_turns
                ),
                "recursive_helper_refine": bool(
                    kwargs.get("recursive_helper_refine", False)
                ),
                "refiner_provider_policy": (
                    _recursive_client_provider_policy(kwargs.get("refiner_client"))
                    if kwargs.get("recursive_helper_refine", False)
                    else {}
                ),
                "recursion_depth": max(
                    0,
                    int(kwargs.get("recursion_depth", 0) or 0),
                ),
                "recursive_config_sha256": _recursive_config_fingerprint(
                    kwargs.get("config")
                ),
                "repair_retrieval_enabled": bool(
                    kwargs.get("repair_retrieval_enabled", True)
                ),
                "repair_retrieval_top_k": int(
                    kwargs.get("repair_retrieval_top_k", 6) or 0
                ),
                "raw_feedback": bool(kwargs.get("raw_feedback", False)),
                "strict_progress_accounting": bool(
                    kwargs.get("strict_progress_accounting", True)
                ),
                "soft_progress_streak_cap": max(
                    0,
                    int(kwargs.get("soft_progress_streak_cap", 4) or 0),
                ),
                "proof_state_present": kwargs.get("proof_state") is not None,
                "proof_state_fingerprint": _recursive_proof_state_fingerprint(
                    kwargs.get("proof_state")
                ),
                "lean_environment_hash": str(
                    getattr(dossier, "current_lean_environment_hash", "") or ""
                ),
                "theory_bundle_ids": tuple(
                    getattr(
                        theory_parent_session,
                        "theory_imported_bundle_ids",
                        (),
                    )
                    or ()
                ),
                "theory_domain": str(
                    getattr(
                        theory_parent_session,
                        "theory_domain",
                        "general mathematics",
                    )
                    or "general mathematics"
                ).strip(),
                "theory_default_imports": tuple(
                    str(item or "").strip()
                    for item in tuple(
                        getattr(
                            theory_parent_session,
                            "theory_default_imports",
                            ("Mathlib",),
                        )
                        or ("Mathlib",)
                    )
                    if str(item or "").strip()
                ),
                "theory_context_snapshot_hash": str(
                    getattr(
                        getattr(
                            theory_parent_session,
                            "theory_context_pair",
                            None,
                        ),
                        "snapshot_hash",
                        "",
                    )
                    or ""
                ),
                "theory_snapshot_sha256": text_hash(
                    json.dumps(
                        tuple(
                            getattr(
                                theory_parent_session,
                                "theory_snapshot",
                                (),
                            )
                            or ()
                        ),
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=True,
                        default=str,
                    )
                ),
                "searcher_capability": (
                    _recursive_runtime_capability_fingerprint(parent_searcher)
                ),
                "proof_cache_capability": (
                    _recursive_runtime_capability_fingerprint(kwargs.get("proof_cache"))
                ),
                "proof_cache_served_frontier": (
                    _recursive_proof_cache_served_frontier(
                        kwargs.get("proof_cache"),
                        conv=conv,
                        proof_state=kwargs.get("proof_state"),
                    )
                ),
                "theory_library_capability": (
                    _recursive_runtime_capability_fingerprint(theory_library)
                ),
                "theory_candidate_builder_capability": (
                    _recursive_runtime_capability_fingerprint(
                        getattr(
                            theory_parent_session,
                            "theory_candidate_builder",
                            None,
                        )
                    )
                ),
            },
        )
        lane_limit = 1 if speculative_operational_probe else 3
        if lane_ledger.unavailable(lane_key, limit=lane_limit):
            return _record_lane_exhausted()
    session.theory_promote_verified_helpers = bool(
        getattr(
            theory_parent_session,
            "theory_promote_verified_helpers",
            False,
        )
    )
    child_promotion_registered = False
    if _session_theory_promotion_enabled(session):
        # A recursive child is its own authoritative workspace. Stage from
        # that dossier immediately so a hard process loss cannot strand an
        # accepted helper until the outer workspace happens to merge it.
        session.theory_verified_helper_accept_callback = partial(
            _stage_session_verified_helper,
            session,
        )
        from ..proof_state_executor import register_verified_helper_accept_session

        register_verified_helper_accept_session(session.dossier, session)
        session.theory_verified_helper_reconcile_callback = partial(
            _stage_all_session_verified_helpers,
            session,
        )
        _initialize_promotion_helper_baseline(
            session,
            durable_parent_fingerprints=dict(
                getattr(
                    theory_parent_session,
                    "_theory_promotion_helper_fingerprints",
                    {},
                )
                or {}
            ),
        )
        # Retry any inherited helper whose parent receipt was not durably
        # attested, while coalescing helpers the parent already persisted.
        _stage_all_session_verified_helpers(session, force=True)
        child_promotion_registered = True
    session.max_stagnation = max(3, max_turns + 2)
    # Parent prove sessions get this from the LLM turn budget. Nested
    # claim sessions defaulted to max_no_applicable_recoveries=0, so
    # generation_rotation_ready followed by a single empty select killed
    # the only prove lane.
    session.configure_no_applicable_recovery(max_turns)

    if not speculative_operational_probe and session.theory_library is not None:
        session.register(DomainTheoryAction(stage="retrieve", id="domain_theory"))
        session.set_budget(
            "domain_theory",
            ActionBudget(max_invocations=2, max_total_seconds=0.0),
        )
        if getattr(session.theory_library, "mode", "off") == "build":
            session.register(
                DomainTheoryAction(
                    candidate_builder=session.theory_candidate_builder,
                    stage="build",
                    id="domain_theory_build",
                )
            )
            # See parent-session note above: theory_need scope ignores a session
            # time cap; per-build caps + the per-need guard bound theory builds.
            session.set_budget(
                "domain_theory_build",
                ActionBudget(max_invocations=4, max_total_seconds=0.0),
            )

    child_tactics_enabled = bool(kwargs.get("proof_state_child_tactics_enabled", False))
    if not speculative_operational_probe and child_tactics_enabled:
        _register_child_session_tactic_actions(
            session,
            max_turns=max_turns,
            kwargs=dict(kwargs),
        )
    elif not speculative_operational_probe and session.proof_state is not None:
        max_nodes = max(1, int(kwargs.get("proof_state_child_goal_limit", 3) or 0))
        session.register(
            GraphRouteAssemblyAction(
                max_routes=max_nodes,
                root_tactic_timeout_s=float(
                    kwargs.get(
                        "root_tactic_timeout_s",
                        kwargs.get(
                            "proof_state_child_tactic_timeout_s",
                            DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                        ),
                    )
                    or 0.0
                ),
                root_tactic_max_candidates=int(
                    kwargs.get(
                        "root_tactic_max_candidates",
                        kwargs.get("proof_state_child_tactic_max_candidates", 32),
                    )
                    or 0
                ),
            )
        )
        session.set_budget(
            "graph_route_assembly",
            ActionBudget(
                max_invocations=max(1, max_turns),
                max_total_seconds=_route_assembly_budget_seconds(
                    timeout_s=float(
                        kwargs.get(
                            "root_tactic_timeout_s",
                            kwargs.get(
                                "proof_state_child_tactic_timeout_s",
                                DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                            ),
                        )
                        or 0.0
                    ),
                    max_invocations=max(1, max_turns),
                ),
            ),
        )
        session.register(GraphNativeShortcutAction())
        session.set_budget(
            "graph_native_shortcut",
            ActionBudget(
                max_invocations=max(1, max_turns * 2),
                max_total_seconds=30.0,
            ),
        )

    if not speculative_operational_probe:
        _register_child_graph_recursive_decompose_action(
            session,
            max_turns=max_turns,
            kwargs=dict(kwargs),
            max_recursion_depth=max_recursion_depth,
        )

    recursive_helper_enabled = bool(
        kwargs.get("recursive_helper_prover_enabled", False)
    )
    recursive_helper_depth_allowed = bool(
        max_recursion_depth <= 0
        or int(session.recursion_depth or 0) < max_recursion_depth
    )
    if (
        not speculative_operational_probe
        and recursive_helper_enabled
        and child_tactics_enabled
        and session.proof_state is not None
        and recursive_helper_depth_allowed
    ):
        raw_helper_budget = int(kwargs.get("recursive_helper_budget", 0) or 0)
        helper_budget = raw_helper_budget if raw_helper_budget > 0 else max_turns
        session.register(
            RecursiveHelperProverAction(
                max_attempts_per_node=int(
                    kwargs.get("recursive_helper_max_attempts_per_node", 2)
                    if kwargs.get("recursive_helper_max_attempts_per_node", 2)
                    is not None
                    else 2
                ),
                helper_turns=int(
                    kwargs.get("recursive_helper_turns", max_turns) or max_turns
                ),
                refine_enabled=bool(kwargs.get("recursive_helper_refine", False)),
            )
        )
        session.set_budget(
            "recursive_helper_prover",
            ActionBudget(
                max_invocations=max(1, int(helper_budget or 1)),
                max_total_seconds=0.0,
            ),
        )

    session.register(
        ConversationTurnAction(
            role=role,
            client=client,
            sample_temperature=kwargs.get("temperature_override"),
            mini_phase_temperatures=kwargs.get("mini_phase_temperatures"),
            # Keep tool/retrieval dispatch on the same isolated child view as
            # MiniSession.searcher.  Reusing the raw parent kwarg here would
            # bypass the fork whenever ConversationTurnAction runs.
            searcher_override=child_searcher,
            lean_check_tool_enabled=bool(kwargs.get("lean_check_tool_enabled", True)),
            try_lean_tool_enabled=bool(kwargs.get("try_lean_tool_enabled", True)),
            compute_examples_tool_enabled=_kwargs_compute_examples_tool_enabled(kwargs),
            apply_decl_to_goal_tool_enabled=bool(
                kwargs.get("apply_decl_to_goal_tool_enabled", True)
            ),
            max_tool_calls_per_turn=child_tool_calls_per_turn,
            raw_feedback=bool(kwargs.get("raw_feedback", False)),
            repair_retrieval_enabled=bool(kwargs.get("repair_retrieval_enabled", True)),
            repair_retrieval_top_k=int(kwargs.get("repair_retrieval_top_k", 6) or 0),
            proof_state_child_tactics_enabled=child_tactics_enabled,
            proof_state_child_tactic_timeout_s=float(
                kwargs.get(
                    "proof_state_child_tactic_timeout_s",
                    DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                )
                or 0.0
            ),
            proof_state_child_tactic_max_candidates=int(
                kwargs.get("proof_state_child_tactic_max_candidates", 32) or 0
            ),
            proof_state_child_goal_limit=int(
                kwargs.get("proof_state_child_goal_limit", 3) or 0
            ),
            proof_state_decl_application_limit=int(
                kwargs.get("proof_state_decl_application_limit", 6) or 0
            ),
            proof_state_batch_parallelism=int(
                kwargs.get("proof_state_batch_parallelism", 1) or 1
            ),
            max_turns_for_budget=max_turns,
            llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(client),
            formalization_llm_turn_elapsed_s=_client_llm_turn_elapsed_budget_s(client),
            provider_dispatch_limit=(1 if speculative_operational_probe else 0),
        )
    )
    session.set_budget(
        f"conversation_turn_{role}",
        ActionBudget(max_invocations=max_turns, max_total_seconds=0.0),
    )
    session.expand_max_iterations_to_action_budgets(headroom=4)
    deadline_epoch_s = max(
        0.0,
        float(kwargs.get("action_deadline_epoch_s", 0.0) or 0.0),
    )
    if deadline_epoch_s <= 0.0 and recursive_max_elapsed_s > 0.0:
        deadline_epoch_s = time.time() + recursive_max_elapsed_s
    if theory_parent_session is not None:
        try:
            parent_recursive_deadline_epoch_s = float(
                getattr(
                    theory_parent_session,
                    "recursive_elapsed_deadline_epoch_s",
                    0.0,
                )
                or 0.0
            )
        except (TypeError, ValueError):
            parent_recursive_deadline_epoch_s = 0.0
        if parent_recursive_deadline_epoch_s > 0.0:
            # The ancestor's durable elapsed authority cannot be reset by a
            # fresh local child allowance or a replayed nested descriptor.
            deadline_epoch_s = (
                parent_recursive_deadline_epoch_s
                if deadline_epoch_s <= 0.0
                else min(deadline_epoch_s, parent_recursive_deadline_epoch_s)
            )
    # RecursiveHelperProverAction selected inside this nested conversation
    # inherits the enclosing deadline rather than resetting its allowance.
    session.recursive_elapsed_deadline_epoch_s = deadline_epoch_s
    if lane_ledger is not None:
        reservation = lane_ledger.try_reserve(
            lane_key,
            limit=(1 if speculative_operational_probe else 3),
        )
        if reservation is None:
            if child_promotion_registered:
                from ..proof_state_executor import (
                    register_verified_helper_accept_session,
                    unregister_verified_helper_accept_session,
                )

                unregister_verified_helper_accept_session(session.dossier)
                if (
                    theory_parent_session is not None
                    and session.dossier is theory_parent_session.dossier
                ):
                    register_verified_helper_accept_session(
                        theory_parent_session.dossier,
                        theory_parent_session,
                    )
            return _record_lane_exhausted()
        lane_token, lane_allowance = reservation
        session.max_model_call_deferred_frontier_retries = max(
            0,
            lane_allowance - 1,
        )
        session.max_model_call_deferred_static_retries = max(
            0,
            lane_allowance - 1,
        )
    completed_normally = False
    child_run_settled = False
    timed_out = False
    try:
        from .recursive_helper_prover import _run_child_with_elapsed_budget

        ok, proof, timed_out = await _run_child_with_elapsed_budget(
            session,
            max_elapsed_s=recursive_max_elapsed_s,
            deadline_epoch_s=deadline_epoch_s,
        )
        child_run_settled = True
        result = (ok, proof)
        if timed_out:
            setattr(conv, "_mini_recursive_child_elapsed_budget_exhausted", True)
            increment_metric = getattr(dossier, "increment_tool_metric", None)
            if callable(increment_metric):
                increment_metric("mini_recursive_child_elapsed_budget_exhausted", 1)
            recorder = kwargs.get("recorder")
            record_turn = getattr(recorder, "record_turn", None)
            if callable(record_turn):
                record_turn(
                    {
                        "phase": "mini_recursive_child_conversation",
                        "role": role,
                        "theorem_name": theorem_name,
                        "max_elapsed_s": recursive_max_elapsed_s,
                        "action_deadline_epoch_s": deadline_epoch_s,
                        "verdict": "recursive_claim_elapsed_budget_exhausted",
                    }
                )
        completed_normally = True
    finally:
        if lane_ledger is not None and lane_token:
            try:
                charged_attempts = _recursive_conversation_lane_paid_failure_count(
                    session,
                    include_unapplied_exposure=(timed_out or not child_run_settled),
                )
            except Exception:
                charged_attempts = 0
            lane_ledger.settle(
                lane_token,
                charge_count=charged_attempts,
            )
        if child_promotion_registered:
            try:
                _stage_all_session_verified_helpers(session, force=True)
            except Exception:
                pass
            from ..proof_state_executor import (
                register_verified_helper_accept_session,
                unregister_verified_helper_accept_session,
            )

            unregister_verified_helper_accept_session(session.dossier)
            if (
                theory_parent_session is not None
                and session.dossier is theory_parent_session.dossier
            ):
                register_verified_helper_accept_session(
                    theory_parent_session.dossier,
                    theory_parent_session,
                )
        _snapshot_session_state_for_caller(session)
    durable_role_counts = getattr(
        session,
        "_conversation_role_turn_counts",
        {},
    )
    exposure_role_counts = getattr(
        session,
        "_conversation_role_turn_exposure_counts",
        {},
    )
    try:
        durable_turns = max(
            0,
            int(
                durable_role_counts.get(role, 0)
                if isinstance(durable_role_counts, dict)
                else 0
            ),
        )
    except (TypeError, ValueError, OverflowError):
        durable_turns = max_turns
    try:
        exposed_turns = max(
            0,
            int(
                exposure_role_counts.get(role, 0)
                if isinstance(exposure_role_counts, dict)
                else 0
            ),
        )
    except (TypeError, ValueError, OverflowError):
        exposed_turns = max_turns
    # This receipt is the recursive driver's authority for sharing one turn
    # tranche between prove and refine.  Clamp it to the invocation's declared
    # budget, but never let a scheduler rollback erase a started outer turn
    # captured by the exposure counter.
    setattr(
        conv,
        "_last_run_turns_used",
        min(max_turns, max(durable_turns, exposed_turns)),
    )
    if completed_normally:
        child_theory_bundle_ids = tuple(
            getattr(session, "theory_imported_bundle_ids", ()) or ()
        )
        child_theory_snapshot = tuple(
            dict(item) for item in getattr(session, "theory_snapshot", ()) or ()
        )
        child_theory_context_hash = str(
            getattr(getattr(session, "theory_context_pair", None), "snapshot_hash", "")
            or getattr(
                getattr(session, "dossier", None), "mini_theory_context_hash", ""
            )
            or ""
        )
        # The recursive driver owns helper admission after this callback
        # returns.  Expose the exact child proof environment so it can replay
        # under/promote that environment instead of treating a child proof as
        # if it were authored under the parent's older preamble.
        setattr(
            conv,
            "mini_theory_imported_bundle_ids",
            child_theory_bundle_ids,
        )
        setattr(conv, "mini_theory_snapshot", child_theory_snapshot)
        setattr(conv, "mini_theory_context_hash", child_theory_context_hash)
        if theory_parent_session is not None and child_theory_bundle_ids:
            if bool(kwargs.get("defer_theory_promotion", False)):
                setattr(
                    conv,
                    "mini_theory_commit_promotion",
                    _DeferredTheoryPromotion(
                        theory_parent_session,
                        child_theory_bundle_ids,
                    ),
                )
            else:
                theory_parent_session.install_theory_bundles(child_theory_bundle_ids)
    latest = str(getattr(session, "last_llm_content", "") or "")
    if latest:
        try:
            setattr(conv, "_last_llm_content", latest)
            if not str(getattr(conv, "_last_no_proof_llm_response", "") or ""):
                setattr(conv, "_last_no_proof_llm_response", latest)
        except Exception:
            pass
    return result


def _bind_theory_parent_callback(session: MiniSession, **inherited_kwargs: Any):
    """Bind child theory inheritance while preserving callback identity."""

    callback_kwargs = dict(inherited_kwargs)
    # Every bound callback is recursive work.  Its child theory context is a
    # candidate until mini_recursive independently replays and accepts the
    # exact returned proof.
    callback_kwargs["defer_theory_promotion"] = True
    callback_kwargs["recursive_lane_owner"] = getattr(
        session,
        "_recursive_lane_authority",
        session,
    )
    callback = partial(
        _mini_session_run_conversation_callback,
        theory_parent_session=session,
        **callback_kwargs,
    )
    callback = update_wrapper(callback, _mini_session_run_conversation_callback)

    def rebind_dispatch_session(staged_session: MiniSession):
        return _bind_theory_parent_callback(
            staged_session,
            **inherited_kwargs,
        )

    callback._mini_dispatch_rebind_session = rebind_dispatch_session
    return callback
