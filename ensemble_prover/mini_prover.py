"""CLI and composition root for Lean-verified ensemble theorem search.

The primary interface targets one theorem in a caller-supplied Lean project
(``--lean-file``, ``--theorem-name``, and ``--project-path``). The release does
not bundle Lean, Lake, Mathlib, or benchmark sources. ``--putnam-file`` is an
optional PutnamBench adapter; the underlying theorem-project model is generic.

CLI searches run in an isolated worker supervised by a parent process; the
public ``prove_problem`` API instead runs cooperatively in its caller's event
loop. Both paths use typed frontier work, provider and Lean budgets, a proof
graph, and verification gates. The CLI persists run receipts; programmatic
callers receive durable recorder events only when they supply a recorder.
Generated text is never proof evidence by itself. The CLI's solved-export path
requests fresh Lean replay and axiom auditing before installing a standalone
artifact; an export failure leaves the verified root finalized with export
still pending. Parallel samples remain isolated until their verified results
and reusable evidence are merged.

Provider roles are configured independently: the prover performs ordinary
search, the optional refiner repairs rejected attempts, and planner escalation
repairs invalid recursive plans. Provider-specific request semantics, usage,
pricing, deadlines, and reasoning controls are preserved by the shared client
layer.

Use ``python -m ensemble_prover.mini_prover --help`` as the authority for
current options and defaults.

Examples::

    python -m ensemble_prover.mini_prover \\
        --lean-file /path/to/project/MyTheorem.lean \\
        --theorem-name MyTheorem \\
        --project-path /path/to/project \\
        --import Mathlib

    python -m ensemble_prover.mini_prover \\
        --putnam-file /path/to/PutnamBench/lean4/src/putnam_2001_a1.lean
"""

from __future__ import annotations

import argparse
import asyncio
import copy
import hashlib
import inspect
import json
import math
import os
import re
import sys
import tempfile
import threading
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Callable, Dict, List, Mapping, Optional, Sequence, Set, Tuple

from dotenv import load_dotenv

from .premise_retrieval import DEFAULT_TOP_K as PREMISE_DEFAULT_TOP_K
from .config import LeanConfig, RetrievalConfig, RoleConfig
from .helper_salvage import (
    HelperSalvager,
    merge_context_helpers,
    merge_helpers_for_correction_recheck,
    refresh_revalidated_dependent_support_hashes,
)
from .lean_runner import LeanRunner
from .lean_syntax import lean_expression_delimiters_balanced
from .llm_deadline import llm_retry_deadline_record_from_exception
from .mini_deadline_transaction import DeadlineMutationTransaction
from .mini_recursive_outcome import is_resumable_mini_recursive_yield
from .llm_usage import (
    CostBudgetController,
    call_with_optional_usage_callback,
    metered_or_plain_call,
    reservation_pricing_targets,
    usage_totals_from_clients,
)
from .mathlib_api_search import MathlibApiSearcher
from .lemma_retriever import LemmaRetriever
from .mathematical_retrieval import (
    MathematicalRetrievalService,
    ProjectSupportSource,
    PublishedTheorySource,
    StaticMathlibSource,
)
from .mathematical_retrieval.service import lake_module_roots
from .mini_falsification import (
    DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
    DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
    require_falsification_search_bound,
    require_falsification_watchdog,
)
from .mini_recursive import (
    PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
    _probe_active_root_targets,
)
from .mini_runtime_defaults import (
    DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
    DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
    DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
    DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
)
from .mini_run_recorder import (
    RunRecorder,
    _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS,
    _MINI_GRAPH_RECURSIVE_DECOMPOSE_METRIC_KEYS,
    _TeeStream as _TeeStream,
)
from .provider_health import (
    ProviderLaneHealthRegistry,
    fresh_provider_lane_health_run,
)
from .mini_temperature import (
    MiniPhaseTemperatures,
    MiniTemperatureContext,
    mini_temperature_metadata,
    refresh_temperature_metadata_from_client,
    resolve_mini_temperature,
)
from .solved_export_policy import (
    failure_counter_present as solved_export_failure_counter_present,
    solved_export_failure_reason,
    solved_export_verified_payload,
)
from .target_integrity import (
    classify_target_integrity_signals,
    target_integrity_feedback,
)
from .mini_branching import (
    _GuardedProofCache as _GuardedProofCache,
    _GuardedRecorder as _GuardedRecorder,
    _SampleAbandonGuard as _SampleAbandonGuard,
    _begin_parallel_falsification_conflict_receipt_scope as _begin_parallel_falsification_conflict_receipt_scope,
    _copy_branch_failure_observability as _copy_branch_failure_observability,
    _copy_dossier_contents as _copy_dossier_contents,
    _consume_parallel_falsification_conflict_receipts as _consume_parallel_falsification_conflict_receipts,
    _clear_parallel_sample_observability as _clear_parallel_sample_observability,
    _install_parallel_monotonic_metric_sink as _install_parallel_monotonic_metric_sink,
    _merge_dossier_helpers as _merge_dossier_helpers,
    _merge_dossier_observability as _merge_dossier_observability,  # noqa: F401
    _merge_dossier_tool_metrics as _merge_dossier_tool_metrics,
    _merge_parallel_sample_structural_progress as _merge_parallel_sample_structural_progress,
    _merge_verified_dossier_helpers as _merge_verified_dossier_helpers,
    _mark_parallel_proof_disproof_conflict as _mark_parallel_proof_disproof_conflict,
    _parallel_authoritative_failure_records as _parallel_authoritative_failure_records,
    _parallel_completed_root_disproof_certificate_hashes as _parallel_completed_root_disproof_certificate_hashes,
    _resolve_parallel_root_disproof_terminal_state as _resolve_parallel_root_disproof_terminal_state,
    _parallel_observability_snapshot as _parallel_observability_snapshot,
    _parallel_monotonic_metric_snapshot as _parallel_monotonic_metric_snapshot,
    _parallel_failure_score as _parallel_failure_score,
    _parallel_proof_disproof_conflict_certificate_hashes as _parallel_proof_disproof_conflict_certificate_hashes,
    _parallel_sample_has_finalized_root_proof as _parallel_sample_has_finalized_root_proof,
    _parallel_sample_has_proof_disproof_conflict as _parallel_sample_has_proof_disproof_conflict,
    _parallel_sample_proof_state_record as _parallel_sample_proof_state_record,
    _parallel_samples_arg as _parallel_samples_arg,
    _parallel_temps_arg as _parallel_temps_arg,
    _restore_parallel_observability_snapshot as _restore_parallel_observability_snapshot,
    _restore_parallel_monotonic_metric_snapshot as _restore_parallel_monotonic_metric_snapshot,
    record_parallel_sample_failure as record_parallel_sample_failure,
    record_parallel_samples_zero_completed as record_parallel_samples_zero_completed,
    _seed_proposed_helpers as _seed_proposed_helpers,
    _select_parallel_failure_primary as _select_parallel_failure_primary,
    _snapshot_parallel_live_root_disproof as _snapshot_parallel_live_root_disproof,
    _snapshot_parallel_live_root_proof as _snapshot_parallel_live_root_proof,
    _snapshot_parallel_live_proof_disproof_conflict as _snapshot_parallel_live_proof_disproof_conflict,
    _stratify_sample_temperatures as _stratify_sample_temperatures,
)
from .mini_lean_extract import (
    _detect_known_answer_no_construction_collapse as _detect_known_answer_no_construction_collapse,
    _extract_example_body as _extract_example_body,
    _extract_first_proof as _extract_first_proof,
    _extract_helpers_and_main as _extract_helpers_and_main,
    _extract_lemma_dag_helper_declarations as _extract_lemma_dag_helper_declarations,
    _extract_single_decl_body as _extract_single_decl_body,
    _find_extra_main_proof_chunks as _find_extra_main_proof_chunks,
    _find_helpers_after_final_main as _find_helpers_after_final_main,
    _find_forbidden_lean_command as _find_forbidden_lean_command,
    _find_post_main_helper_declarations as _find_post_main_helper_declarations,
    _has_durable_subgoal_helper as _has_durable_subgoal_helper,
    _helper_is_sorry_stub as _helper_is_sorry_stub,
    _helper_referenced_names as _helper_referenced_names,
    _helper_statement_root_equivalent as _helper_statement_root_equivalent,
    _helpers_referenced_by_proof as _helpers_referenced_by_proof,
    _is_noop_root_proof as _is_noop_root_proof,
    _is_plausible_main_proof as _is_plausible_main_proof,
    _lean_body_is_sorry_stub as _lean_body_is_sorry_stub,
    _lean_comment_text as _lean_comment_text,
    _partition_preamble_redeclarations as _partition_preamble_redeclarations,
    _root_equivalent_helper_names_from_blocks as _root_equivalent_helper_names_from_blocks,
    _root_equivalent_sorry_stub_helper_names_from_blocks as _root_equivalent_sorry_stub_helper_names_from_blocks,
    _sorry_stub_helper_names as _sorry_stub_helper_names,
    _salvage_small_multiple_main_submission as _salvage_small_multiple_main_submission,
    _split_top_level_chunks as _split_top_level_chunks,
    _strip_lean_comments as _strip_lean_comments,
    _strip_lean_comments_and_strings as _strip_lean_comments_and_strings,
    _strip_redundant_preamble_commands as _strip_redundant_preamble_commands,
    _top_level_chunks_from_reply as _top_level_chunks_from_reply,
)
from .mini_failure_analysis import (
    FailureAnalyzer as FailureAnalyzer,
    _FAILURE_ANALYZER as _FAILURE_ANALYZER,
    _RAW_FEEDBACK_MAX_CHARS as _RAW_FEEDBACK_MAX_CHARS,
    _analyze_lean_failure as _analyze_lean_failure,
    _failure_signature_from_analysis as _failure_signature_from_analysis,
    _failure_signature_from_feedback as _failure_signature_from_feedback,
    _format_lean_failure_feedback as _format_lean_failure_feedback,
    _format_raw_lean_feedback as _format_raw_lean_feedback,
    _lean_failure_all_goals_are_direct_local_closes as _lean_failure_all_goals_are_direct_local_closes,
    _manual_lean_failure_analysis as _manual_lean_failure_analysis,
    _needs_answer_safe_feedback_check as _needs_answer_safe_feedback_check,
    _prepend_repeated_failure_notice as _prepend_repeated_failure_notice,
)
from .mini_policy import (
    _GRAPH_SELECTED_WORK_SCOPE_KEY as _GRAPH_SELECTED_WORK_SCOPE_KEY,
    _REJECTED_FRAGMENT_HEADER as _REJECTED_FRAGMENT_HEADER,
    _REPAIR_BOUNDARY as _REPAIR_BOUNDARY,
    _REPAIR_CONTINUATION as _REPAIR_CONTINUATION,
    _REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY as _REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY,
    _REPAIR_FEEDBACK as _REPAIR_FEEDBACK,
    _REPAIR_PAYLOAD_CARRIED_KEY as _REPAIR_PAYLOAD_CARRIED_KEY,
    _REPAIR_PAYLOAD_RESET_BEFORE_KEY as _REPAIR_PAYLOAD_RESET_BEFORE_KEY,
    _REPAIR_REJECTED_FRAGMENTS_KEY as _REPAIR_REJECTED_FRAGMENTS_KEY,
    _REPAIR_SELF_CHECK_MARKER as _REPAIR_SELF_CHECK_MARKER,
    _REPAIR_SEMANTICS_KEY as _REPAIR_SEMANTICS_KEY,
    _REPAIR_TRANSIENT_GOAL_TARGETS_KEY as _REPAIR_TRANSIENT_GOAL_TARGETS_KEY,
    _TRANSIENT_GOAL_TARGET_HEADER as _TRANSIENT_GOAL_TARGET_HEADER,
    _bank_helpers_as_proposed as _bank_helpers_as_proposed,
    _bind_provider_continuation_policy_receipt as _bind_provider_continuation_policy_receipt,
    _classify_giveup_signal as _classify_giveup_signal,
    _compact_history_summary_text as _compact_history_summary_text,
    _conversation_official_answer_visible as _conversation_official_answer_visible,
    _conversation_should_redact_solution_refs as _conversation_should_redact_solution_refs,
    _dedupe_repair_payload_items as _dedupe_repair_payload_items,
    _drop_last_assistant_if_content as _drop_last_assistant_if_content,
    _drop_stale_feedback_before_first_kept_attempt as _drop_stale_feedback_before_first_kept_attempt,
    _extract_rejected_code_fragments as _extract_rejected_code_fragments,
    _extract_transient_goal_targets as _extract_transient_goal_targets,
    _format_invalid_helper_stub_with_main_feedback as _format_invalid_helper_stub_with_main_feedback,
    _format_no_proof_extracted_feedback as _format_no_proof_extracted_feedback,
    _format_repackaged_goal_target_feedback as _format_repackaged_goal_target_feedback,
    _format_repair_self_check_missing_feedback as _format_repair_self_check_missing_feedback,
    _format_reused_fragment_feedback as _format_reused_fragment_feedback,
    _format_root_equivalent_helper_feedback as _format_root_equivalent_helper_feedback,
    _format_self_check_mismatch_feedback as _format_self_check_mismatch_feedback,
    _format_self_check_terminal_continuation_feedback as _format_self_check_terminal_continuation_feedback,
    _giveup_decomposition_nudge as _giveup_decomposition_nudge,
    _infer_repair_semantics_for_user_content as _infer_repair_semantics_for_user_content,
    _is_controller_repair_continuation_content as _is_controller_repair_continuation_content,
    _is_explicit_repair_boundary_content as _is_explicit_repair_boundary_content,
    _is_history_compaction_summary as _is_history_compaction_summary,
    _is_low_signal_goal_target as _is_low_signal_goal_target,
    _is_repair_cycle_neutral_user_message as _is_repair_cycle_neutral_user_message,
    _is_repair_feedback_content as _is_repair_feedback_content,
    _is_stable_handoff_message as _is_stable_handoff_message,
    _is_stale_selected_work_context_message as _is_stale_selected_work_context_message,
    _is_stale_repair_feedback_message as _is_stale_repair_feedback_message,
    _message_has_visible_repair_payload as _message_has_visible_repair_payload,
    _message_repair_semantics as _message_repair_semantics,
    _merge_repair_self_check_non_verdict_status as _merge_repair_self_check_non_verdict_status,
    _normalise_repair_semantics as _normalise_repair_semantics,
    _proof_is_structural_collapse as _proof_is_structural_collapse,
    _proof_repackages_transient_goal_target as _proof_repackages_transient_goal_target,
    _proof_reuses_rejected_fragments as _proof_reuses_rejected_fragments,
    _prompt_safe_tool_arguments as _prompt_safe_tool_arguments,
    _prompt_safe_tool_call_token as _prompt_safe_tool_call_token,
    _prompt_safe_tool_name_token as _prompt_safe_tool_name_token,
    _provider_safe_chat_message as _provider_safe_chat_message,
    _record_repair_policy_attempt as _record_repair_policy_attempt,
    _rejected_fragments_from_feedback_text as _rejected_fragments_from_feedback_text,
    _rejected_fragments_from_latest_feedback as _rejected_fragments_from_latest_feedback,
    _repair_feedback_messages_in_current_cycle as _repair_feedback_messages_in_current_cycle,
    _repair_content_is_helper_only_decomposition as _repair_content_is_helper_only_decomposition,
    _repair_payload_from_current_cycle as _repair_payload_from_current_cycle,
    _repair_payload_from_failure_analysis as _repair_payload_from_failure_analysis,
    _repair_payload_values_from_message as _repair_payload_values_from_message,
    _repair_self_check_durable_submission_evidence as _repair_self_check_durable_submission_evidence,
    _repair_self_check_has_accepted_evidence as _repair_self_check_has_accepted_evidence,
    _repair_self_check_has_terminal_continuation as _repair_self_check_has_terminal_continuation,
    _repair_self_check_matches_submission as _repair_self_check_matches_submission,
    _repair_self_check_non_verdict_is_compliant as _repair_self_check_non_verdict_is_compliant,
    _repair_self_check_required_message as _repair_self_check_required_message,
    _repair_turn_requires_self_check as _repair_turn_requires_self_check,
    _responses_output_matches_advertised_tool_calls as _responses_output_matches_advertised_tool_calls,
    _select_tool_calls_for_repair_budget as _select_tool_calls_for_repair_budget,
    _summarize_compacted_attempts as _summarize_compacted_attempts,
    _summarize_compacted_tool_evidence as _summarize_compacted_tool_evidence,
    _transient_goal_targets_from_feedback_text as _transient_goal_targets_from_feedback_text,
    _transient_goal_targets_from_latest_feedback as _transient_goal_targets_from_latest_feedback,
    _user_history_message as _user_history_message,
)
from .mini_repair import (
    _GOAL_OPERATOR_TAGS as _GOAL_OPERATOR_TAGS,
    _LEAN_BUILTIN_WORDS as _LEAN_BUILTIN_WORDS,
    _LEAN_IDENTIFIER_RE as _LEAN_IDENTIFIER_RE,
    _LEAN_METAVAR_RE as _LEAN_METAVAR_RE,
    _LEAN_RESERVED_LOCAL_NAMES as _LEAN_RESERVED_LOCAL_NAMES,
    _LEAN_SOURCE_LOCATION_RE as _LEAN_SOURCE_LOCATION_RE,
    _LEAN_TYPE_SYMBOLS as _LEAN_TYPE_SYMBOLS,
    _MATHLIB_SHAPE_KEYWORDS as _MATHLIB_SHAPE_KEYWORDS,
    _REPAIR_QUERY_NOISE_WORDS as _REPAIR_QUERY_NOISE_WORDS,
    _REPAIR_RETRIEVAL_QUERY_MAX_CHARS as _REPAIR_RETRIEVAL_QUERY_MAX_CHARS,
    _compact_search_text as _compact_search_text,
    _format_search_results as _format_search_results,
    _repair_query_keywords as _repair_query_keywords,
    _repair_retrieval_query as _repair_retrieval_query,
    _retrieve_repair_candidates as _retrieve_repair_candidates,
    _retrieve_repair_candidates_async as _retrieve_repair_candidates_async,
    _sanitize_repair_query_fragment as _sanitize_repair_query_fragment,
)
from .mini_root_tactic import (
    root_tactic_success_contract_status,
    try_close_root_with_active_lift,
    try_root_tactic_close as _run_root_tactic_close,
)
from .tactic_attempt_telemetry import (
    dossier_lean_attempt_observer,
    tactic_attempt_telemetry_fields,
)

from .mini_tactic_closer import (
    TacticPatternCache,
    is_transient_tactic_close_failure,
    try_close_with_tactics,
)
from .models import (
    OpenAICompatClient,
    response_output_items,
    response_reasoning_items,
    response_reasoning_text,
)
from .pricing import (
    base_url_matches_provider,
    canonical_openrouter_model_id,
    lookup_known_token_pricing_async,
)
from .run_provenance import capture_repository_provenance
from .provider_tool_protocol import (
    DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC,
    DEEPSEEK_FINAL_RAW_NO_TOOLS_METRIC,
    DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
    MINI_TOOL_REASONING_EFFORT,
    MiniReasoningCapabilityUnavailable,
    extract_simple_xml_tool_calls,
    handle_deepseek_dsml_after_budget,
    is_deepseek_client,
    mini_bounded_visible_output_reasoning_effort,
    mini_model_output_capacity,
    mini_visible_output_reasoning_effort,
    preflight_mini_reasoning_contract,
    resolve_final_no_tools_output,
    should_use_raw_final_no_tools,
    toolless_final_messages,
)
from .proof_dossier import (
    ProofDossier,
    _decl_application_error_is_lean_diagnostic,
    _prompt_safe_helper_name,
    _prompt_safe_inline_text,
    _prompt_safe_lean_diagnostic_text,
    _prompt_safe_natural_language_text,
    active_root_target_statement,
    active_root_targets_match_frame as dossier_active_root_targets_match_frame,
    active_root_targets_for_frame,
    canonical_dossier_statement_key,
    effective_solution_placeholder_suppression,
    helper_progress_metadata_for_accepted_helpers,
    helper_decl_name,
    is_answer_unsafe_statement_text,
    official_answer_visible_to_llm,
    text_hash,
    verified_helper_semantic_statement_changed,
    verified_helper_surface_statement_changed,
)
from .proof_state import ProofSearchState
from .proof_state_cache import (
    MiniVerifiedLemmaCache,
    store_verified_helper_for_dossier,
)
from .proof_state_executor import (
    _LeanOperationDeadline,
    _accept_proof_state_helper,
    _await_serialized_lean_operation,
    _axiomatize_helper_for_feedback,
    _decl_application_failure_is_retryable,
    _extract_and_spawn_typed_residual_goals,
    _fully_funded_operation_timeout,
    _proof_from_decl_application_stub,
    _proof_state_helper_block,
    _proof_state_acceptance_preamble,
    _proof_state_check_preamble,
    retain_pending_helper_acceptance_retry,
    stage_pending_helper_acceptance,
    stage_closed_typed_residual_acceptance,
    _try_proof_state_child_closures,
    _try_proof_state_lemma_dag_helpers,
    _try_proof_state_salvaged_helper_assembly,
    _typed_residual_operation_timeout,
    _with_turn_budget_footer,
)
from .proof_state_scheduler import _retrieve_proof_state_node_candidates_async
from .putnam import load_putnam_project as load_putnam_problem, problem_docstring_text
from .theorem_project import (
    GENERIC_ADAPTER_ID,
    PUTNAMBENCH_ADAPTER_ID,
    TheoremProblem,
    TheoremProjectRequest,
    decode_theorem_target_context,
    resolve_theorem_project,
    scan_lean_imports,
    refresh_theorem_project_environment,
    with_elaborated_statement_type,
    validate_theorem_project_source,
)
from .proof_tools import (
    APPLY_DECL_TO_ACTIVE_GOAL_TOOL as APPLY_DECL_TO_GOAL_TOOL,
    normalize_theorem_search_query,
)
from .lean_compute_tool import COMPUTE_EXAMPLES_TOOL, run_compute_examples_tool
from .try_lean_tool import TRY_LEAN_TOOL, run_try_lean_tool
from .certify_counterexample_tool import (
    CERTIFY_COUNTEREXAMPLE_TOOL,
    run_certify_counterexample_tool,
)
from .utils import display_line_count, format_exception, parse_tool_arguments
from .llm_error_policy import (
    LLMErrorClassification,
    classify_llm_error_text,
    classify_llm_exception,
    llm_failure_scope,
    is_retryable_llm_exception,
)


def _sanitize_model_facing_value(
    value: Any,
    *,
    redact_solution_refs: bool,
    limit: int = 1000,
) -> Any:
    if isinstance(value, str):
        return _prompt_safe_inline_text(
            value,
            limit=limit,
            redact_solution_refs=redact_solution_refs,
        )
    if isinstance(value, Mapping):
        return {
            str(
                _sanitize_model_facing_value(
                    str(key),
                    redact_solution_refs=redact_solution_refs,
                    limit=limit,
                )
            ): _sanitize_model_facing_value(
                item,
                redact_solution_refs=redact_solution_refs,
                limit=limit,
            )
            for key, item in value.items()
        }
    if isinstance(value, (list, tuple)):
        return [
            _sanitize_model_facing_value(
                item,
                redact_solution_refs=redact_solution_refs,
                limit=limit,
            )
            for item in value
        ]
    return value


class _VisibleAnswerModeAction(argparse.Action):
    """Argparse action that enables the explicit with-answer control mode."""

    def __call__(
        self,
        parser: argparse.ArgumentParser,
        namespace: argparse.Namespace,
        values: Any,
        option_string: Optional[str] = None,
    ) -> None:
        setattr(namespace, "opaque_mode", False)
        setattr(namespace, "allow_official_answer_visibility", True)


class _TrackedBooleanOptionalAction(argparse.BooleanOptionalAction):
    """Boolean flag that preserves whether the user supplied either spelling."""

    def __call__(
        self,
        parser: argparse.ArgumentParser,
        namespace: argparse.Namespace,
        values: Any,
        option_string: Optional[str] = None,
    ) -> None:
        super().__call__(parser, namespace, values, option_string)
        setattr(namespace, f"_{self.dest}_explicit", True)


def _effective_cli_formal_state_search(args: argparse.Namespace) -> bool:
    """Return the capability the selected CLI execution path can run."""
    return bool(
        getattr(args, "formal_state_search", False)
        and max(
            0.0,
            float(
                getattr(
                    args,
                    "formal_state_search_timeout_s",
                    DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                )
                or 0.0
            ),
        )
        > 0.0
    )


def _mini_temperature_arg(value: str) -> float:
    try:
        temp = float(value)
    except Exception as exc:
        raise argparse.ArgumentTypeError(
            f"temperature must be a finite float in [0.0, 2.0], got {value!r}"
        ) from exc
    if not math.isfinite(temp) or temp < 0.0 or temp > 2.0:
        raise argparse.ArgumentTypeError(
            f"temperature must be a finite float in [0.0, 2.0], got {value!r}"
        )
    return temp


def _positive_finite_float_arg(value: str) -> float:
    try:
        parsed = float(value)
    except Exception as exc:
        raise argparse.ArgumentTypeError(
            f"value must be a finite float > 0, got {value!r}"
        ) from exc
    if not math.isfinite(parsed) or parsed <= 0.0:
        raise argparse.ArgumentTypeError(
            f"value must be a finite float > 0, got {value!r}"
        )
    return parsed


def _nonnegative_finite_float_arg(value: str) -> float:
    try:
        parsed = float(value)
    except Exception as exc:
        raise argparse.ArgumentTypeError(
            f"value must be a finite float >= 0, got {value!r}"
        ) from exc
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError(
            f"value must be a finite float >= 0, got {value!r}"
        )
    return parsed


def _llm_request_timeout_arg(value: str) -> Any:
    text = str(value or "").strip()
    if text.lower() in _LLM_REQUEST_TIMEOUT_DISABLED_ALIASES:
        return _LLM_REQUEST_TIMEOUT_DISABLED
    return _positive_finite_float_arg(text)


def _resolve_llm_request_timeout_setting(
    value: Any,
    *,
    role_name: str,
) -> Tuple[Optional[float], Optional[bool]]:
    if value is None:
        return None, None
    if isinstance(value, str) and value.strip().lower() in (
        _LLM_REQUEST_TIMEOUT_DISABLED_ALIASES | {_LLM_REQUEST_TIMEOUT_DISABLED}
    ):
        return None, True
    try:
        parsed = float(value)
    except Exception as exc:
        raise SystemExit(
            f"{role_name} request timeout must be finite seconds or one of "
            f"{', '.join(sorted(_LLM_REQUEST_TIMEOUT_DISABLED_ALIASES))}, "
            f"got {value!r}"
        ) from exc
    if not math.isfinite(parsed) or parsed <= 0.0:
        raise SystemExit(
            f"{role_name} request timeout must be a finite number > 0, got {parsed}"
        )
    return parsed, False


def _mini_phase_temperature_policy_from_args(args: Any) -> MiniPhaseTemperatures:
    return MiniPhaseTemperatures(
        enabled=bool(getattr(args, "mini_phase_temperatures", True)),
        planner=_mini_temperature_arg(
            getattr(args, "mini_temperature_planner", 0.10)
        ),
        initial_proof=_mini_temperature_arg(
            getattr(args, "mini_temperature_initial_proof", 0.45)
        ),
        formalization_helper=_mini_temperature_arg(
            getattr(args, "mini_temperature_formalization_helper", 0.10)
        ),
        lean_repair=_mini_temperature_arg(
            getattr(args, "mini_temperature_lean_repair", 0.05)
        ),
        refine=_mini_temperature_arg(getattr(args, "mini_temperature_refine", 0.25)),
        route_assembly=_mini_temperature_arg(
            getattr(args, "mini_temperature_route_assembly", 0.25)
        ),
        stagnation_escape=_mini_temperature_arg(
            getattr(args, "mini_temperature_stagnation_escape", 0.85)
        ),
        use_sample_temperature_for_initial=bool(
            getattr(args, "mini_temperature_initial_use_sample", True)
        ),
    )


# Load .env from the project root so OPENAI_API_KEY / DEEPSEEK_API_KEY /
# OPENROUTER_API_KEY are available without the user exporting them manually.
# ``override=False`` means real shell exports still win — the .env is the fallback.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
load_dotenv(_PROJECT_ROOT / ".env", override=False)


# ---------------------------------------------------------------------------
# Two role system-prompts. ONE template family, swapped by role.
# ---------------------------------------------------------------------------

_HELPER_RULES = (
    "\n"
    "Lean submission shape: put one fenced ```lean block in your answer. "
    "Submit a proof attempt for the active goal on every turn. Any helper "
    "declarations in that block must have complete proofs (no `sorry`, no "
    "`admit`, no holes), and the block must end with exactly one "
    "`example : <main_goal_type> := by ...` or bare `by ...` proof body. "
    "Do not re-emit the parent theorem as a helper and do not redeclare "
    "names from the preamble, including `_solution` names. Local "
    "`have`/`suffices` bridge targets are allowed only when you can close "
    "them in the submitted proof. Do not submit a proof body that merely "
    "names an unproved intermediate fact and leaves it to future work. Missing "
    "Mathlib names are not proof-failure evidence: search for the exact name, "
    "prove the needed fact from available ingredients, or pivot to a different "
    "proof route. Do not answer an active proof turn by emitting "
    "helper-obligation sections, sorry-stub theorem declarations, or a "
    "helper-DAG plan unless a separate planner/decomposition prompt explicitly "
    "asks for that format. Unavailable facts are work items, not blockers: "
    "when the proof needs a fact that is not already named, manufacture the "
    "smallest useful local theorem/lemma/definition, prove it completely, and "
    "then use it to advance the active proof."
)

_DECLARATION_REQUIRED_HELPER_RULES = (
    "\n"
    "Lean submission shape for declaration-required formalization: put one "
    "fenced ```lean block in your answer. This is not a proof-body turn: "
    "do not end with an anonymous `example : ... := by ...` or a bare "
    "`by ...` proof body. Submit complete named `theorem` or `lemma` "
    "declarations only. Any auxiliary declarations in that block must have "
    "complete proofs (no `sorry`, no `admit`, no holes), and the final "
    "declaration must be the selected formalized obligation or the smallest "
    "parent-anchored bridge requested by the graph work. Keep route "
    "hypotheses explicit in the final declaration statement. Do not re-emit "
    "the parent theorem as a helper and do not redeclare names from the "
    "preamble, including `_solution` names. Missing Mathlib names are not "
    "proof-failure evidence: search for the exact name, prove the needed "
    "fact from available ingredients, or pivot to a different proof route. "
    "Do not answer with helper-obligation sections, sorry-stub theorem "
    "declarations, or a helper-DAG plan unless a separate planner/"
    "decomposition prompt explicitly asks for that format."
)

_DECLARATION_REQUIRED_TURN_RULES = (
    "\n\nDeclaration-required graph formalization mode: this turn must "
    "materialize graph work as named Lean declarations. The generic proof "
    "turn instruction to finish with `example ...` or bare `by ...` is "
    "suspended for this turn. The final Lean block must contain complete "
    "`theorem`/`lemma` declarations, with the selected obligation/bridge as "
    "the final declaration. A proof body or anonymous `example` is the wrong "
    "artifact shape for this mode and will be rejected before root proof "
    "checking."
)


_ANSWER_PLACEHOLDER_RULES = (
    "\n"
    "`_solution` names are answer placeholders. If a `_solution` name is "
    "shown as an opaque axiom, infer its concrete value from the problem "
    "statement before proving. A proof whose substance is only unfolding or "
    "simplifying a `_solution` definition is not a mathematical proof. Do not "
    "say the theorem is unprovable merely because a `_solution` name is "
    "opaque. Do not invent unstated lemmas or self-reference the theorem being "
    "proved."
)


_LEAN_BLOCK_RULES = (
    "\n"
    "The proof body must be executable proof code with no `sorry`, no "
    "`admit`, and no holes — the orchestration rejects a proof that leaves "
    "the active goal open. If you need a mathematical bridge lemma, either "
    "prove it as a complete named helper before the final proof body, or use "
    "a local `have`/`suffices` target only when that target is also closed in "
    "the submitted proof. Do not emit sorry-stub helper "
    "declarations as a substitute for the active proof attempt; the next "
    "turn still needs proof code for the active goal.\n"
    "\n"
    "Avoid refusal/impossibility commentary in the Lean block. If you need a "
    "Mathlib name, use the available discovery and verification tools to "
    "confirm exact signatures before citing uncertain names. Do not ask the "
    "user to run Lean commands for you."
)


_LEAN_AUTHORITY_RULES = (
    "\n"
    "Lean is the only authority on whether your proof is correct. The "
    "rejection diagnostic on each failed turn tells you which step failed "
    "and what type Lean expected; read it before writing the next attempt. "
    "A rejection means this attempt is wrong; the underlying mathematical "
    "plan may still be correct, so isolate which step failed before "
    "deciding whether to repair the formalization or pivot the plan. "
    "Do not rationalize a rejected proof by claiming the kernel \"really "
    "knows\" the value, the lemma \"should\" exist, or the result is "
    "definitionally equal to something you wish it were. If the current route "
    "does not produce a proof Lean accepts, keep the search honest: repair the "
    "specific failed step or pivot to a different formal route. Do not paper "
    "over the gap in the "
    "main proof with sorry, admit, holes, self-references to the theorem being proved, or "
    "tautological junk like `lt_irrefl x x`. If a bridge lemma is missing, "
    "do not paper over it by writing an unproved local target with comments. "
    "A helper-stub-only response is not a proof of the main proof; do not "
    "use it as an off-ramp from the active goal. "
    "Either prove the bridge, manufacture a fully checked smaller lemma that "
    "supplies it, or replace the route with a smaller proof. "
    "Do not turn absence of a library lemma into the turn outcome. Do not "
    "manufacture contradictions to escape "
    "the goal: `False.elim`, `exfalso`, `contradiction`, impossible facts like "
    "`0 < 0`, or fake divisibility such as `0 ∣ n` are valid only when they "
    "follow from real hypotheses Lean can check. "
    "Before betting a turn on a hypothesis about how the goal reduces "
    "(e.g. expecting a particular rewrite to close, or expecting a goal "
    "to become `refl` after a tactic), frame the hypothesis as a small "
    "`by ...` body and test it with try_lean first; if try_lean rejects, "
    "the hypothesis is wrong and you should not submit a proof that "
    "depends on it.\n"
    "\n"
    "Lean style and lemma-naming rules (Mathlib stays current, your "
    "training data may not):\n"
    "- Use `simp [args]` rather than `simpa [args]` when no `using <hyp>` "
    "  clause follows. Use `simpa` only when you have `simpa using <h>` "
    "  or need the simp+exact composition. Lean may warn `try simp instead "
    "  of simpa`; treat that as style guidance and switch on the next turn, "
    "  but do not confuse the warning with the rejection cause when real "
    "  errors are also present.\n"
    "- When Lean reports a deprecation warning of the form "
    "  `'X' has been deprecated: Use 'Y' instead`, switch to `Y` on the "
    "  next turn. The replacement name in the message IS authoritative; "
    "  do not retry `X`.\n"
    "- Common renamings under recent Mathlib: `Int.ofNat_*` lemmas have "
    "  largely moved to `Nat.cast_*` (e.g., `Int.ofNat_mul` → "
    "  `Nat.cast_mul`); `Int.ofNat_eq_coe` → `Int.ofNat_eq_natCast`; "
    "  `Int.coe_nat_*` → `Nat.cast_*`. If the exact target name isn't "
    "  obvious, run `search_mathlib` or `apply_decl_to_goal` rather than "
    "  guessing.\n"
    "- If you see `unknownIdentifier` for a name you are confident "
    "  exists, the name has likely been renamed or moved to a different "
    "  namespace. Search Mathlib via the available tool BEFORE re-citing "
    "  the same name; do NOT emit the same name across multiple turns "
    "  if Lean rejected it once."
)


_PROOF_PATCH_RULES = (
    "\n"
    "When a previous long Lean proof attempt is close and the next Lean "
    "diagnostic points to a local edit, you may submit a fenced `lean-patch` "
    "block instead of regenerating the whole proof. Use exact "
    "search/replace hunks against the latest retained proof body:\n"
    "<<<<<<< SEARCH\n"
    "<copy exact old proof lines>\n"
    "=======\n"
    "<replacement lines>\n"
    ">>>>>>> REPLACE\n"
    "Or replace an inclusive proof-body line range with:\n"
    "@@ 45-50\n"
    "<replacement lines>\n"
    "The controller will reconstruct the full proof and Lean-check that "
    "patched proof. Use a full fenced `lean` block when the proof structure "
    "has changed globally."
)


PROVER_SYSTEM = (
    "You are solving a mathematics problem in Lean 4. Produce complete Lean "
    "proof artifacts for the active goal.\n"
    "\n"
    "Treat the task as verified proof search, not one-shot code generation. "
    "Maintain a small proof graph in your head: root goal, reusable helper "
    "lemmas, failed routes, and exact Mathlib facts verified by tools. Prefer "
    "Lean-checkable helper lemmas that unblock the root over long fragile "
    "proof scripts. Grow a verified local theory: define the right auxiliary "
    "objects, prove the smallest next local fact, and assemble those facts "
    "when the route is complete.\n"
    "\n"
    "You have a fixed turn budget for this proof phase. Spend each turn on a "
    "checkable artifact: a Lean proof attempt, a Lean patch against the latest "
    "attempt, or tool calls that directly support that artifact. Late turns "
    "should repair Lean errors without changing the mathematical route unless "
    "the route is actually wrong.\n"
    "\n"
    "On each proof turn, submit one Lean proof attempt for the active goal in "
    "a fenced ```lean block. Do not spend a reply on non-Lean commentary or "
    "lemma requests. The attempt may include fully proved helper declarations, "
    "but it must not use helper stubs as an off-ramp from proving the goal. If a "
    "non-Mathlib fact is needed, manufacture it as a proved local `have` or "
    "helper declaration in the same Lean block, not as prose."
    + _ANSWER_PLACEHOLDER_RULES
    + _LEAN_BLOCK_RULES
    + _LEAN_AUTHORITY_RULES
    + _PROOF_PATCH_RULES
    + _HELPER_RULES
)

REFINER_SYSTEM = (
    "You are taking over a stalled Lean proof. Read the transcript "
    "to recover the active goal, the attempted answer, and the Lean failures. "
    "Produce a cleaner checkable Lean proof artifact.\n"
    "\n"
    "Use the transcript as proof-search state: keep verified helpers, discard "
    "Lean-rejected routes unless the diagnostic points to a local fix, and "
    "introduce only helper lemmas that you can actually prove in Lean. Grow "
    "the local theory deliberately: each unavailable route fact should become "
    "the smallest checked lemma, definition, or local `have` that moves the "
    "proof closer to assembly.\n"
    "\n"
    "Use your fixed refiner turn budget deliberately: repair the formalization "
    "when Lean diagnostics point to a local fix, and pivot only when checked "
    "evidence shows the route is wrong. On each refiner turn, submit one Lean "
    "proof attempt for the active goal, or a `lean-patch` against the latest "
    "attempt. Do not spend a reply on non-Lean commentary or lemma requests. "
    "The attempt may include fully proved helper declarations, but do not use "
    "helper stubs as an off-ramp "
    "from repairing the goal. Do not end at "
    "context-availability commentary; manufacture or repair the next local "
    "fact inside the returned Lean artifact."
    + _ANSWER_PLACEHOLDER_RULES
    + _LEAN_BLOCK_RULES
    + _LEAN_AUTHORITY_RULES
    + _PROOF_PATCH_RULES
    + _HELPER_RULES
)

_PROMPT_REDACTION_TOKEN_RE = re.compile(
    r"(?:(?:\[?solution_ref)|code|identifier|helper_name|prompt_control)_hidden_[0-9a-f]{16}\]?"
)

_OFFICIAL_SOLUTION_SYMBOL_RE = re.compile(r"\bputnam_[A-Za-z0-9_'.]*_solution\b")
_OFFICIAL_SOLUTION_VALUE_DECL_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+"
    r"(putnam_[A-Za-z0-9_'.]*_solution)\b[\s\S]{0,800}?:="
)


def _text_has_official_solution_symbol(text: object) -> bool:
    return bool(_OFFICIAL_SOLUTION_SYMBOL_RE.search(str(text or "")))


def _text_has_official_solution_value_decl(text: object) -> bool:
    return bool(_OFFICIAL_SOLUTION_VALUE_DECL_RE.search(str(text or "")))


def _official_solution_symbol_names(text: object) -> Set[str]:
    return {
        str(match.group(0) or "").strip()
        for match in _OFFICIAL_SOLUTION_SYMBOL_RE.finditer(str(text or ""))
        if str(match.group(0) or "").strip()
    }


def _official_solution_value_decl_names(text: object) -> Set[str]:
    return {
        str(match.group(1) or "").strip()
        for match in _OFFICIAL_SOLUTION_VALUE_DECL_RE.finditer(str(text or ""))
        if str(match.group(1) or "").strip()
    }


def _expected_official_solution_name(theorem_name: object) -> str:
    name = str(theorem_name or "").strip()
    if not name.startswith("putnam_"):
        return ""
    if name.endswith("_solution"):
        return name
    return f"{name}_solution"


def _problem_has_official_answer_payload(problem: Any) -> bool:
    """Whether the problem carries a Putnam-style filled answer payload.

    ``--visible-answer-mode`` is meaningful only when there is an actual
    ``putnam_*_solution`` answer symbol whose checker preamble reveals a value.
    Non-Putnam theorem projects must not inherit benchmark/with-answer prompt
    framing just because a compatibility flag was supplied.
    """

    adapter_id = getattr(problem, "adapter_id", None)
    if adapter_id is not None and str(adapter_id) != PUTNAMBENCH_ADAPTER_ID:
        return False
    prompt_preamble = str(getattr(problem, "preamble", "") or "")
    checker_preamble = str(getattr(problem, "lean_preamble", "") or "")
    statement = str(getattr(problem, "statement_type", "") or "")
    theorem_name = str(getattr(problem, "theorem_name", "") or "")
    combined = "\n".join([prompt_preamble, checker_preamble, statement, theorem_name])
    if not _text_has_official_solution_symbol(combined):
        return False
    value_decl_names = _official_solution_value_decl_names(checker_preamble)
    if not value_decl_names:
        return False
    symbol_names = _official_solution_symbol_names(combined)
    if not (value_decl_names & symbol_names):
        return False
    expected_name = _expected_official_solution_name(theorem_name)
    if expected_name and expected_name in symbol_names:
        return expected_name in value_decl_names
    return True


def _problem_uses_solution_placeholder_policy(problem: Any) -> bool:
    """Whether benchmark-only ``*_solution`` safety rules apply."""

    adapter_id = getattr(problem, "adapter_id", None)
    if adapter_id is not None:
        return str(adapter_id) == PUTNAMBENCH_ADAPTER_ID
    # Preserve legacy duck-typed Putnam problem objects while ensuring every
    # canonical generic TheoremProblem (which has adapter_id="generic") is
    # excluded from the benchmark policy.
    return _problem_has_official_answer_payload(problem)


def _history_message_payload_chars(msg: Dict[str, Any]) -> int:
    """Approximate provider-visible message payload size for compaction metrics."""

    payload: Dict[str, Any] = {}
    for key in ("role", "content", "tool_call_id", "name", "tool_calls"):
        if key in msg:
            payload[key] = msg.get(key)
    try:
        return len(json.dumps(payload, sort_keys=True, default=str))
    except Exception:
        return len(str(payload))


def _conversation_has_official_answer_payload(conv: "Conversation") -> bool:
    explicit = getattr(conv, "official_answer_payload_present", None)
    if explicit is not None:
        return bool(explicit)
    combined = "\n".join(
        [
            str(getattr(conv, "goal_statement", "") or ""),
            str(getattr(conv, "lean_signature", "") or ""),
            str(getattr(conv, "preamble", "") or ""),
            str(getattr(conv, "lean_preamble", "") or ""),
        ]
    )
    if not _text_has_official_solution_symbol(combined):
        return False
    checker_preamble = str(getattr(conv, "lean_preamble", "") or "")
    visible_preamble = str(getattr(conv, "preamble", "") or "")
    value_decl_names = (
        _official_solution_value_decl_names(checker_preamble)
        or _official_solution_value_decl_names(visible_preamble)
    )
    if not value_decl_names:
        return False
    symbol_names = _official_solution_symbol_names(combined)
    if not (value_decl_names & symbol_names):
        return False
    theorem_match = re.search(r"\b(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)\b", combined)
    expected_name = (
        _expected_official_solution_name(theorem_match.group(1))
        if theorem_match is not None
        else ""
    )
    if expected_name and expected_name in symbol_names:
        return expected_name in value_decl_names
    return True

# ---------------------------------------------------------------------------
# Conversation state.
# ---------------------------------------------------------------------------

@dataclass
class Conversation:
    """Working memory for one prove-or-refine session against one goal.

    The proof loop defaults to answer-safe mode. ``preamble`` is the
    model-visible Lean context and may keep PutnamBench's opaque ``axiom``
    placeholders. ``lean_preamble`` is the checker context. In normal no-leak mode it is
    identical to ``preamble``; when tests or legacy callers provide a different
    checker preamble, ``run_conversation`` rechecks success and failure feedback
    against ``preamble`` before anything is shown or recorded.
    """

    role: str  # "prove" | "refine"
    goal_statement: str  # Lean type passed to LeanRunner.check()
    problem_text: str  # optional natural-language theorem description
    lean_signature: str  # full theorem decl as displayed to the LLM
    preamble: str  # LLM-visible context; answer-safe unless explicit visibility is allowed
    lean_preamble: str  # Lean checker context; normally identical to preamble
    turn_budget: Optional[int] = None
    known_premise_names: List[str] = field(default_factory=list)
    # Active repair-turn state. This is intentionally scoped to the latest
    # Lean-feedback repair, not the full conversation lifetime.
    rejected_code_fragments: List[str] = field(default_factory=list)
    # Lean's unsolved-goal targets from the latest repair feedback. Stored
    # separately from ``rejected_code_fragments`` (2026-05-13 regression
    # fix): these are pending-goal expressions, not LLM-written code, and
    # are gated by a narrow sorry-helper-repackaging detector — NOT the
    # strict identifier-bounded gate that ``rejected_code_fragments`` uses.
    # Banning the bare goal expression context-free (e.g. ``∃``) would
    # ban any honest existential proof; the narrow gate only catches the
    # specific abuse it was designed for.
    transient_goal_targets: List[str] = field(default_factory=list)
    repair_self_check_active: bool = False
    opaque_mode: bool = True
    allow_official_answer_visibility: bool = False
    official_answer_payload_present: Optional[bool] = None
    # Backward-compatible benchmark safety default. Canonical generic
    # theorem-project constructors always set this to False explicitly.
    suppress_solution_placeholders: bool = True
    # Some scoped sub-sessions are proof-only: their job is to prove the
    # current target or return Lean failure, not to recursively ask the
    # scheduler for new helper obligations. Root/problem sessions keep this
    # enabled so explicit helper decomposition remains available there.
    allow_helper_decomposition: bool = True
    history: List[Dict[str, Any]] = field(default_factory=list)

    def __post_init__(self) -> None:
        # A filled answer definition that is explicitly visible is a real
        # symbol throughout this conversation, including its Lean tools and
        # extraction gates. Do not retain the contradictory opaque-placeholder
        # flag inherited from the benchmark-safe dossier default.
        self.suppress_solution_placeholders = (
            effective_solution_placeholder_suppression(
                suppress_solution_placeholders=(
                    self.suppress_solution_placeholders
                ),
                opaque_mode=self.opaque_mode,
                allow_official_answer_visibility=(
                    self.allow_official_answer_visibility
                ),
                official_answer_payload_present=(
                    self.official_answer_payload_present
                ),
            )
        )

    def compact_history_for_next_turn(
        self,
        *,
        keep_recent_attempts: int = 1,
        max_summaries: int = 3,
    ) -> Dict[str, Any]:
        """Remove stale failed proof transcripts before the next LLM call.

        Older rejected proofs are high-token, high-salience examples of what
        not to do. Keeping the latest failed attempt plus the latest feedback
        preserves local repair context while avoiding repeated anchoring on
        obsolete code and old tool-search transcripts.
        """

        if not self.history:
            return {}
        keep_recent_attempts = max(1, int(keep_recent_attempts or 1))

        proof_attempt_indices = [
            i
            for i, msg in enumerate(self.history)
            if msg.get("role") == "assistant"
            and not msg.get("tool_calls")
            and str(msg.get("content", "") or "").strip()
        ]
        if len(proof_attempt_indices) <= keep_recent_attempts:
            return {}

        first_assistant = next(
            (
                i
                for i, msg in enumerate(self.history)
                if msg.get("role") == "assistant"
            ),
            proof_attempt_indices[-keep_recent_attempts],
        )
        boundary_pos = len(proof_attempt_indices) - keep_recent_attempts - 1
        if boundary_pos >= 0:
            # Keep the feedback and tool evidence that led into the first
            # retained proof attempt. Only the older failed proof turn(s) are
            # compacted away.
            keep_from = proof_attempt_indices[boundary_pos] + 1
        else:
            keep_from = first_assistant
        selected_work_prompts = [
            msg
            for msg in self.history
            if _is_stale_selected_work_context_message(msg)
        ]
        latest_selected_work_anchor = (
            selected_work_prompts[-1] if selected_work_prompts else None
        )
        if (
            latest_selected_work_anchor is not None
            and not str(
                latest_selected_work_anchor.get(
                    _GRAPH_SELECTED_WORK_SCOPE_KEY,
                    "",
                )
                or ""
            ).strip()
        ):
            # Unscoped legacy prompts cannot safely anchor target-local
            # history across compaction.
            latest_selected_work_anchor = None
        leading = [
            msg
            for msg in self.history[:first_assistant]
            if (
                not _is_history_compaction_summary(msg)
                or _is_stable_handoff_message(msg)
            )
            and not _is_stale_repair_feedback_message(msg)
            and (
                not _is_stale_selected_work_context_message(msg)
                or msg is latest_selected_work_anchor
            )
        ]
        preserved_from_removed = [
            msg
            for msg in self.history[first_assistant:keep_from]
            if (
                _is_stable_handoff_message(msg)
                or msg is latest_selected_work_anchor
            )
        ]
        removed = self.history[first_assistant:keep_from]
        raw_kept = self.history[keep_from:]
        anchor_in_tail = bool(
            latest_selected_work_anchor is not None
            and any(
                msg is latest_selected_work_anchor
                for msg in raw_kept
            )
        )
        if (
            anchor_in_tail
            and all(
                msg is not latest_selected_work_anchor
                for msg in (*leading, *preserved_from_removed)
            )
        ):
            # Keep the durable target anchor before the synthesized summary.
            # A later scope switch can then cut the anchor, the summary, and
            # every retained attempt as one target-local segment.
            preserved_from_removed.append(latest_selected_work_anchor)
        kept = _drop_stale_feedback_before_first_kept_attempt(
            [
                msg
                for msg in raw_kept
                if msg is not latest_selected_work_anchor
            ]
        )
        summaries = _summarize_compacted_attempts(
            self.history,
            [
                idx
                for idx in proof_attempt_indices
                if first_assistant <= idx < keep_from
            ][-max_summaries:],
        )
        removed_chars = sum(_history_message_payload_chars(msg) for msg in removed)
        summary_lines = [
            "[history compaction]",
            "Older rejected proof attempts and stale tool results were omitted from this prompt to avoid anchoring on failed code.",
            "Do not reuse an omitted proof shape merely because it appeared earlier; repair from the latest Lean feedback below.",
        ]
        if summaries:
            summary_lines.append("Compacted failure summary:")
            summary_lines.extend(summaries)
        tool_summaries = _summarize_compacted_tool_evidence(removed)
        if tool_summaries:
            summary_lines.append("Compacted tool evidence:")
            summary_lines.extend(tool_summaries)
        summary_lines.append(
            f"Omitted {len(removed)} message(s), including "
            f"{len(proof_attempt_indices) - keep_recent_attempts} older assistant proof attempt(s)."
        )
        self.history = [
            *leading,
            *preserved_from_removed,
            {"role": "user", "content": "\n".join(summary_lines)},
            *kept,
        ]
        return {
            "removed_messages": len(removed),
            "removed_chars": removed_chars,
            "older_attempts": len(proof_attempt_indices) - keep_recent_attempts,
            "kept_attempts": keep_recent_attempts,
        }

    def compact_history_for_refine_handoff(
        self,
        *,
        keep_recent_tool_rounds: Optional[int] = None,
        max_summaries: int = 6,
        force: bool = False,
        reason: str = "refine_handoff",
    ) -> Dict[str, Any]:
        """Summarize bulky prover tool exploration before refiner takeover.

        Ordinary history compaction is attempt-oriented: it keeps the latest
        assistant proof text and its local feedback. A distinct observed
        failure mode spent many
        tool rounds and then emitted no proof text, so the refiner inherited a
        large tool-only tail. This handoff compactor removes complete
        assistant-tool/tool-result rounds and replaces them with a small,
        explicitly untrusted evidence summary.
        """

        reason_key = re.sub(r"[^A-Za-z0-9_]+", "_", str(reason or "")).strip("_")
        if not reason_key:
            reason_key = "tool_history"
        done_key = (
            "_refine_handoff_compaction_done"
            if reason_key == "refine_handoff"
            else f"_{reason_key}_compaction_done"
        )
        if bool(getattr(self, done_key, False)) and not force:
            return {}
        try:
            setattr(self, done_key, True)
        except Exception:
            pass
        if not self.history:
            return {}
        if keep_recent_tool_rounds is None:
            keep_recent_tool_rounds = 3
        keep_recent_tool_rounds = max(0, int(keep_recent_tool_rounds or 0))

        history = list(self.history or [])
        tool_assistant_indices = [
            idx
            for idx, msg in enumerate(history)
            if msg.get("role") == "assistant" and msg.get("tool_calls")
        ]

        def complete_tool_round(index: int) -> bool:
            """Whether one assistant tool request has an exact result pairing."""

            raw_calls = list(history[index].get("tool_calls") or ())
            expected_ids = [
                str(call.get("id", "") or "")
                for call in raw_calls
                if isinstance(call, Mapping)
            ]
            if (
                not expected_ids
                or any(not call_id for call_id in expected_ids)
                or len(set(expected_ids)) != len(expected_ids)
            ):
                return False
            observed_ids: List[str] = []
            cursor = index + 1
            while cursor < len(history):
                result = history[cursor]
                if str(result.get("role", "") or "") != "tool":
                    break
                observed_ids.append(str(result.get("tool_call_id", "") or ""))
                cursor += 1
            return len(observed_ids) == len(expected_ids) and set(
                observed_ids
            ) == set(expected_ids)

        complete_tool_assistant_indices = [
            index for index in tool_assistant_indices if complete_tool_round(index)
        ]
        kept_tool_assistant_indices = set(
            complete_tool_assistant_indices[-keep_recent_tool_rounds:]
            if keep_recent_tool_rounds
            else ()
        )

        def bounded_recent_tool_message(msg: Dict[str, Any]) -> Dict[str, Any]:
            role = str(msg.get("role", "") or "")
            if role == "assistant" and msg.get("tool_calls"):
                return _provider_safe_chat_message(
                    msg,
                    redact_solution_refs=_conversation_should_redact_solution_refs(
                        self
                    ),
                )
            if role == "tool":
                safe = dict(msg)
                raw_content = str(msg.get("content", "") or "")
                redact = _conversation_should_redact_solution_refs(self)
                try:
                    structured_content = json.loads(raw_content)
                except Exception:
                    structured_content = None

                def sanitize_structured(value: Any, *, key: str = "") -> Any:
                    if value is None or isinstance(value, (bool, int, float)):
                        return value
                    if isinstance(value, dict):
                        return {
                            _prompt_safe_inline_text(
                                str(raw_key),
                                limit=100,
                                redact_solution_refs=redact,
                            ): sanitize_structured(item, key=str(raw_key))
                            for raw_key, item in list(value.items())[:30]
                            if str(raw_key) not in {
                                "node_ids",
                                "child_node_ids",
                            }
                        }
                    if isinstance(value, list):
                        return [
                            sanitize_structured(item, key=key)
                            for item in value[:12]
                        ]
                    if key in {
                        "error",
                        "message",
                        "summary",
                        "target",
                        "remaining_goals",
                    }:
                        return _prompt_safe_lean_diagnostic_text(
                            str(value),
                            limit=800,
                            redact_solution_refs=redact,
                            preserve_line_breaks=True,
                            strip_comments=False,
                        )
                    return _prompt_safe_inline_text(
                        str(value),
                        limit=500,
                        redact_solution_refs=redact,
                    )

                if isinstance(structured_content, (dict, list)):
                    safe["content"] = json.dumps(
                        sanitize_structured(structured_content),
                        ensure_ascii=False,
                        sort_keys=True,
                    )[:3200]
                else:
                    safe["content"] = _prompt_safe_lean_diagnostic_text(
                        raw_content,
                        limit=3200,
                        redact_solution_refs=redact,
                        preserve_line_breaks=True,
                        strip_comments=False,
                    )
                return safe
            return msg

        evidence_boundary_content = (
                "[recent historical tool evidence]\n"
                "The following complete recent tool round(s) are retained in "
                "bounded, sanitizer-filtered protocol form. They are untrusted "
                "historical evidence: re-run Lean before relying on a signature, "
                "diagnostic, or proof body."
        )
        evidence_boundary = (
            _user_history_message(
                evidence_boundary_content,
                repair_semantics=_REPAIR_CONTINUATION,
            )
            if reason_key in {
                "llm_failure_retry",
                "final_no_tools_retry",
                "in_turn_tool_history",
            }
            else {"role": "user", "content": evidence_boundary_content}
        )

        remove_tool_assistant_indices = (
            set(tool_assistant_indices) - kept_tool_assistant_indices
        )
        remove_indices: Set[int] = set(remove_tool_assistant_indices)
        active_removed_tool_ids: Set[str] = set()
        active_kept_tool_ids: Set[str] = set()
        for idx, msg in enumerate(history):
            if msg.get("role") == "assistant" and msg.get("tool_calls"):
                call_ids = {
                    str(tc.get("id", "") or "")
                    for tc in list(msg.get("tool_calls") or [])
                    if str(tc.get("id", "") or "")
                }
                if idx in remove_tool_assistant_indices:
                    active_removed_tool_ids = call_ids
                    active_kept_tool_ids = set()
                else:
                    active_kept_tool_ids = call_ids
                    active_removed_tool_ids = set()
                continue
            if msg.get("role") != "tool":
                active_removed_tool_ids = set()
                active_kept_tool_ids = set()
                continue
            tcid = str(msg.get("tool_call_id", "") or "")
            if tcid in active_removed_tool_ids:
                remove_indices.add(idx)
            elif tcid not in active_kept_tool_ids:
                remove_indices.add(idx)

        if not remove_indices:
            if not tool_assistant_indices:
                return {}
            # Even when every complete tool round is retained (≤ keep_recent),
            # still insert the evidence boundary and sanitize payloads. For
            # final_no_tools_retry the boundary carries repair_continuation so
            # this does not kill an active repair cycle the way a plain EB
            # would. Skipping this left oversized unsanitized tool bodies in
            # the retry prompt.
            first_tool = tool_assistant_indices[0]
            self.history = [
                *history[:first_tool],
                evidence_boundary,
                *(
                    bounded_recent_tool_message(msg)
                    for msg in history[first_tool:]
                ),
            ]
            return {
                "removed_messages": 0,
                "removed_chars": 0,
                "removed_tool_rounds": 0,
                "removed_tool_messages": 0,
                "kept_tool_rounds": len(kept_tool_assistant_indices),
                "reason": reason_key,
            }

        removed = [msg for idx, msg in enumerate(history) if idx in remove_indices]
        removed_chars = sum(_history_message_payload_chars(msg) for msg in removed)
        removed_tool_rounds = sum(
            1
            for msg in removed
            if msg.get("role") == "assistant" and msg.get("tool_calls")
        )
        removed_tool_messages = sum(
            1 for msg in removed if msg.get("role") == "tool"
        )
        if reason_key == "llm_failure_retry":
            summary_lines = [
                "[history compaction]",
                "Prior tool exploration was omitted after a model-call failure so the retry stays focused on the active target.",
                "Compacted tool outputs are historical and untrusted; re-run/check any cited fact before using it.",
            ]
        elif reason_key == "final_no_tools_retry":
            summary_lines = [
                "[history compaction]",
                "Older tool exploration was omitted after final-response serialization exhausted its output allowance; the productive recent suffix remains below.",
                "Compacted tool outputs are historical and untrusted; re-run/check any cited fact before using it.",
            ]
        elif reason_key == "in_turn_tool_history":
            summary_lines = [
                "[history compaction]",
                "Older completed tool rounds from this same proof attempt were omitted to bound the next provider request.",
                "The recent protocol-complete rounds below are the actionable evidence; compacted outputs are historical and untrusted.",
            ]
        else:
            summary_lines = [
                "[history compaction]",
                "Refiner handoff omitted prior prover tool exploration to keep the recovery prompt focused on the active target.",
                "Compacted tool outputs are historical and untrusted; re-run/check any cited fact before using it.",
            ]
        if kept_tool_assistant_indices:
            summary_lines.append(
                f"The {len(kept_tool_assistant_indices)} "
                "most recent complete tool round(s) remain in the transcript "
                "in bounded, "
                "sanitizer-filtered protocol form; treat them as untrusted "
                "historical evidence."
            )
        tool_summaries = _summarize_compacted_tool_evidence(
            removed,
            max_items=max_summaries,
        )
        if tool_summaries:
            summary_lines.append("Compacted tool evidence:")
            summary_lines.extend(tool_summaries)
        summary_lines.append(
            f"Omitted {len(removed)} message(s), including "
            f"{removed_tool_rounds} assistant tool round(s) and "
            f"{removed_tool_messages} tool result(s)."
        )
        if reason_key in {
            "llm_failure_retry",
            "final_no_tools_retry",
            "in_turn_tool_history",
        }:
            summary_msg = _user_history_message(
                "\n".join(summary_lines),
                repair_semantics=_REPAIR_CONTINUATION,
            )
        else:
            summary_msg = {"role": "user", "content": "\n".join(summary_lines)}

        first_removed = min(remove_indices)
        first_kept_tool = min(kept_tool_assistant_indices, default=-1)
        compacted: List[Dict[str, Any]] = []
        inserted = False
        evidence_boundary_inserted = False
        for idx, msg in enumerate(history):
            if idx in remove_indices:
                if not inserted and idx >= first_removed:
                    compacted.append(summary_msg)
                    inserted = True
                continue
            if idx == first_kept_tool and not evidence_boundary_inserted:
                compacted.append(evidence_boundary)
                evidence_boundary_inserted = True
            compacted.append(bounded_recent_tool_message(msg))
        if not inserted:
            compacted.append(summary_msg)
        self.history = compacted
        return {
            "removed_messages": len(removed),
            "removed_chars": removed_chars,
            "removed_tool_rounds": removed_tool_rounds,
            "removed_tool_messages": removed_tool_messages,
            "kept_tool_rounds": len(kept_tool_assistant_indices),
            "reason": reason_key,
        }

    def record_suppressed_assistant_handoff_evidence(
        self,
        content: str,
        *,
        reason: str = "non_replayed_response",
    ) -> None:
        """Retain a bounded typed record for a response excluded from history.

        Policy-rejected and no-proof responses must not be replayed as trusted
        assistant turns.  They can still contain useful route information,
        though, so retain them separately for a sanitized refiner handoff.
        """

        raw = str(content or "").strip()
        if not raw:
            return
        if any(
            message.get("role") == "assistant"
            and str(message.get("content") or "").strip() == raw
            for message in list(self.history or ())
            if isinstance(message, Mapping)
        ):
            return
        clean_reason = str(reason or "non_replayed_response").strip()[:160]
        evidence_hash = text_hash(f"{clean_reason}\0{raw}")
        records = [
            dict(item)
            for item in list(
                getattr(self, "_suppressed_assistant_handoff_evidence", []) or []
            )
            if isinstance(item, Mapping)
        ]
        if any(
            str(item.get("evidence_hash") or "") == evidence_hash
            for item in records
        ):
            return
        records.append({
            "schema_version": 1,
            "reason": clean_reason,
            "content": raw[:12000],
            "evidence_hash": evidence_hash,
        })
        self._suppressed_assistant_handoff_evidence = records[-8:]

    def append_suppressed_draft_handoff_summary(
        self,
        *,
        max_items: int = 3,
        max_item_chars: int = 900,
    ) -> Dict[str, Any]:
        """Expose non-replayed prover evidence to a refiner without authority.

        The synthesized user message is sanitizer-filtered and explicitly says
        that none of the material was accepted by Lean or by the proof policy.
        It therefore carries useful search state without turning a rejected
        draft into an assistant assertion or a named mathematical fact.
        """

        if bool(getattr(self, "_suppressed_draft_handoff_summary_done", False)):
            return {}
        candidates: List[Dict[str, str]] = []
        for item in list(
            getattr(self, "_suppressed_assistant_handoff_evidence", []) or []
        ):
            if not isinstance(item, Mapping):
                continue
            candidates.append({
                "reason": str(item.get("reason") or "non_replayed_response"),
                "content": str(item.get("content") or ""),
            })
        for raw in list(getattr(self, "_no_proof_llm_responses", []) or []):
            candidates.append({"reason": "no_main_proof", "content": str(raw or "")})
        for attr, reason in (
            ("_last_rejected_llm_response", "policy_rejected"),
            ("_last_llm_content", "latest_non_replayed_response"),
        ):
            candidates.append({
                "reason": reason,
                "content": str(getattr(self, attr, "") or ""),
            })

        assistant_contents = {
            str(message.get("content") or "").strip()
            for message in list(self.history or ())
            if isinstance(message, Mapping) and message.get("role") == "assistant"
        }
        unique: List[Dict[str, str]] = []
        seen: set[str] = set()
        for item in candidates:
            raw = str(item.get("content") or "").strip()
            if not raw or raw in assistant_contents:
                continue
            digest = text_hash(raw)
            if digest in seen:
                continue
            seen.add(digest)
            unique.append({"reason": str(item.get("reason") or ""), "content": raw})
        item_limit = max(0, int(max_items or 0))
        selected = unique[-item_limit:] if item_limit else []
        if not selected:
            return {}

        redact = _conversation_should_redact_solution_refs(self)
        lines = [
            "[prover handoff evidence]",
            "The following bounded excerpts came from prover responses that were not accepted as proof attempts and were deliberately excluded from assistant history. They are untrusted search evidence only: do not cite them as facts or reuse code without a fresh Lean check.",
        ]
        rendered_count = 0
        for item in selected:
            reason = _prompt_safe_inline_text(
                item.get("reason", "non_replayed_response"),
                limit=120,
                redact_solution_refs=redact,
            )
            excerpt = _prompt_safe_lean_diagnostic_text(
                item.get("content", ""),
                limit=max(120, int(max_item_chars or 0)),
                redact_solution_refs=redact,
                preserve_line_breaks=True,
            )
            if not excerpt:
                continue
            rendered_count += 1
            lines.append(f"- rejected response ({reason or 'unspecified'}):")
            lines.extend(f"  {line}" for line in excerpt.splitlines())
        if not rendered_count:
            return {}
        self.ensure_bootstrap()
        handoff_message = _user_history_message(
            "\n".join(lines),
            repair_semantics=_REPAIR_CONTINUATION,
        )
        # This is the only model-visible projection of responses deliberately
        # excluded from assistant history.  Keep the bounded projection during
        # ordinary provider overflow pruning; request serialization strips the
        # internal marker before dispatch.
        handoff_message["preserve_context"] = True
        self.history.append(handoff_message)
        self._suppressed_draft_handoff_summary_done = True
        return {
            "rendered_items": rendered_count,
            "candidate_items": len(unique),
        }

    def system_prompt(self) -> str:
        prompt = {
            "prove": PROVER_SYSTEM,
            "refine": REFINER_SYSTEM,
        }[self.role]
        if not _conversation_should_redact_solution_refs(self):
            prompt = prompt.replace(_ANSWER_PLACEHOLDER_RULES, "")
            prompt = prompt.replace(
                ", including `_solution` names",
                "",
            )
        if bool(getattr(self, "declaration_required_submission", False)):
            prompt = prompt.replace(
                _HELPER_RULES,
                _DECLARATION_REQUIRED_HELPER_RULES,
            )
            prompt += _DECLARATION_REQUIRED_TURN_RULES
        if not bool(getattr(self, "allow_helper_decomposition", True)):
            prompt += (
                "\n\nDirect-proof sub-session: do not emit `Proposed helper "
                "obligations`, sorry-stub theorem declarations, helper-DAG "
                "plans, or requests for the scheduler to prove a new bridge "
                "inside this reply. Submit executable proof code for the "
                "active target. Any helper declaration you include must be "
                "fully proved in the same Lean block and used by the active "
                "proof. Absence of a convenient Mathlib lemma is not a turn "
                "outcome; search, prove the bridge locally, pivot the proof "
                "route, or expose a concrete Lean failure from the attempted "
                "local proof. Do not describe the bridge as unavailable."
            )
        return prompt

    def _role_label(self) -> str:
        return self.role

    def initial_user_message(self) -> str:
        preamble_label = "Lean preamble (answer-safe imports / open / axioms):"
        has_answer_payload = _conversation_has_official_answer_payload(self)
        if not has_answer_payload:
            preamble_label = "Lean preamble (imports / open / definitions):"
            placeholder_note = (
                "Important: solve the displayed Lean target directly. The "
                "preamble is the local proof environment for this theorem; "
                "missing route facts are mathematical development obligations, "
                "not evidence that the target should be bypassed. Build any "
                "needed local theory as checked helper declarations or closed "
                "`have` steps, then assemble the active proof."
            )
        elif self.opaque_mode or not self.allow_official_answer_visibility:
            placeholder_note = (
                "Important: this is an answer-safe view of the preamble. "
                "`putnam_..._solution` names are answer placeholders shown "
                "opaquely so the value is not supplied. Infer the answer from the "
                "problem statement; do not treat opacity as evidence that the "
                "theorem is unprovable."
            )
        else:
            preamble_label = "Lean preamble (imports / open / definitions):"
            placeholder_note = (
                "Important: this run is in visible-answer mode. The preamble may "
                "include filled reference `_solution` definitions from PutnamBench. "
                "Those definitions reveal target answer values for with-answer "
                "controls only; they are not proof facts, and unfolding or "
                "simplifying a `_solution` value is not a proof of the problem. "
                "When unfolding a `_solution` shell leaves a nontrivial active "
                "goal, that active goal is the mathematical target; do not "
                "prove by vacuity or reason from the RHS value as if it were "
                "evidence for the LHS. "
                "Do not cite a problem-specific Putnam theorem from Mathlib unless "
                "a tool has shown that exact declaration exists. Use this mode only "
                "for with-answer controls, not no-answer benchmark runs."
            )
        parts = [
            f"Problem (natural language):\n{self.problem_text.strip()}",
            f"Lean signature:\n{self.lean_signature.strip()}",
            f"{preamble_label}\n{self.preamble.strip()}",
            self._turn_budget_note(),
            placeholder_note,
            (
                "Direct-proof sub-session: work the displayed Lean target "
                "directly in this reply. Fully prove any local bridge you "
                "introduce; if a bridge remains unproved, expose it through "
                "a concrete Lean attempt and diagnostic rather than prose "
                "about availability."
                if not bool(getattr(self, "allow_helper_decomposition", True))
                else ""
            ),
            "Produce a checkable Lean proof artifact for the active goal.",
        ]
        return "\n\n".join(part for part in parts if str(part or "").strip())

    def _turn_budget_note(self) -> str:
        try:
            budget = int(self.turn_budget or 0)
        except Exception:
            budget = 0
        if budget > 0:
            return (
                f"Turn budget: you have {budget} {self._role_label()} turn(s) in this "
                "phase. Use the first attempts to produce checkable Lean proof "
                "artifacts, then spend remaining turns on Lean repair."
            )
        return (
            "Turn budget: you have a small fixed number of turns. Produce "
            "checkable Lean proof artifacts first, then spend remaining turns "
            "on Lean repair."
        )

    def messages_for_llm(self) -> List[Dict[str, Any]]:
        msgs: List[Dict[str, Any]] = [
            {"role": "system", "content": self.system_prompt()},
        ]
        if not self.history:
            msgs.append({"role": "user", "content": self.initial_user_message()})
        else:
            redact_solution_refs = _conversation_should_redact_solution_refs(self)
            msgs.extend(
                _provider_safe_chat_message(
                    msg,
                    redact_solution_refs=redact_solution_refs,
                )
                for msg in self.history
            )
        return msgs

    def ensure_bootstrap(self) -> None:
        """Ensure the initial user message is in history.

        ``messages_for_llm`` synthesizes ``[system, initial_user]`` only when
        history is empty; once anything else is appended directly to history,
        that synthesized initial-user disappears. Call this before any direct
        ``history.append(...)`` (e.g. tool-call path) so the original problem
        statement remains visible to subsequent LLM calls in the same turn.
        """
        if not self.history:
            self.history.append(
                _user_history_message(
                    self.initial_user_message(),
                    repair_semantics=_REPAIR_BOUNDARY,
                )
            )

    def append_assistant(self, content: str) -> None:
        # Ensure the first user turn is in history before any assistant turn,
        # so a refiner taking over sees the original problem statement.
        self.ensure_bootstrap()
        self.history.append({"role": "assistant", "content": content})

    def append_user(
        self,
        content: str,
        *,
        repair_semantics: Optional[str] = None,
        repair_payload: Optional[Dict[str, Sequence[str]]] = None,
    ) -> Dict[str, Any]:
        # CRITICAL: bootstrap before appending so the initial user message
        # (problem statement + Lean preamble + no-leak placeholder note) is
        # always present in history. Without this, ``messages_for_llm``'s
        # bootstrap path is bypassed (since history is no longer empty
        # after the first append) and the model would see only the
        # post-bootstrap user messages — missing the actual problem.
        # Mirrors ``append_assistant``'s pattern.
        #
        # Repair-state (rejected_code_fragments / transient_goal_targets /
        # repair_self_check_active) is NOT cached on the instance any more
        # — readers derive it from ``self.history`` via
        # ``_repair_feedback_texts_in_current_cycle`` (B1-B4 structural fix,
        # 2026-05-18 audit). The previous cache-write branches here suffered
        # asymmetric updates (Branch B), survived history mutations
        # (compaction, history reset, role transition), and could poison
        # gates against content the LLM could no longer see in its
        # transcript. Deriving from history removes the staleness vector
        # entirely.
        if (
            repair_semantics is None
            and _repair_feedback_messages_in_current_cycle(self)
            and not _is_explicit_repair_boundary_content(content)
        ):
            repair_semantics = _REPAIR_FEEDBACK
        effective_repair_semantics = _normalise_repair_semantics(
            repair_semantics
        ) or _infer_repair_semantics_for_user_content(content)
        carry_repair_payload: Optional[Dict[str, Sequence[str]]] = None
        if effective_repair_semantics == _REPAIR_FEEDBACK:
            own_fragments = _rejected_fragments_from_feedback_text(content)
            own_targets = _transient_goal_targets_from_feedback_text(content)
            explicit_payload_fresh = bool(
                repair_payload
                and (
                    repair_payload.get("fragments")
                    or repair_payload.get("transient_goal_targets")
                )
            )
            fresh_payload = bool(own_fragments or own_targets or explicit_payload_fresh)
            payload_parts: Dict[str, List[str]] = {
                "fragments": [],
                "transient_goal_targets": [],
            }
            if _repair_feedback_messages_in_current_cycle(self) and not fresh_payload:
                previous_payload = _repair_payload_from_current_cycle(self)
                payload_parts["fragments"].extend(
                    previous_payload.get("fragments", [])
                )
                payload_parts["transient_goal_targets"].extend(
                    previous_payload.get("transient_goal_targets", [])
                )
            if repair_payload:
                payload_parts["fragments"].extend(
                    list(repair_payload.get("fragments", []) or [])
                )
                payload_parts["transient_goal_targets"].extend(
                    list(repair_payload.get("transient_goal_targets", []) or [])
                )
            carry_repair_payload = (
                payload_parts
                if payload_parts["fragments"]
                or payload_parts["transient_goal_targets"]
                else None
            )
        payload_reset_candidate = bool(
            getattr(self, _REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY, False)
        )
        self.ensure_bootstrap()
        msg = _user_history_message(
            content,
            repair_semantics=effective_repair_semantics,
            repair_payload=carry_repair_payload,
            payload_reset_candidate=payload_reset_candidate,
        )
        self.history.append(msg)
        if payload_reset_candidate and (
            bool(msg.get(_REPAIR_PAYLOAD_RESET_BEFORE_KEY))
            or _message_repair_semantics(msg) == _REPAIR_BOUNDARY
        ):
            setattr(self, _REPAIR_DROPPED_ASSISTANT_BEFORE_FEEDBACK_KEY, False)
        return msg

    def clear_repair_state(self) -> None:
        """No-op kept for backward compatibility with external callers.

        Repair-state is derived from ``conv.history`` by readers via
        ``_repair_feedback_texts_in_current_cycle`` (B1-B4 fix, 2026-05-18).
        There is no cached state to clear; mutating history (or simply
        appending a non-repair user message) ends the repair cycle as the
        invariant requires.
        """

        # Vestigial dataclass fields are left in place for any code path that
        # still reads them attributively — they remain at their __init__
        # defaults (empty lists / False) for the entire conversation lifetime.

    def sanitize_orphan_tool_calls(self) -> int:
        """Repair historical assistant/tool exchanges before replay.

        This appends synthetic ``tool`` results for orphan assistant
        ``tool_calls`` and uniquifies duplicate call ids within one exchange so
        the transcript stays well-formed for the next
        OpenAI call.

        Bonus #4 fix (2026-05-08): the per-tc try/except added by B1 closes
        the orphan window inside ``run_conversation``'s main loop, but the
        recursive controller hands ``subgoal_conv`` to a refiner *after*
        the prover may have crashed somewhere outside the audited path
        (e.g. a future tool runner not yet wrapped, an exception on a
        pre-call helper that bypasses B1's wrapper, or a transcript built
        by an older code path). This sanitizer is defense-in-depth: it
        scans ``history`` and ensures every advertised ``tool_call_id``
        on an assistant message has a matching ``tool`` message before
        the NEXT assistant turn. Orphans get a synthetic tool message
        explaining the missing result so OpenAI returns 200 instead of
        a 400 ``tool_call_id has no corresponding tool message``.

        Returns the number of transcript repairs applied.
        """

        if not self.history:
            return 0
        # Index assistant messages with tool_calls and their advertised IDs.
        # Build the new history by streaming through and patching as we go.
        patched: List[Dict[str, Any]] = []
        repair_count = 0
        i = 0
        n = len(self.history)
        while i < n:
            msg = self.history[i]
            if msg.get("role") == "assistant" and msg.get("tool_calls"):
                remapped_ids: List[Tuple[str, str]] = []
                used_ids: set[str] = set()
                patched_msg = dict(msg)
                patched_tool_calls: List[Dict[str, Any]] = []
                for tc_index, tc in enumerate(msg.get("tool_calls") or []):
                    if not isinstance(tc, dict):
                        continue
                    patched_tc = dict(tc)
                    raw_id = str(patched_tc.get("id", "") or "")
                    base = raw_id or f"call_repaired_{i}_{tc_index + 1}"
                    candidate = base
                    suffix = 2
                    while not candidate or candidate in used_ids:
                        candidate = f"{base or 'call_repaired'}__{suffix}"
                        suffix += 1
                    used_ids.add(candidate)
                    if candidate != raw_id:
                        patched_tc["id"] = candidate
                        repair_count += 1
                    remapped_ids.append((raw_id, candidate))
                    patched_tool_calls.append(patched_tc)
                patched_msg["tool_calls"] = patched_tool_calls
                patched.append(patched_msg)
                # Collect contiguous ``tool`` messages that follow this
                # assistant turn until the NEXT non-tool message.
                tool_messages: List[Dict[str, Any]] = []
                j = i + 1
                while j < n and self.history[j].get("role") == "tool":
                    tool_messages.append(dict(self.history[j]))
                    j += 1
                assigned_tool_ids: Dict[int, str] = {}
                consumed_tool_indices: set[int] = set()
                for original_id, repaired_id in remapped_ids:
                    for tool_index, tool_msg in enumerate(tool_messages):
                        if tool_index in consumed_tool_indices:
                            continue
                        tcid = str(tool_msg.get("tool_call_id", "") or "")
                        if tcid != original_id:
                            continue
                        consumed_tool_indices.add(tool_index)
                        assigned_tool_ids[tool_index] = repaired_id
                        break
                seen_ids: set[str] = set()
                for tool_index, tool_msg in enumerate(tool_messages):
                    repaired_id = assigned_tool_ids.get(tool_index)
                    if repaired_id:
                        if tool_msg.get("tool_call_id") != repaired_id:
                            tool_msg["tool_call_id"] = repaired_id
                            repair_count += 1
                        seen_ids.add(repaired_id)
                        patched.append(tool_msg)
                    else:
                        repair_count += 1
                # For every advertised id that has no matching tool
                # message, append a synthetic tool message keyed to that
                # id. OpenAI requires ALL advertised ids to be answered
                # before the next assistant message.
                for _original_id, advertised_id in remapped_ids:
                    if advertised_id and advertised_id not in seen_ids:
                        patched.append(
                            {
                                "role": "tool",
                                "tool_call_id": advertised_id,
                                "content": (
                                    "(tool result unavailable — the runner "
                                    "did not produce a response. Treat this "
                                    "as 'call abandoned' and proceed.)"
                                ),
                            }
                        )
                        repair_count += 1
                i = j
                continue
            patched.append(msg)
            i += 1
        if repair_count:
            self.history = patched
        return repair_count


def _llm_visible_preamble_for_problem(
    problem: TheoremProblem,
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
) -> str:
    """Return the LLM-facing preamble for a problem.

    ``opaque_mode`` only controls answer visibility. Showing a filled official
    answer definition to the LLM requires both the explicit capability bit and
    an actual adapter-declared answer payload. Generic theorem-project inputs
    keep the ordinary prompt/checker preamble without benchmark framing.
    """

    if official_answer_visible_to_llm(
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=_problem_has_official_answer_payload(problem),
    ):
        return str(getattr(problem, "lean_preamble", "") or problem.preamble)
    return str(problem.preamble)


def _lean_checker_preamble_for_problem(
    problem: TheoremProblem,
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
) -> str:
    """Return executable context without widening benchmark answer access."""

    official_visible = _official_answer_visible_to_llm(
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=_problem_has_official_answer_payload(problem),
    )
    if official_visible:
        return str(getattr(problem, "lean_preamble", "") or problem.preamble)
    answer_safe = str(
        getattr(problem, "adapter_metadata", {}).get(
            "answer_safe_lean_preamble", ""
        )
        or ""
    )
    if answer_safe:
        return answer_safe
    adapter_id = str(getattr(problem, "adapter_id", "") or "")
    if adapter_id != GENERIC_ADAPTER_ID:
        # Compatibility/legacy PutnamProblem instances may predate the
        # encoded answer-safe checker field. Never fall through to their
        # filled lean_preamble unless visibility was explicitly authorized.
        return str(problem.preamble)
    return str(getattr(problem, "lean_preamble", "") or problem.preamble)


def _official_answer_visible_to_llm(
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> bool:
    """Whether filled PutnamBench answer definitions were prompt-visible."""

    return official_answer_visible_to_llm(
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        official_answer_payload_present=official_answer_payload_present,
    )


def _answer_visibility_label(
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> str:
    """Summary/export label for the actual official-answer visibility."""

    return (
        "visible"
        if _official_answer_visible_to_llm(
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        else "opaque"
    )


def _putnambench_answer_variant_label(
    *,
    opaque_mode: bool,
    allow_official_answer_visibility: bool = False,
    official_answer_payload_present: Optional[bool] = None,
) -> str:
    """Classifier used by run summaries and solved-run export selection."""

    return (
        "with_answer"
        if _official_answer_visible_to_llm(
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
        else "no_answer"
    )


def _active_root_targets_match_frame(
    targets: Sequence[Dict[str, Any]],
    *,
    root_statement: str,
    preamble: str,
    helper_blocks: Sequence[str] = (),
    require_helper_context_hash_match: bool = False,
) -> bool:
    """Return whether cached active roots belong to this root/preamble frame."""

    return dossier_active_root_targets_match_frame(
        targets,
        root_statement=root_statement,
        preamble=preamble,
        helper_blocks=helper_blocks,
        require_helper_context_hash_match=require_helper_context_hash_match,
    )


async def _record_visible_answer_active_root_targets(
    *,
    dossier: Optional[ProofDossier],
    lean: LeanRunner,
    root_statement: str,
    preamble: str,
    official_answer_visible: bool,
    timeout_s: float,
    recorder: Optional[RunRecorder] = None,
    trace_prefix: str = "",
    accepted_root_proof_out: Optional[Dict[str, Any]] = None,
) -> List[Dict[str, Any]]:
    """Populate active-root goals for every visible-answer proof path.

    The recursive planner already probes ``simp [_solution]`` before planning.
    Bare legacy runs need the same target-frame correction; otherwise the LLM
    sees only the original ``P ↔ _solution`` shell and keeps treating the answer
    value as mathematical evidence.
    """

    if dossier is None:
        return []
    if not official_answer_visible:
        # Active-root targets are derived from materialized answer values. If a
        # dossier is reused in opaque/no-answer mode, stale targets must not
        # keep steering prompts or tools.
        dossier.active_root_targets = []
        classifier = getattr(
            dossier,
            "activate_active_root_classification_preamble",
            None,
        )
        if callable(classifier):
            classifier("")
        return []
    classifier = getattr(
        dossier,
        "activate_active_root_classification_preamble",
        None,
    )
    if callable(classifier):
        classifier(preamble)
    existing = [
        dict(item)
        for item in list(getattr(dossier, "active_root_targets", []) or ())
        if isinstance(item, dict) and str(item.get("target") or "").strip()
    ]
    try:
        helpers = dossier.verified_helper_blocks()
    except Exception:
        helpers = []
    if existing:
        framed_existing = active_root_targets_for_frame(
            existing,
            root_statement=root_statement,
            preamble=preamble,
            helper_blocks=helpers,
            require_helper_context_hash_match=True,
        )
        if framed_existing:
            dossier.record_active_root_targets(framed_existing)
            return framed_existing
        dossier.active_root_targets = []
        _trace(
            trace_prefix,
            "=== visible-answer active-root probe refreshing stale target "
            "cache for current root/preamble frame ===",
        )
    probe_inconclusive = False

    def record_probe_event(event: Dict[str, Any]) -> None:
        nonlocal probe_inconclusive
        if (
            accepted_root_proof_out is not None
            and str(event.get("verdict") or "")
            == "active_root_simplification_proof_accepted"
        ):
            proof = str(event.get("proof") or "").strip()
            if proof:
                accepted_root_proof_out.clear()
                accepted_root_proof_out.update(dict(event))
        if str(event.get("verdict") or "").endswith(
            "infrastructure_unknown_retryable"
        ):
            probe_inconclusive = True
            _trace(
                trace_prefix,
                "=== visible-answer active-root probe was inconclusive; "
                "the verifier operation can be retried ===",
            )
        if recorder is not None:
            recorder.record_turn(dict(event))

    targets = await _probe_active_root_targets(
        lean=lean,
        root_statement=root_statement,
        preamble=preamble,
        helpers=helpers,
        timeout_s=timeout_s,
        record_event=record_probe_event,
    )
    if not targets:
        if accepted_root_proof_out:
            _trace(
                trace_prefix,
                "=== visible-answer active-root probe accepted a complete "
                "root proof ===",
            )
        elif not probe_inconclusive:
            _trace(
                trace_prefix,
                "=== visible-answer active-root probe: no nontrivial "
                "post-simplification goal ===",
            )
        return []
    root_key = canonical_dossier_statement_key(root_statement)
    preamble_hash = text_hash(preamble)
    helper_context_hash = text_hash(
        "\n".join(sorted(str(block or "").strip() for block in helpers if str(block or "").strip()))
    )
    dossier.record_active_root_targets(
        [
            {
                **dict(item),
                "root_statement_key": root_key,
                "preamble_hash": preamble_hash,
                "helper_context_hash": helper_context_hash,
                "official_answer_visible": "1",
            }
            for item in list(targets or ())
            if isinstance(item, dict)
        ]
    )
    cleaned = list(getattr(dossier, "active_root_targets", []) or [])
    _trace(
        trace_prefix,
        "=== visible-answer active-root probe extracted "
        f"{len(cleaned)} authoritative target(s) ===",
    )
    if recorder is not None:
        recorder.record_turn(
            {
                "phase": "visible_answer_active_target",
                "targets": copy.deepcopy(cleaned),
                "verdict": "active_root_targets_extracted",
            }
        )
    return cleaned


# ---------------------------------------------------------------------------
# Proof extraction. We reuse the v1 candidate extractor because it already
# handles ```lean fences, comment-stripping, and dedup robustly.
# ---------------------------------------------------------------------------





def _is_retryable_llm_exception(exc: BaseException) -> bool:
    """Return whether one immediate LLM-call retry is worth attempting."""
    return is_retryable_llm_exception(exc)


def _callable_accepts_keyword(func: Any, key: str) -> bool:
    try:
        signature = inspect.signature(func)
    except (TypeError, ValueError):
        return True
    parameters = signature.parameters
    if key in parameters:
        return True
    return any(
        parameter.kind is inspect.Parameter.VAR_KEYWORD
        for parameter in parameters.values()
    )


async def _metered_or_plain_call_compat(
    *,
    retryable_exception_no_charge: Optional[Callable[[BaseException], bool]] = None,
    **kwargs: Any,
) -> Any:
    """Call current or pre-no-charge metering shims without hard failing."""

    if retryable_exception_no_charge is not None and _callable_accepts_keyword(
        metered_or_plain_call,
        "retryable_exception_no_charge",
    ):
        kwargs["retryable_exception_no_charge"] = retryable_exception_no_charge
    return await metered_or_plain_call(**kwargs)




def _messages_with_dossier_context(
    messages: List[Dict[str, Any]],
    dossier: Optional[ProofDossier],
    *,
    goal_statement: str = "",
    preamble: str = "",
    context_lemmas: Sequence[str] = (),
) -> List[Dict[str, Any]]:
    """Attach the proof workbench snapshot as a synthetic user message."""
    if dossier is None:
        return messages
    context = dossier.render_context(
        current_goal_statement=goal_statement,
        current_preamble=preamble,
        current_context_lemmas=context_lemmas,
    )
    if not context:
        return messages
    return _messages_with_reference_context(
        messages,
        [{"role": "user", "content": context}],
    )


def _single_active_root_target(
    dossier: Optional[ProofDossier],
    *,
    active_root_targets: Optional[Sequence[Mapping[str, Any]]] = None,
) -> Optional[Dict[str, Any]]:
    if dossier is None and active_root_targets is None:
        return None
    raw_targets = (
        list(active_root_targets or ())
        if active_root_targets is not None
        else list(getattr(dossier, "active_root_targets", []) or ())
    )
    targets = [
        dict(item)
        for item in raw_targets
        if isinstance(item, dict) and str(item.get("target") or "").strip()
    ]
    if len(targets) != 1:
        return None
    return targets[0]


def _framed_active_root_targets_for_conversation(
    dossier: Optional[ProofDossier],
    conv: Any,
    *,
    helper_blocks: Optional[Sequence[str]] = None,
) -> List[Dict[str, Any]]:
    """Return active-root targets owned by this root/preamble/helper frame."""

    if dossier is None or conv is None:
        return []
    if helper_blocks is None:
        try:
            helpers = list(dossier.verified_helper_blocks())
        except Exception:
            helpers = []
    else:
        helpers = list(helper_blocks)
    return active_root_targets_for_frame(
        dossier,
        root_statement=str(
            getattr(conv, "goal_statement", "")
            or getattr(dossier, "root_statement", "")
            or ""
        ),
        preamble=str(getattr(conv, "preamble", "") or ""),
        helper_blocks=helpers,
        require_helper_context_hash_match=True,
    )


def _active_root_tool_goal_statement(
    dossier: Optional[ProofDossier],
    *,
    conv: Any = None,
    helper_blocks: Optional[Sequence[str]] = None,
) -> str:
    """Return the scratch-check goal that matches the active-root prompt.

    For visible-answer ``P ↔ *_solution`` shells the prompt may ask the model
    to prove the mechanically reduced active target ``P`` directly. Scratch
    checks must use that same target; checking the unreduced shell tells the
    model a correct active-target proof failed for the wrong reason.  Local
    Lean context is closed into a theorem-shaped target by the shared
    active-root helper, and final acceptance still requires a Lean-checked
    lift back into the root theorem.
    """

    framed_targets = (
        _framed_active_root_targets_for_conversation(
            dossier,
            conv,
            helper_blocks=helper_blocks,
        )
        if conv is not None
        else None
    )
    return active_root_target_statement(
        framed_targets if framed_targets is not None else dossier,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )


def _is_active_root_lift_feedback_source(feedback_source: str) -> bool:
    return str(feedback_source or "") in {
        "active_root_lift_check",
        "active_root_lift_answer_safe_check",
    }


_ACTIVE_ROOT_LIFT_FEEDBACK_LINE_RE = re.compile(
    r"(?im)^.*(?:h_active|active-root|root-shell|shell stitch).*$"
)


def _suppress_active_root_lift_feedback_text(text: str) -> str:
    raw = str(text or "")
    if not raw:
        return ""
    kept = [
        line
        for line in raw.splitlines()
        if not _ACTIVE_ROOT_LIFT_FEEDBACK_LINE_RE.search(line)
    ]
    cleaned = "\n".join(kept).strip()
    return cleaned or (
        "The submitted proof checked the active target, but the internal "
        "root-shell finalization step failed. Continue proving the active "
        "target directly; do not mention or repair internal wrapper names."
    )


def _local_decl_names_for_search(
    dossier: Optional[ProofDossier],
    conv: Optional[Conversation] = None,
) -> List[str]:
    """Names local to this run that ``search_mathlib`` should not promise."""

    names: List[str] = []

    def add(value: Any) -> None:
        name = str(value or "").strip()
        if name and name not in names:
            names.append(name)

    add(getattr(dossier, "theorem_name", "") if dossier is not None else "")
    add(getattr(conv, "theorem_name", "") if conv is not None else "")
    if dossier is None:
        return names
    for mapping_name in ("verified_helpers", "proposed_helpers"):
        mapping = getattr(dossier, mapping_name, {}) or {}
        if not isinstance(mapping, dict):
            continue
        for name, helper in mapping.items():
            add(name)
            add(getattr(helper, "name", ""))
            add(helper_decl_name(getattr(helper, "source", "") or ""))
            if isinstance(helper, str):
                add(helper_decl_name(helper))
    for block in list(getattr(dossier, "helpers", []) or ()):
        add(helper_decl_name(block))
    return names


def _active_root_working_target_block(
    dossier: Optional[ProofDossier],
    *,
    active_root_targets: Optional[Sequence[Mapping[str, Any]]] = None,
    session_scope: str = "problem",
) -> str:
    item = _single_active_root_target(
        dossier,
        active_root_targets=active_root_targets,
    )
    if item is None:
        return ""
    target = " ".join(str(item.get("target") or "").split()).strip()
    if not target:
        return ""
    hypotheses = [
        _prompt_safe_inline_text(str(hyp or ""), limit=180)
        for hyp in list(item.get("hypotheses") or [])[:6]
        if str(hyp or "").strip()
    ]
    local_child_scope = str(session_scope or "problem").strip() in {
        "subgoal",
        "branch",
    }
    lines = [
        (
            "Active local child working target (authoritative):"
            if local_child_scope
            else "Active Lean working target (authoritative):"
        ),
        (
            "The verifier has mechanically reduced the original "
            "`↔ _solution` shell. Prove the remaining mathematical target "
            "directly; do not re-prove the shell and do not refute this "
            "active target."
        ),
    ]
    if hypotheses:
        if local_child_scope:
            lines.append(
                "Submit a complete Lean proof that introduces these local "
                "hypotheses and closes the local child target. The checked "
                "result may be returned only as a helper for its caller. Do "
                "not reason from the `_solution` value, and do not prove by "
                "vacuity."
            )
        else:
            lines.append(
                "Submit a complete Lean proof that introduces these local "
                "hypotheses and closes the target inside the root theorem; a "
                "standalone proof of only the target line is not a complete "
                "top-level proof. Do not reason from the `_solution` value, "
                "and do not prove by vacuity."
            )
        lines.append("Local hypotheses from Lean's active goal:")
        lines.extend(f"- {hyp}" for hyp in hypotheses if hyp)
        lines.append("Target:")
        lines.append(f"`{_prompt_safe_inline_text(target, limit=900)}`")
    else:
        lines.extend([
            "Lean working signature:",
            "```lean",
            f"example : {target} := by",
            "```",
        ])
    return "\n".join(lines)


def _rewrite_active_root_history_signature(
    content: str,
    *,
    theorem_name: str,
    target: str,
) -> str:
    """Normalize prior failed root attempts to the active-target frame."""

    name = str(theorem_name or "").strip()
    active_target = " ".join(str(target or "").split()).strip()
    text = str(content or "")
    if not name or not active_target or "_solution" not in text:
        return text
    pattern = re.compile(
        r"(?ms)^(?P<indent>[ \t]*)theorem[ \t]+"
        + re.escape(name)
        + r"\b.*?:=[ \t]*by"
    )

    def replace_header(match: re.Match[str]) -> str:
        indent = match.group("indent") or ""
        return f"{indent}example : {active_target} := by"

    return pattern.sub(replace_header, text)


_LEAN_SIGNATURE_BLOCK_RE = re.compile(
    r"Lean signature:\n(?P<sig>.*?)(?=\n\n(?:Lean preamble|Current goal state|Context lemmas|Context lemmas available|Turn budget|Important:|Direct-proof|Solve|Build|Return)|\Z)",
    re.DOTALL,
)


def _messages_with_active_root_working_target(
    messages: List[Dict[str, Any]],
    dossier: Optional[ProofDossier],
    *,
    active_root_targets: Optional[Sequence[Mapping[str, Any]]] = None,
    session_scope: str = "problem",
) -> List[Dict[str, Any]]:
    active_item = _single_active_root_target(
        dossier,
        active_root_targets=active_root_targets,
    )
    active_block = _active_root_working_target_block(
        dossier,
        active_root_targets=active_root_targets,
        session_scope=session_scope,
    )
    if not active_block:
        return list(messages or ())
    active_target = (
        " ".join(str((active_item or {}).get("target") or "").split()).strip()
        if active_item is not None
        else ""
    )
    active_hypotheses = list((active_item or {}).get("hypotheses") or ())
    rewrite_history_headers = not active_hypotheses
    theorem_name = str(getattr(dossier, "theorem_name", "") or "")
    rewritten: List[Dict[str, Any]] = []
    replaced_initial_signature = False
    for msg in list(messages or ()):
        item = dict(msg)
        content = str(item.get("content", "") or "")
        if item.get("role") == "assistant" and rewrite_history_headers:
            content = _rewrite_active_root_history_signature(
                content,
                theorem_name=theorem_name,
                target=active_target,
            )
            item["content"] = content
        if (
            not replaced_initial_signature
            and item.get("role") == "user"
            and "Problem (natural language):" in content
            and "Lean signature:" in content
        ):
            match = _LEAN_SIGNATURE_BLOCK_RE.search(content)
            if match is not None:
                original = str(match.group("sig") or "").strip()
                replacement = active_block
                if original:
                    if str(session_scope or "problem").strip() in {
                        "subgoal",
                        "branch",
                    }:
                        replacement += (
                            "\n\nOriginal local child shell "
                            "(kept for returning a checked helper; do not "
                            "re-prove in this reply):\n```lean\n"
                            f"{original}\n```"
                        )
                    else:
                        replacement += (
                            "\n\nOriginal root theorem shell "
                            "(kept for final Lean stitching; do not re-prove in "
                            "this reply):\n```lean\n"
                            f"{original}\n```"
                        )
                content = (
                    content[: match.start()]
                    + replacement
                    + content[match.end() :]
                )
                item["content"] = content
                replaced_initial_signature = True
        rewritten.append(item)
    if replaced_initial_signature:
        return rewritten
    return _messages_with_reference_context(
        rewritten,
        [{"role": "user", "content": active_block}],
    )


def _messages_with_search_context(
    messages: List[Dict[str, Any]],
    dossier: Optional[ProofDossier],
    proof_state: Optional[ProofSearchState],
    *,
    goal_statement: str = "",
    preamble: str = "",
    context_lemmas: Sequence[str] = (),
    session_scope: str = "problem",
) -> List[Dict[str, Any]]:
    """Attach durable dossier context plus run-local scheduler context."""

    normalized_session_scope = str(session_scope or "problem").strip() or "problem"
    local_child_scope = normalized_session_scope in {"subgoal", "branch"}

    def _with_active_root_anchor(
        current: List[Dict[str, Any]],
        active_context: str,
    ) -> List[Dict[str, Any]]:
        active = str(active_context or "").strip()
        if not active:
            return list(current)
        if (
            current
            and current[-1].get("role") == "user"
            and any(msg.get("role") == "assistant" for msg in current)
        ):
            anchored = [dict(msg) for msg in current]
            last = dict(anchored[-1])
            content = str(last.get("content", "") or "").rstrip()
            if active not in content:
                last["content"] = f"{content}\n\n{active}" if content else active
            anchored[-1] = last
            return anchored
        return _messages_with_reference_context(
            current,
            [{"role": "user", "content": active}],
        )

    frame_root_statement = str(
        (getattr(dossier, "root_statement", "") if dossier is not None else "")
        or goal_statement
    )
    frame_helpers = []
    if dossier is not None:
        try:
            frame_helpers = list(dossier.verified_helper_blocks())
        except Exception:
            frame_helpers = []
    active_targets = (
        active_root_targets_for_frame(
            dossier,
            root_statement=frame_root_statement,
            preamble=preamble,
            helper_blocks=frame_helpers,
            require_helper_context_hash_match=True,
        )
        if dossier is not None
        else []
    )
    active_statement = active_root_target_statement(
        active_targets,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    current_goal = " ".join(str(goal_statement or "").split()).strip()
    root_goal = " ".join(
        str(getattr(dossier, "root_statement", "") if dossier is not None else "").split()
    ).strip()
    use_active_root_context = bool(
        active_statement
        and (
            not current_goal
            or current_goal == active_statement
            or current_goal == root_goal
        )
    )
    out = (
        _messages_with_active_root_working_target(
            list(messages or ()),
            dossier,
            active_root_targets=active_targets,
            session_scope=normalized_session_scope,
        )
        if use_active_root_context
        else list(messages or ())
    )
    out = _messages_with_dossier_context(
        out,
        dossier,
        goal_statement=goal_statement,
        preamble=preamble,
        context_lemmas=context_lemmas,
    )
    if proof_state is None:
        return out
    active_context = (
        dossier.render_active_root_target_context(
            active_root_targets=active_targets,
        )
        if use_active_root_context
        and dossier is not None
        and hasattr(dossier, "render_active_root_target_context")
        else ""
    )
    if local_child_scope and active_context:
        active_context = active_context.replace(
            "Lean-derived active root target",
            "Lean-derived active local child target",
        )
    try:
        context = proof_state.render_context(
            active_root_targets=active_targets,
            graph=getattr(dossier, "proof_graph", None) if dossier is not None else None,
            session_scope=normalized_session_scope,
        )
    except TypeError:
        try:
            context = proof_state.render_context(
                active_root_targets=active_targets,
                graph=(
                    getattr(dossier, "proof_graph", None)
                    if dossier is not None
                    else None
                ),
            )
        except TypeError:
            context = proof_state.render_context()
    if not context:
        if active_context:
            return _with_active_root_anchor(out, active_context)
        return out
    out = _messages_with_reference_context(
        out,
        [{"role": "user", "content": context}],
    )
    if active_context:
        out = _with_active_root_anchor(out, active_context)
    return out


def _messages_with_reference_context(
    messages: List[Dict[str, Any]],
    context_messages: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Insert stable context without burying the latest repair instruction."""

    if not context_messages:
        return list(messages)
    if (
        messages
        and messages[-1].get("role") == "user"
        and any(msg.get("role") == "assistant" for msg in messages)
    ):
        return [*messages[:-1], *context_messages, messages[-1]]
    return [*messages, *context_messages]


def _helper_names_from_blocks(blocks: List[str]) -> List[str]:
    names: List[str] = []
    seen: set[str] = set()
    for block in blocks:
        name = helper_decl_name(block)
        if name and name not in seen:
            seen.add(name)
            names.append(name)
    return names


def _helper_blocks_for_names(blocks: List[str], names: List[str]) -> List[str]:
    wanted = {
        str(name or "").strip()
        for name in list(names or [])
        if str(name or "").strip()
    }
    if not wanted:
        return [str(block or "") for block in list(blocks or [])]
    return [
        str(block or "")
        for block in list(blocks or [])
        if (helper_decl_name(str(block or "")) or "") in wanted
    ]


# ---------------------------------------------------------------------------
# Mathlib API search — local file-based index over Mathlib lemmas, exposed
# to the LLM as an OpenAI tool. Reuses the v1 searcher; we just instantiate
# it and wire it into the conversational loop.
# ---------------------------------------------------------------------------

SEARCH_MATHLIB_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "search_mathlib",
        "description": (
            "DISCOVERY tool. Search Mathlib for Lean 4 lemmas, theorems, "
            "definitions, and abbrevs to surface candidate names you might "
            "use. Combine natural-language keywords with Lean symbol names — "
            "e.g. 'Nat.divisors card', 'tsum telescoping', "
            "'IntervalIntegrable', 'volume torus'. Returns name + type "
            "signature + source file for each match. Search results are "
            "ranked guesses; verify any specific name with the available "
            "Lean-checking tools before citing it."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "query": {
                    "type": "string",
                    "description": (
                        "Search terms. Mix Lean identifiers and natural-"
                        "language descriptions. Examples: 'Finset.card_image', "
                        "'monotone power 2-adic valuation', 'CommSemigroup "
                        "cancellation'."
                    ),
                },
                "max_results": {
                    "type": "integer",
                    "description": "Number of results (1-20, default 10).",
                },
            },
            "required": ["query"],
        },
    },
}


SEARCH_THEOREMS_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "search_theorems",
        "description": (
            "Search all configured mathematical libraries: Mathlib, explicit "
            "project/support roots, and verified published Mini theory. Results "
            "include scope/activation status. A result marked importable or "
            "requires_bundle_activation is discovery evidence, not yet a usable "
            "Lean declaration; use only already_imported results in proof text."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "query": {
                    "type": "string",
                    "description": "Natural-language, Lean-symbol, or type-shaped query.",
                },
                "max_results": {
                    "type": "integer",
                    "description": "Number of results (1-20, default 10).",
                },
            },
            "required": ["query"],
        },
    },
}


CHECK_LEAN_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "check_lean",
        "description": (
            "VERIFICATION tool — call this BEFORE writing a proof that cites "
            "a Mathlib lemma whose exact name and type you are not 100% sure "
            "of. Runs `#check <declaration>` in the same answer-safe Lean "
            "environment shown in the prompt and returns the declaration's "
            "type signature. Confirms (a) the name actually exists, and (b) "
            "the signature matches what your proof expects. Provide one or "
            "more declaration names or `#check declaration.name` lines — e.g. "
            "`tsum_subtype`, `Equiv.tsum_eq`, "
            "`Nat.choose_eq_factorial_div`. Cheap and deterministic; use it "
            "whenever search_mathlib surfaces a candidate or whenever you're "
            "about to write `apply foo`/`exact foo`/`simp [foo]` for a `foo` "
            "you haven't confirmed."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": (
                        "Scratch Lean text containing declaration names or "
                        "`#check declaration.name` lines. `import` lines are "
                        "ignored. Multiple checks are allowed and capped."
                    ),
                }
            },
            "required": ["code"],
        },
    },
}


def _init_api_searcher(lean_cfg: LeanConfig) -> Optional[MathlibApiSearcher]:
    """Build the Mathlib API index once (cached on disk after first build)."""
    retrieval_cfg = RetrievalConfig(
        # mathlib_root auto-resolves from lean_cfg.project_dir/.lake/packages/mathlib/Mathlib
        max_prompt_lemmas=15,
        prompt_budget_tokens=1500,
        # Disable embedding/dense paths — we only need the BM25 index.
        use_embeddings=False,
        dense_retrieval_enabled=False,
        include_project=False,
    )
    print("Building / loading Mathlib API index... (slow first time, cached after)", flush=True)
    started = time.monotonic()
    try:
        searcher = MathlibApiSearcher.load_or_build(retrieval_cfg, lean_cfg)
    except Exception as exc:
        print(f"  Mathlib index init failed: {type(exc).__name__}: {exc}", flush=True)
        return None
    elapsed = round(time.monotonic() - started, 2)
    if searcher is None:
        print(f"  Mathlib index unavailable (mathlib_root not found?). [{elapsed}s]", flush=True)
        return None
    n_entries = len(getattr(searcher, "_entries", []))
    print(f"  Mathlib index ready: {n_entries} entries [{elapsed}s]", flush=True)
    startup = getattr(searcher, "_startup_telemetry", {})
    if isinstance(startup, dict) and startup:
        reasons = startup.get("rebuild_reasons") or []
        reason = ",".join(str(item) for item in reasons) or str(
            startup.get("validation_reason") or "unknown"
        )
        print(
            "  Mathlib index startup: "
            f"cache_hit={bool(startup.get('cache_hit'))} "
            f"validation={float(startup.get('validation_s', 0.0)):.3f}s "
            f"load={float(startup.get('index_load_s', 0.0)):.3f}s "
            f"runtime_index={float(startup.get('runtime_index_build_s', 0.0)):.3f}s "
            f"rebuild={float(startup.get('rebuild_s', 0.0)):.3f}s "
            f"reason={reason}",
            flush=True,
        )
    return searcher


_LEAN_IMPORT_LINE_RE = re.compile(r"(?m)^\s*import\s+([^\s]+)\s*$")


def _lean_imports_from_text(*texts: str) -> Tuple[str, ...]:
    imports: List[str] = []
    for text in texts:
        for module_name in scan_lean_imports(str(text or "")):
            if module_name and module_name not in imports:
                imports.append(module_name)
    return tuple(imports)


def _external_theorem_support_roots(problem: Any) -> Tuple[Path, ...]:
    """Return support roots not already covered by the active Lake project."""

    project_value = getattr(problem, "project_path", None)
    project = (
        Path(project_value).expanduser().resolve()
        if project_value is not None
        else None
    )
    roots: List[Path] = []
    for raw_root in tuple(getattr(problem, "source_dirs", ()) or ()):
        root = Path(raw_root).expanduser().resolve()
        owner = None
        for candidate in (root, *root.parents):
            if any(
                (candidate / manifest).is_file()
                for manifest in ("lakefile.lean", "lakefile.toml")
            ):
                owner = candidate.resolve()
                break
        if (
            project is not None
            and owner in {None, project}
            and (root == project or root.is_relative_to(project))
        ):
            continue
        if root not in roots:
            roots.append(root)
    return tuple(roots)


def _init_mathematical_retrieval_service(
    *,
    lean_cfg: LeanConfig,
    args: argparse.Namespace,
    api_searcher: Optional[MathlibApiSearcher],
    theory_library: Optional[Any],
    active_imports: Sequence[str],
) -> Optional[Any]:
    """Compose Mini's federated retriever from explicit, provenance-safe roots."""

    if not bool(getattr(args, "mathematical_retrieval", True)):
        return api_searcher
    sources: List[Any] = []
    try:
        from .mini_theory.environment import dependency_environment_fingerprint

        environment_hash = dependency_environment_fingerprint(
            Path(lean_cfg.project_dir)
        )
    except Exception:
        environment_hash = text_hash(
            f"{Path(lean_cfg.project_dir).resolve()}\n"
            f"{','.join(str(item) for item in active_imports)}"
        )
    if api_searcher is not None:
        sources.append(
            StaticMathlibSource(
                api_searcher,
                environment_hash=environment_hash,
                active_imports=active_imports,
            )
        )

    configured_roots: List[Path] = []
    for raw_root in list(getattr(args, "mini_retrieval_project_roots", ()) or ()):
        candidate = Path(str(raw_root or "")).expanduser().resolve()
        if candidate not in configured_roots:
            configured_roots.append(candidate)
    if bool(getattr(args, "mini_retrieval_include_lean_project", False)):
        candidate = Path(lean_cfg.project_dir).expanduser().resolve()
        if candidate not in configured_roots:
            configured_roots.append(candidate)

    cache_root = Path(
        str(
            getattr(
                args,
                "mini_retrieval_cache_root",
                _PROJECT_ROOT / "runs" / "mini_retrieval",
            )
            or (_PROJECT_ROOT / "runs" / "mini_retrieval")
        )
    ).expanduser()
    semantic_enabled = bool(
        getattr(args, "mini_retrieval_semantic", True)
    )
    dense_enabled = bool(getattr(args, "mini_retrieval_dense", False))
    for root_index, project_root in enumerate(configured_roots):
        if not project_root.exists() or not project_root.is_dir():
            print(
                f"  Project retrieval root unavailable: {project_root}",
                flush=True,
            )
            continue
        root_key = hashlib.sha256(str(project_root).encode("utf-8")).hexdigest()[:16]
        source_cache = cache_root / root_key
        retrieval_cfg = RetrievalConfig(
            index_path=str(source_cache / "project_index.jsonl"),
            meta_path=str(source_cache / "project_index.meta.json"),
            dense_index_path=str(source_cache / "project_dense.npy"),
            dense_meta_path=str(source_cache / "project_dense.meta.json"),
            project_root=str(project_root),
            include_mathlib=False,
            include_project=True,
            update_on_start=True,
            # Dense retrieval also needs a query embedder.  Semantic scoring
            # may remain disabled independently at the policy layer, but the
            # explicitly requested dense channel must be initialized.
            use_embeddings=semantic_enabled or dense_enabled,
            dense_retrieval_enabled=dense_enabled,
            dense_build_on_start=dense_enabled,
            max_prompt_lemmas=max(
                30,
                int(getattr(args, "premise_retrieval_top_k", 64) or 64),
            ),
        )
        # Dense construction is intentionally allowed to run for a long time
        # across many batches, but one hung embedding-provider call must not
        # freeze Mini startup indefinitely.
        retrieval_cfg.dense_build_batch_timeout_s = 300.0
        try:
            retriever = LemmaRetriever(retrieval_cfg, lean_cfg)
        except Exception as exc:
            semantic_error = f"{type(exc).__name__}: {exc}"
            if not semantic_enabled and not dense_enabled:
                print(
                    "  Project retrieval init failed for "
                    f"{project_root}: {semantic_error}",
                    flush=True,
                )
                continue
            print(
                "  Project semantic retrieval unavailable for "
                f"{project_root}: {semantic_error}; retrying lexical/type-only.",
                flush=True,
            )
            retrieval_cfg.use_embeddings = False
            retrieval_cfg.dense_retrieval_enabled = False
            retrieval_cfg.dense_build_on_start = False
            try:
                retriever = LemmaRetriever(retrieval_cfg, lean_cfg)
            except Exception as fallback_exc:
                print(
                    "  Project retrieval init failed for "
                    f"{project_root}: {type(fallback_exc).__name__}: "
                    f"{fallback_exc}",
                    flush=True,
                )
                continue
            setattr(retriever, "_mini_semantic_init_error", semantic_error)
        setattr(retriever, "_mini_semantic_requested", semantic_enabled)
        setattr(retriever, "_mini_dense_requested", dense_enabled)
        setattr(
            retriever,
            "_mini_semantic_init_error",
            str(
                getattr(retriever, "_mini_semantic_init_error", "")
                or getattr(retriever, "_embedder_init_error", "")
                or ""
            ),
        )
        setattr(
            retriever,
            "_mini_semantic_available",
            bool(semantic_enabled and getattr(retriever, "_embedder", None) is not None),
        )
        sources.append(
            ProjectSupportSource(
                retriever,
                project_root=project_root,
                source_id=f"project:{root_index}",
                environment_hash=environment_hash,
                # A bare Lean module name is not enough to choose between two
                # configured project roots containing the same relative path.
                # Project declarations become active only after the exact
                # declaration/import probe in PremiseRetrievalAction succeeds.
                active_imports=(),
                module_roots=lake_module_roots(project_root),
            )
        )
    if theory_library is not None and getattr(theory_library, "mode", "off") != "off":
        sources.append(
            PublishedTheorySource(
                theory_library,
                environment_hash=environment_hash,
            )
        )
    service = MathematicalRetrievalService(
        sources,
        static_mathlib_searcher=api_searcher,
        enable_type_index=bool(
            getattr(args, "mini_retrieval_type_directed", True)
        ),
    )
    status = service.status()
    source_summary = ", ".join(
        _format_retrieval_source_status(item)
        for item in list(status.get("sources") or ())
    )
    print(
        "Mathematical retrieval ready: "
        f"snapshot={str(status.get('index_snapshot_id') or '')[:16]} "
        f"sources=[{source_summary}]",
        flush=True,
    )
    return service


def _format_retrieval_source_status(item: Mapping[str, Any]) -> str:
    """Render corpus status without conflating source ordinals with counts."""

    source_id = str(item.get("source_id") or "unknown")
    project_match = re.fullmatch(r"project:(\d+)", source_id)
    label = f"project[{project_match.group(1)}]" if project_match else source_id
    rendered = f"{label}={int(item.get('entry_count') or 0)}"
    state = str(item.get("index_state") or "")
    if state == "current_policy_empty":
        details = [state]
        policy_version = int(item.get("policy_version") or 0)
        environment_key = str(item.get("environment_key") or "").strip()
        if policy_version > 0:
            details.append(f"policy=v{policy_version}")
        if environment_key:
            details.append(f"env=E_{environment_key}")
        return f"{rendered}({';'.join(details)})"
    if state in {"configured_empty", "error"}:
        return f"{rendered}({state})"
    return rendered


def _ensure_default_mathematical_retrieval_service(
    *,
    searcher: Optional[Any],
    lean: Any,
    theory_library: Optional[Any],
    active_imports: Sequence[str],
    project_roots: Sequence[Path] = (),
    enabled: bool = True,
) -> Optional[Any]:
    """Compose the full default retriever for production programmatic calls.

    The CLI performs this composition before ``prove_problem``. Direct API
    callers historically received no retrieval at all when ``searcher=None``;
    a real ``LeanRunner`` carries enough configuration to build the same
    default-on Mathlib/project/semantic/dense/type/theory service safely.
    Test doubles and custom Lean protocols without a ``LeanConfig`` remain
    injection-only rather than triggering filesystem discovery.
    """

    if not enabled:
        if isinstance(searcher, MathematicalRetrievalService):
            return searcher.static_mathlib_searcher
        return searcher
    if isinstance(searcher, MathematicalRetrievalService):
        return searcher
    # A caller-supplied protocol-compatible searcher is an intentional
    # integration boundary.  Do not silently discard it merely because a real
    # LeanRunner is also present.  Concrete MathlibApiSearcher instances can
    # safely be promoted into the federated service; other implementations
    # remain caller-owned.
    if searcher is not None and not isinstance(searcher, MathlibApiSearcher):
        return searcher
    lean_cfg = getattr(lean, "cfg", None)
    if not isinstance(lean_cfg, LeanConfig):
        return searcher
    api_searcher = (
        searcher
        if isinstance(searcher, MathlibApiSearcher)
        else _init_api_searcher(lean_cfg)
    )
    defaults = argparse.Namespace(
        mathematical_retrieval=True,
        mini_retrieval_project_roots=[str(path) for path in project_roots],
        mini_retrieval_include_lean_project=True,
        mini_retrieval_cache_root=str(_PROJECT_ROOT / "runs" / "mini_retrieval"),
        mini_retrieval_semantic=True,
        mini_retrieval_dense=True,
        mini_retrieval_type_directed=True,
        premise_retrieval_top_k=max(PREMISE_DEFAULT_TOP_K, 64),
    )
    return _init_mathematical_retrieval_service(
        lean_cfg=lean_cfg,
        args=defaults,
        api_searcher=api_searcher,
        theory_library=theory_library,
        active_imports=active_imports,
    )


def _searcher_supports_static_mathlib(searcher: Any) -> bool:
    return bool(
        searcher is not None
        and (
            not isinstance(searcher, MathematicalRetrievalService)
            or searcher.static_mathlib_searcher is not None
        )
    )




def _run_search_tool(
    searcher: MathlibApiSearcher,
    args: Dict[str, Any],
    *,
    known_decl_names: Sequence[str] = (),
    local_decl_names: Sequence[str] = (),
    metric_sink: Optional[Dict[str, int]] = None,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> str:
    """Execute one search_mathlib call. Returns a string for the tool result."""
    query, removed_placeholders = normalize_theorem_search_query(
        args.get("query", "")
    )
    # Execution telemetry below reads this same parsed mapping. Show the
    # effective query while the immutable raw argument record retains exactly
    # what the model emitted.
    args["query"] = query
    try:
        max_n = int(args.get("max_results", 10))
    except Exception:
        max_n = 10
    max_n = max(1, min(20, max_n))
    if not query:
        if removed_placeholders:
            if metric_sink is not None:
                key = "mini_search_placeholder_only_queries_rejected"
                metric_sink[key] = int(metric_sink.get(key, 0) or 0) + 1
            return (
                "Error: query contained only synthetic <string> redaction "
                "placeholders; search was not dispatched. Supply concrete "
                "Mathlib names or mathematical terms."
            )
        return "Error: empty query."
    if removed_placeholders and metric_sink is not None:
        key = "mini_search_placeholders_removed"
        metric_sink[key] = int(metric_sink.get(key, 0) or 0) + int(
            removed_placeholders
        )
    local_decls = {
        str(name or "").strip().lstrip("@")
        for name in list(local_decl_names or ())
        if str(name or "").strip()
    }
    local_query = query.lstrip("@")
    if local_query in local_decls:
        if metric_sink is not None:
            key = "mini_search_local_decl_queries_suppressed"
            metric_sink[key] = int(metric_sink.get(key, 0) or 0) + 1
        return (
            "No matching Mathlib declarations found. "
            "That exact name is local to the current theorem/run; use "
            "`check_lean` or `try_lean` for local helpers and current-theorem "
            "declarations."
        )
    known = {
        str(name or "").strip()
        for name in list(known_decl_names or ())
        if str(name or "").strip()
    }
    search_max_n = max_n
    if known:
        # Ask the retriever for enough extra candidates to backfill entries
        # already shown by eager premise retrieval.  The LLM should see new
        # evidence, not a smaller result set, just because two retrieval paths
        # touched the same lemma.
        search_max_n = min(40, max_n + len(known))
    search_fn = getattr(searcher, "search_mathlib", None)
    if not callable(search_fn):
        search_fn = searcher.search
    search_kwargs: Dict[str, Any] = {"max_results": search_max_n}
    try:
        search_signature = inspect.signature(search_fn)
        search_parameters = search_signature.parameters
        if "deadline_exhausted" in search_parameters or any(
            parameter.kind is inspect.Parameter.VAR_KEYWORD
            for parameter in search_parameters.values()
        ):
            search_kwargs["deadline_exhausted"] = deadline_exhausted
    except (TypeError, ValueError):
        pass
    try:
        hits = search_fn(query, **search_kwargs)
    except Exception as exc:
        safe_exc_type = _prompt_safe_inline_text(type(exc).__name__, limit=120)
        return (
            f"Search failed: {safe_exc_type}: "
            f"{_prompt_safe_inline_text(exc, limit=500)}"
        )

    def _hit_name(entry: Any) -> str:
        if isinstance(entry, dict):
            return str(entry.get("name", "") or "").strip()
        return str(getattr(entry, "name", "") or "").strip()

    suppressed = 0
    if known:
        returned_hits = list(hits or [])
        fresh_hits = [
            hit
            for hit in returned_hits
            if _hit_name(hit) not in known
        ]
        suppressed = len(returned_hits) - len(fresh_hits)
        if suppressed and metric_sink is not None:
            key = "mini_search_pre_retrieved_duplicates_suppressed"
            metric_sink[key] = int(metric_sink.get(key, 0) or 0) + suppressed
        hits = fresh_hits[:max_n]
        if suppressed and not hits:
            shown = ", ".join(
                _prompt_safe_helper_name(name) for name in sorted(known)[:6]
            )
            extra = " ..." if len(known) > 6 else ""
            return (
                "No new matches. All returned declarations were already shown "
                f"in the pre-retrieved premise block ({shown}{extra})."
            )
    rendered = _format_search_results(hits, max_n)
    if suppressed:
        rendered = (
            rendered.rstrip()
            + f"\n\n({suppressed} already pre-retrieved declaration(s) omitted.)"
        )
    if removed_placeholders:
        rendered = (
            f"Ignored {removed_placeholders} synthetic <string> "
            f"placeholder(s); effective query: {query}\n{rendered}"
        )
    return rendered


def _run_search_theorems_tool(
    searcher: Any,
    args: Dict[str, Any],
    *,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    accepted_result_out: Optional[Dict[str, Any]] = None,
    goal_state: str = "",
) -> str:
    """Execute one provenance-aware federated theorem search."""

    query, removed_placeholders = normalize_theorem_search_query(
        args.get("query", "")
    )
    args["query"] = query
    if not query:
        if removed_placeholders:
            return (
                "Error: query contained only synthetic <string> redaction "
                "placeholders; federated search was not dispatched. Supply "
                "concrete theorem names or mathematical terms."
            )
        return "Error: empty query."
    fork = getattr(searcher, "fork_session_context", None)
    if callable(fork):
        searcher = fork()
    try:
        max_n = max(1, min(20, int(args.get("max_results", 10) or 10)))
    except Exception:
        max_n = 10
    try:
        hits = list(
            searcher.search_with_scores(
                query,
                goal_state=str(goal_state or "").strip(),
                max_results=max_n,
                deadline_exhausted=deadline_exhausted,
            )
            or []
        )
    except Exception as exc:
        return (
            f"Search failed: {_prompt_safe_inline_text(type(exc).__name__, limit=120)}: "
            f"{_prompt_safe_inline_text(exc, limit=500)}"
        )
    if deadline_exhausted is not None:
        try:
            expired = bool(deadline_exhausted())
        except Exception:
            expired = True
        if expired:
            return "Search deadline exhausted; late results were discarded."
    if accepted_result_out is not None:
        accepted_result_out["result"] = getattr(searcher, "last_result", None)
    if not hits:
        return "No matching declarations found across configured sources."
    lines = [f"{len(hits)} federated match(es):"]
    for index, hit in enumerate(hits[:max_n], 1):
        entry = getattr(hit, "entry", hit)
        candidate = getattr(hit, "candidate", None) or getattr(
            entry, "retrieval_candidate", None
        )
        name = _prompt_safe_helper_name(
            str(getattr(entry, "name", "") or "?")
        )
        type_text = _prompt_safe_inline_text(
            str(getattr(entry, "type", "") or ""),
            limit=360,
        )
        lines.append(f"{index}. {name}")
        if type_text:
            lines.append(f"   : {type_text}")
        if candidate is not None and getattr(candidate, "origins", None):
            origin = candidate.origins[0]
            lines.append(
                "   source="
                f"{_prompt_safe_inline_text(origin.source_kind, limit=80)} "
                "availability="
                f"{_prompt_safe_inline_text(origin.availability, limit=80)}"
            )
            if origin.module_name:
                lines.append(
                    "   module="
                    f"{_prompt_safe_inline_text(origin.module_name, limit=180)}"
                )
            if origin.availability != "already_imported":
                lines.append(
                    "   NOT YET USABLE in proof text; an explicit import, theory "
                    "activation, or helper recheck is required."
                )
    rendered = "\n".join(lines)
    if removed_placeholders:
        rendered = (
            f"Ignored {removed_placeholders} synthetic <string> "
            f"placeholder(s); effective query: {query}\n{rendered}"
        )
    return rendered


_CHECK_TERM_RE = re.compile(r"^@?[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
_LEAN_LOCAL_IDENT_RE = re.compile(r"^(?:[^\W\d]|_)[\w']*$", flags=re.UNICODE)


def _normalize_check_query(term: str) -> Optional[str]:
    """Prefilter one expression for the model-facing ``#check`` tool.

    Lean's ``#check`` accepts applications and named arguments as well as bare
    declaration names.  Preserve the complete expression so a query such as
    ``Finset.strongInductionOn (motive := ...)`` actually checks that
    specialization.  Newlines, comments, and ``#`` commands are rejected here
    for prompt/tool hygiene.  This text-only filter is not the command boundary:
    ``LeanRunner.check_term_type`` must parse every non-bare candidate with
    Lean's native ``term`` parser before embedding it in generated source.
    """
    s = str(term or "").strip()
    if not s:
        return None
    if s.startswith("#check"):
        s = s[len("#check") :].strip()
    if len(s) > 2000:
        return None
    if any(token in s for token in ("\n", "\r", "#", "--", "/-", "-/")):
        return None
    if re.search(
        r"(?<![\w'])(?:by|sorry|admit)(?![\w'])",
        s,
    ):
        return None
    if not lean_expression_delimiters_balanced(s):
        return None
    if _PROMPT_REDACTION_TOKEN_RE.search(s):
        return None
    # Reject lone Lean keywords / common tactic names that have identifier
    # shape but are NOT declarations. Qualified names (e.g. ``Real.sqrt``)
    # always pass since the qualifier prevents the fullmatch from being a
    # bare keyword. Case-sensitive — ``Theorem`` (a hypothetical user decl)
    # is allowed; only the lowercase keyword ``theorem`` is rejected.
    bare_name = s[1:].strip() if s.startswith("@") else s
    if _CHECK_TERM_RE.fullmatch(bare_name) and bare_name in _LEAN_BUILTIN_WORDS:
        return None
    return bare_name if _CHECK_TERM_RE.fullmatch(bare_name) else f"({s})"


def _extract_check_queries(args: Dict[str, Any], *, limit: int = 8) -> List[str]:
    """Extract complete ``#check`` expressions from a tool call."""
    cap = max(0, int(limit or 0))
    if cap <= 0:
        return []
    out: List[str] = []
    seen: set[str] = set()

    def add_query(value: Any) -> bool:
        normalized = _normalize_check_query(str(value or ""))
        if normalized and normalized not in seen:
            seen.add(normalized)
            out.append(normalized)
        return len(out) >= cap

    raw_terms = args.get("terms")
    if isinstance(raw_terms, list):
        for item in raw_terms:
            if add_query(item):
                return out

    for key in ("term", "name", "query"):
        if key in args:
            if add_query(args.get(key)):
                return out

    raw_code = str(args.get("code", "") or "")
    if raw_code:
        # Locate commands in a mask that blanks comments *and* strings, while
        # slicing query text from the comment-only mask so legitimate string
        # literals remain intact.  Both scanners preserve source positions.
        # This prevents a model's explanatory ``-- #check ...`` (including
        # one after an import on the same line) from becoming a real lookup.
        marker_code = _strip_lean_comments_and_strings(raw_code)
        query_code = _strip_lean_comments(raw_code)
        marker_lines = marker_code.split("\n")
        query_lines = query_code.split("\n")
        for line_index, marker_line in enumerate(marker_lines):
            query_line = (
                query_lines[line_index]
                if line_index < len(query_lines)
                else ""
            )
            stripped = marker_line.strip()
            if not stripped:
                continue
            if "#check" in stripped:
                matches = list(re.finditer(r"#check\b", marker_line))
                for match_index, match in enumerate(matches):
                    end = (
                        matches[match_index + 1].start()
                        if match_index + 1 < len(matches)
                        else len(marker_line)
                    )
                    if add_query(query_line[match.end() : end].strip()):
                        return out
            else:
                query_text = query_line.strip()
                if _CHECK_TERM_RE.fullmatch(query_text.lstrip("@")) and add_query(
                    query_text
                ):
                    return out
    return out


def _proof_state_node_for_tool_statement(
    proof_state: Optional[ProofSearchState],
    statement: str,
    *,
    active_root_targets: Sequence[Dict[str, Any]] = (),
) -> Any:
    """Return the unique live proof-state node matching a tool statement."""

    if proof_state is None:
        return None
    target = str(statement or "").strip()
    if not target:
        return None
    try:
        desired = proof_state._normalize_goal_text(target)  # noqa: SLF001
    except Exception:
        desired = target
    active_statement = active_root_target_statement(
        list(active_root_targets or ()),
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    if active_statement:
        try:
            active_desired = proof_state._normalize_goal_text(active_statement)  # noqa: SLF001
        except Exception:
            active_desired = " ".join(str(active_statement or "").split()).strip()
        if desired == active_desired:
            root = getattr(proof_state, "nodes", {}).get(
                getattr(proof_state, "root_node_id", "")
            )
            if root is not None and getattr(root, "status", "") not in {
                "proved",
                "obsolete",
            }:
                return root
    try:
        signature = proof_state._goal_signature(  # noqa: SLF001 - scheduler identity API
            target,
            [],
            source_failure="apply_decl_to_goal_tool",
        )
        matches = [
            node
            for node in getattr(proof_state, "nodes", {}).values()
            if node.status not in {"proved", "obsolete"}
            and getattr(node.goal, "normalized_statement_hash", "")
            == signature.normalized_statement_hash
        ]
        if len(matches) == 1:
            return matches[0]
        if len(matches) > 1:
            return None
    except Exception:
        pass

    matches = []
    for node in getattr(proof_state, "nodes", {}).values():
        if node.status in {"proved", "obsolete"}:
            continue
        try:
            node_target = proof_state._normalize_goal_text(node.target)  # noqa: SLF001
        except Exception:
            node_target = str(getattr(node, "target", "") or "").strip()
        if node_target == desired:
            matches.append(node)
    if len(matches) == 1:
        return matches[0]

    return None


async def _finalize_apply_decl_root_closure(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: ProofDossier,
    proof_state: ProofSearchState,
    node: Any,
    proof_code: str,
    decl_name: str,
    signature: str,
    context_lemmas: Sequence[str],
    active_root_targets: Sequence[Dict[str, Any]],
    turn_index: int,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
    verifier_timeout_s: float = 300.0,
) -> Dict[str, Any]:
    """Verify and finalize a root proof produced by apply_decl_to_goal."""

    from ensemble_prover.mini_session.turn.lean_check import (
        AnswerSafeRecheckInfrastructureError,
        LeanVerificationDeadline,
        verify_with_lean,
    )
    from ensemble_prover.root_finalization import (
        finalize_root_solution,
        root_verification_certificate,
    )

    root_statement = str(
        getattr(dossier, "root_statement", "")
        or getattr(conv, "goal_statement", "")
        or getattr(node, "target", "")
        or ""
    )
    verify_conv = conv
    if not str(getattr(verify_conv, "goal_statement", "") or "").strip():
        verify_conv = SimpleNamespace(
            role=getattr(conv, "role", "prove"),
            # The fallback is entered specifically because the supplied
            # context has no goal.  Do not copy that empty value back into the
            # verification context; the dossier owns the canonical root here.
            goal_statement=root_statement,
            preamble=getattr(conv, "preamble", ""),
            lean_preamble=getattr(conv, "lean_preamble", ""),
            opaque_mode=getattr(conv, "opaque_mode", True),
            allow_official_answer_visibility=getattr(
                conv,
                "allow_official_answer_visibility",
                False,
            ),
            suppress_solution_placeholders=bool(
                getattr(
                    conv,
                    "suppress_solution_placeholders",
                    getattr(dossier, "suppress_solution_placeholders", True),
                )
            ),
        )
    def deadline_elapsed() -> bool:
        try:
            return bool(
                (deadline_exhausted and deadline_exhausted())
                or (
                    float(deadline_monotonic or 0.0) > 0.0
                    and time.monotonic() >= float(deadline_monotonic)
                )
            )
        except Exception:
            return True

    def deadline_result() -> Dict[str, Any]:
        return {
            "node_id": str(getattr(node, "node_id", "") or ""),
            "status": "llm_turn_elapsed_budget_exhausted",
        }

    try:
        verdict = await verify_with_lean(
            conv=verify_conv,
            lean=lean,
            proof=proof_code,
            helpers=[],
            context_helpers=list(context_lemmas or ()),
            check_lemmas=list(context_lemmas or ()),
            active_root_targets=list(active_root_targets or ()),
            deadline_monotonic=max(0.0, float(deadline_monotonic or 0.0)),
            verifier_timeout_override_s=max(
                300.0,
                float(verifier_timeout_s or 0.0),
            ),
            deadline_exhausted=deadline_elapsed,
        )
    except LeanVerificationDeadline:
        return {
            "node_id": str(getattr(node, "node_id", "") or ""),
            "status": "llm_turn_elapsed_budget_exhausted",
            "decl_name": decl_name,
        }
    except AnswerSafeRecheckInfrastructureError as exc:
        if isinstance(exc.__cause__, LeanVerificationDeadline):
            return {
                "node_id": str(getattr(node, "node_id", "") or ""),
                "status": "llm_turn_elapsed_budget_exhausted",
                "decl_name": decl_name,
            }
        raise
    if deadline_elapsed():
        return {
            "node_id": node.node_id,
            "status": "llm_turn_elapsed_budget_exhausted",
            "decl_name": decl_name,
        }
    if not bool(verdict.accepted):
        proof_state.record_decl_application_result(
            node_id=node.node_id,
            ok=False,
            attempt_count=1,
            exit_reason=(
                f"root_verification_rejected:{verdict.feedback_source}"
                if str(verdict.feedback_source or "").strip()
                else "root_verification_rejected"
            ),
            decl_application_signature=signature,
        )
        return {
            "node_id": node.node_id,
            "status": "root_verification_rejected",
            "decl_name": decl_name,
            "feedback_source": verdict.feedback_source,
        }

    accepted_proof = str(verdict.accepted_proof or proof_code)
    helper_names = tuple(
        name
        for block in list(context_lemmas or ())
        for name in [helper_decl_name(block)]
        if name
    )
    result_for_output = (
        verdict.safe_result
        if verdict.safe_result is not None and bool(getattr(verdict.safe_result, "ok", False))
        else verdict.primary_result
    )
    if deadline_elapsed():
        return {
            "node_id": node.node_id,
            "status": "llm_turn_elapsed_budget_exhausted",
            "decl_name": decl_name,
        }
    finalization = finalize_root_solution(
        dossier=dossier,
        proof_state=proof_state,
        proof=accepted_proof,
        replay_helpers=list(context_lemmas or ()),
        helper_names=helper_names,
        phase="llm_tool_decl_application",
        turn_index=turn_index,
        source_action_id=f"apply_decl_to_goal:{decl_name}",
        target_statement=root_statement,
        verification_certificate=root_verification_certificate(
            accepted=True,
            proof=accepted_proof,
            phase="llm_tool_decl_application",
            turn_index=turn_index,
            target_statement=root_statement,
            replay_helpers=list(context_lemmas or ()),
            helper_names=helper_names,
            output=str(getattr(result_for_output, "output", "") or ""),
            source="legacy_apply_decl_to_goal_tool",
        ),
        require_verification_certificate=True,
        metadata={
            "decl_name": str(decl_name or ""),
            "decl_application_signature": signature,
            "lean_primary_source": str(verdict.primary_source or ""),
            "active_root_statement": str(verdict.active_root_statement or ""),
        },
        deadline_exhausted=(
            deadline_elapsed
            if deadline_exhausted is not None
            or float(deadline_monotonic or 0.0) > 0.0
            else None
        ),
    )
    if deadline_elapsed():
        return {
            "node_id": node.node_id,
            "status": "llm_turn_elapsed_budget_exhausted",
            "decl_name": decl_name,
        }
    if not bool(finalization.accepted):
        proof_state.record_decl_application_result(
            node_id=node.node_id,
            ok=False,
            attempt_count=1,
            exit_reason=f"root_finalization_blocked:{finalization.verdict}",
            decl_application_signature=signature,
        )
        return {
            "node_id": node.node_id,
            "status": "root_finalization_blocked",
            "decl_name": decl_name,
            "root_finalization_verdict": finalization.verdict,
            "route_contract_verdict": str(
                finalization.route_contract_status.get("verdict") or ""
            ),
        }

    try:
        proof_state.record_decl_application_result(
            node_id=node.node_id,
            ok=True,
            attempt_count=1,
            exit_reason=f"closed_by_tool:{decl_name}",
            decl_application_signature=signature,
        )
        proof_state.mark_root_solved()
        proof_state.sync_to_graph(
            dossier,
            phase="llm_tool_decl_application",
            turn_index=turn_index,
            refresh_target_node_ids=[node.node_id],
        )
    except Exception:
        pass
    return {
        "node_id": node.node_id,
        "status": "root_finalized",
        "decl_name": decl_name,
        "root_finalization_verdict": finalization.verdict,
        "proof_source": verdict.primary_source,
    }


async def _sync_apply_decl_to_proof_state(
    *,
    lean: LeanRunner,
    conv: Any,
    dossier: Optional[ProofDossier],
    proof_state: Optional[ProofSearchState],
    proof_cache: Optional[MiniVerifiedLemmaCache],
    statement: str,
    decl_name: str,
    applicable: bool,
    proof_stub: str,
    remaining_goals: Sequence[Any],
    error_kind: str,
    turn_index: int,
    context_lemmas: Sequence[str] = (),
    residual_preamble: str = "",
    active_root_targets: Sequence[Dict[str, Any]] = (),
    timeout_s: float = 300.0,
    max_residual_goals: int = 4,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
) -> Dict[str, Any]:
    """Mirror LLM apply_decl_to_goal probes into ProofSearchState when safe."""

    if dossier is None or proof_state is None:
        return {}

    def deadline_elapsed() -> bool:
        try:
            return bool(
                (deadline_exhausted and deadline_exhausted())
                or (
                    float(deadline_monotonic or 0.0) > 0.0
                    and time.monotonic() >= float(deadline_monotonic)
                )
            )
        except Exception:
            return True

    def deadline_result() -> Dict[str, Any]:
        return {
            "node_id": str(getattr(node, "node_id", "") or ""),
            "status": "llm_turn_elapsed_budget_exhausted",
        }

    combined_deadline_exhausted = (
        deadline_elapsed
        if deadline_exhausted is not None
        or float(deadline_monotonic or 0.0) > 0.0
        else None
    )

    if deadline_elapsed():
        return {"status": "llm_turn_elapsed_budget_exhausted"}
    node = _proof_state_node_for_tool_statement(
        proof_state,
        statement,
        active_root_targets=active_root_targets,
    )
    if node is None:
        return {}
    signature = text_hash(
        "\n".join(
            [
                str(decl_name or ""),
                f"residual_goal_limit={max(0, int(max_residual_goals or 0))}",
            ]
        )
    )
    authoritative_proof_stub = (
        _proof_from_decl_application_stub(str(proof_stub or ""))
        if applicable and proof_stub
        else ""
    )
    if applicable and proof_stub:
        residual_goal_limit = max(0, int(max_residual_goals or 0))
        residual_source = f"llm_tool_decl_application:{decl_name}"
        authoritative_residual_preamble = str(
            residual_preamble
            or getattr(conv, "lean_preamble", "")
            or getattr(conv, "preamble", "")
            or ""
        )
        if (
            remaining_goals
            and getattr(node, "decl_application_signature", "") == signature
            and getattr(node, "child_node_ids", [])
        ):
            return {
                "node_id": node.node_id,
                "status": "already_spawned_remaining_goals",
                "spawned_child_nodes": list(getattr(node, "child_node_ids", [])),
            }
        residual_deadline_monotonic = max(
            0.0,
            float(deadline_monotonic or 0.0),
        )
        residual_operation_timeout_s = _typed_residual_operation_timeout(
            lean,
            timeout_s,
        )
        if (
            residual_deadline_monotonic > 0.0
            and residual_deadline_monotonic - time.monotonic()
            < residual_operation_timeout_s + 1.0
        ):
            # Preserve the exact paid stub as a verifier-only pending frame
            # without launching work that the enclosing turn cannot fund.
            # The one-second headroom is for atomic workspace commit, not a
            # shorter Lean operation allowance.
            residual_deadline_monotonic = time.monotonic()
        spawned, residual_goal_count, receipt_status = (
            await _extract_and_spawn_typed_residual_goals(
                lean=lean,
                proof_state=proof_state,
                parent_node=node,
                parent_proof_stub=authoritative_proof_stub,
                source=residual_source,
                preamble=authoritative_residual_preamble,
                lemmas=list(context_lemmas or ()),
                timeout_s=timeout_s,
                max_goals=residual_goal_limit,
                deadline_monotonic=residual_deadline_monotonic,
                deadline_exhausted=combined_deadline_exhausted,
                origin_metadata={
                    "kind": "llm_tool_decl_application",
                    "decl_name": decl_name,
                    "turn_index": turn_index,
                },
            )
        )
        node = proof_state.nodes.get(node.node_id, node)
        if receipt_status.endswith("_deferred"):
            return {
                "node_id": node.node_id,
                "status": "residual_attestation_deferred",
                "reason": receipt_status,
            }
        if receipt_status == "residual_attestation_goal_cap_exceeded":
            if deadline_elapsed():
                return deadline_result()
            reason = "decl_application_residual_goal_cap_exceeded"
            proof_state.record_graph_frontier_error(
                {
                    "source": f"llm_tool_decl_application:{decl_name}",
                    "parent_node_id": node.node_id,
                    "error_type": reason,
                    "residual_goal_count": residual_goal_count,
                    "residual_goal_limit": residual_goal_limit,
                }
            )
            proof_state.record_transition(
                node_id=node.node_id,
                source=f"llm_tool_decl_application:{decl_name}",
                error_type=reason,
                action=node.action,
                blocker=(
                    f"{decl_name} left {residual_goal_count} residual goal(s), "
                    f"exceeding configured limit {residual_goal_limit}"
                ),
                phase="llm_tool_decl_application",
                turn_index=turn_index,
                payload={
                    "decl_name": decl_name,
                    "residual_goal_count": residual_goal_count,
                    "residual_goal_limit": residual_goal_limit,
                },
            )
            proof_state.record_decl_application_result(
                node_id=node.node_id,
                ok=False,
                attempt_count=1,
                exit_reason=reason,
                decl_application_signature=signature,
            )
            return {
                "node_id": node.node_id,
                "status": "residual_goal_cap_exceeded",
                "residual_goal_count": residual_goal_count,
                "residual_goal_limit": residual_goal_limit,
            }
        if receipt_status == "residual_attestation_closed_goal":
            # Typed replay, not diagnostic text, decides whether the stub left
            # obligations. Continue into the verified closure path below.
            remaining_goals = []
        elif receipt_status != "residual_attestation_admitted" or not spawned:
            return {
                "node_id": node.node_id,
                "status": "residual_attestation_rejected",
                "reason": receipt_status,
            }
        if spawned:
            node.decl_application_signature = signature
            node.decl_application_attempts += 1
            node.close_attempts += 1
            node.action = "assemble_from_children"
            node.blocker = f"{decl_name} left {residual_goal_count} subgoal(s)"
            node.priority = proof_state._priority(node)  # noqa: SLF001
            try:
                proof_state.sync_to_graph(
                    dossier,
                    phase="llm_tool_decl_application_partial",
                    turn_index=turn_index,
                    refresh_target_node_ids=[node.node_id, *list(spawned)],
                )
            except Exception:
                pass
            return {
                "node_id": node.node_id,
                "status": "spawned_remaining_goals",
                "spawned_child_nodes": list(spawned),
            }
    if applicable and proof_stub and not remaining_goals:
        proof_code = authoritative_proof_stub
        if not proof_code:
            return {"node_id": node.node_id, "status": "missing_proof_code"}
        closure_operation_timeout_s = _typed_residual_operation_timeout(
            lean,
            timeout_s,
        )
        if str(getattr(node, "node_id", "") or "") == str(
            getattr(proof_state, "root_node_id", "") or ""
        ):
            # Root verification can require an active-target check, its root
            # lift, and an answer-safe check. Hand the zero-goal receipt to the
            # durable verifier-only acceptance lane before attempting any of
            # them; successful finalization clears it, while infrastructure
            # leaves it for scheduler replay without another extraction or
            # provider/declaration probe.
            closure_staged = stage_closed_typed_residual_acceptance(
                conv=conv,
                dossier=dossier,
                lean=lean,
                proof_state=proof_state,
                parent_node=node,
                parent_proof_stub=authoritative_proof_stub,
                source=f"llm_tool_decl_application:{decl_name}",
                max_goals=max(0, int(max_residual_goals or 0)),
                origin_metadata={
                    "kind": "llm_tool_decl_application",
                    "decl_name": decl_name,
                    "turn_index": turn_index,
                },
                action_metadata={"decl_name": decl_name},
            )
            if not closure_staged:
                return {
                    "node_id": node.node_id,
                    "status": "root_closure_pending_stage_deferred",
                }
            root_verification_operation_count = (
                1
                + int(bool(active_root_targets))
                + int(_needs_answer_safe_feedback_check(conv))
            )
            root_verification_quantum_s = (
                float(root_verification_operation_count)
                * closure_operation_timeout_s
                + 1.0
            )
            if (
                float(deadline_monotonic or 0.0) > 0.0
                and float(deadline_monotonic) - time.monotonic()
                < root_verification_quantum_s
            ):
                return {
                    "node_id": node.node_id,
                    "status": "root_closure_verification_deferred",
                }
            root_result = await _finalize_apply_decl_root_closure(
                lean=lean,
                conv=conv,
                dossier=dossier,
                proof_state=proof_state,
                node=node,
                proof_code=proof_code,
                decl_name=decl_name,
                signature=signature,
                context_lemmas=context_lemmas,
                active_root_targets=active_root_targets,
                turn_index=turn_index,
                deadline_exhausted=combined_deadline_exhausted,
                deadline_monotonic=deadline_monotonic,
                verifier_timeout_s=closure_operation_timeout_s,
            )
            if str(root_result.get("status") or "") not in {
                "llm_turn_elapsed_budget_exhausted",
                "root_closure_verification_deferred",
            }:
                proof_state.clear_pending_residual_goal_extraction(node)
            return root_result
        helper_name = proof_state.helper_name_for_node(node, dossier)
        helper_block = _proof_state_helper_block(helper_name, node.target, proof_code)
        helper_staged = stage_pending_helper_acceptance(
            conv=conv,
            dossier=dossier,
            node=node,
            helper_block=helper_block,
            source=f"decl_application:{decl_name}",
            continuation={
                "kind": "decl_application",
                "decl_name": decl_name,
                "decl_application_signature": signature,
            },
        )
        if not helper_staged:
            return {
                "node_id": node.node_id,
                "status": "helper_acceptance_pending_owner_busy",
            }
        helper_acceptance_quantum_s = (
            float(1 + int(_needs_answer_safe_feedback_check(conv)))
            * closure_operation_timeout_s
            + 1.0
        )
        if (
            float(deadline_monotonic or 0.0) > 0.0
            and float(deadline_monotonic) - time.monotonic()
            < helper_acceptance_quantum_s
        ):
            return {
                "node_id": node.node_id,
                "status": "helper_acceptance_deferred",
            }
        accept_status: Dict[str, Any] = {}
        accepted = await _accept_proof_state_helper(
            lean=lean,
            conv=conv,
            dossier=dossier,
            helper_block=helper_block,
            phase="llm_tool_decl_application",
            turn_index=turn_index,
            timeout_s=closure_operation_timeout_s,
            proof_cache=proof_cache,
            proof_state=proof_state,
            status_out=accept_status,
            target_statement=node.target,
            deadline_exhausted=combined_deadline_exhausted,
            deadline_monotonic=deadline_monotonic,
        )
        if deadline_elapsed():
            return {
                "node_id": node.node_id,
                "status": "llm_turn_elapsed_budget_exhausted",
            }
        if accepted:
            node.pending_helper_acceptance = {}
            if deadline_elapsed():
                return deadline_result()
            proof_state.record_decl_application_result(
                node_id=node.node_id,
                ok=True,
                attempt_count=1,
                exit_reason=f"closed_by_tool:{decl_name}",
                helper_name=helper_name,
                decl_application_signature=signature,
            )
            try:
                proof_state.sync_to_graph(
                    dossier,
                    phase="llm_tool_decl_application",
                    turn_index=turn_index,
                    refresh_target_node_ids=[node.node_id],
                )
            except Exception:
                pass
            return {
                "node_id": node.node_id,
                "status": "closed",
                "helper_name": helper_name,
            }
        retryable_acceptance = bool(
            str(accept_status.get("status") or "")
            in {"retryable_error", "cancelled"}
            or _decl_application_failure_is_retryable(
                str(accept_status.get("error_kind") or "")
            )
        )
        if not retryable_acceptance:
            node.pending_helper_acceptance = {}
        else:
            retain_pending_helper_acceptance_retry(
                proof_state=proof_state,
                node=node,
                status=accept_status,
            )
        out = {
            "node_id": node.node_id,
            "status": (
                "helper_acceptance_deferred"
                if retryable_acceptance
                else "helper_rejected"
            ),
        }
        if accept_status:
            out["acceptance_status"] = dict(accept_status)
        return out
    if not applicable:
        if deadline_elapsed():
            return deadline_result()
        proof_state.record_decl_application_result(
            node_id=node.node_id,
            ok=False,
            attempt_count=1,
            exit_reason=error_kind or "decl_application_not_applicable",
            decl_application_signature=signature,
        )
        return {"node_id": node.node_id, "status": "recorded_rejection"}
    return {"node_id": node.node_id, "status": "no_state_change"}


async def _run_apply_decl_to_goal_tool_impl(
    lean: LeanRunner,
    *,
    preamble: str,
    context_lemmas: Sequence[str],
    args: Dict[str, Any],
    conv: Any = None,
    dossier: Optional[ProofDossier] = None,
    proof_state: Optional[ProofSearchState] = None,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    turn_index: int = 0,
    tool_call_index: int = 0,
    max_residual_goals: int = 4,
    goal_statement_override: str = "",
    redact_solution_refs: bool = True,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    deadline_monotonic: float = 0.0,
) -> str:
    """Probe one declaration's applicability to a stated goal.

    Thin wrapper around ``LeanRunner.apply_decl_to_goal`` that handles
    arg extraction and rendering for the LLM tool loop. The caller must
    pass ``conv.preamble`` (the LLM-facing axiom view) so the probe's outputs
    are leak-safe; see the dispatcher comment in ``run_conversation`` for the
    full rationale.
    """
    requested_statement = str(args.get("statement", "") or "").strip()
    active_statement = str(goal_statement_override or "").strip()
    statement = active_statement or requested_statement
    statement_overridden = bool(
        active_statement
        and requested_statement
        and requested_statement != active_statement
    )
    decl_name = str(args.get("decl_name", "") or "").strip()

    def _json_response(payload: Dict[str, Any]) -> str:
        return json.dumps(payload, ensure_ascii=False, sort_keys=True, default=str)

    def _sanitize_tool_value(value: Any, *, limit: int = 280) -> str:
        return _prompt_safe_inline_text(
            value,
            limit=limit,
            redact_solution_refs=redact_solution_refs,
        )

    def _sanitize_lean_tool_value(value: Any, *, limit: int = 280) -> str:
        return _prompt_safe_lean_diagnostic_text(
            value,
            limit=limit,
            redact_solution_refs=redact_solution_refs,
        )

    def _sanitize_tool_goals(values: Sequence[Any]) -> List[str]:
        return [_sanitize_lean_tool_value(goal, limit=280) for goal in values]

    def _sanitize_tool_payload(value: Any, *, limit: int = 280) -> Any:
        if value is None or isinstance(value, (bool, int, float)):
            return value
        if isinstance(value, dict):
            return {
                _sanitize_tool_value(key, limit=120): _sanitize_tool_payload(
                    item,
                    limit=limit,
                )
                for key, item in value.items()
            }
        if isinstance(value, (list, tuple)):
            return [_sanitize_tool_payload(item, limit=limit) for item in value]
        return _sanitize_tool_value(value, limit=limit)

    def _unsafe_decl_response(error_kind: str, error_text: str) -> str:
        if dossier is not None:
            try:
                dossier.record_decl_application(
                    turn_index=turn_index,
                    tool_call_index=tool_call_index,
                    statement=statement,
                    decl_name=decl_name,
                    applicable=False,
                    proof_stub="",
                    remaining_goals=[],
                    error_kind=error_kind,
                    error_text=error_text,
                    error_text_is_lean_diagnostic=False,
                    decl_type="",
                )
            except Exception as record_exc:
                safe_record_exc = _sanitize_tool_value(
                    f"{type(record_exc).__name__}: {record_exc}",
                    limit=500,
                )
                _trace(
                    "",
                    "  [_run_apply_decl_to_goal_tool] "
                    "dossier.record_decl_application failed "
                    f"({safe_record_exc}); "
                    "preserving unsafe-decl rejection result",
                )
        message = (
            "Applicable: no "
            f"({_sanitize_tool_value(error_kind, limit=120)})\n"
            f"Reason: {_sanitize_tool_value(error_text, limit=360)}"
        )
        return _json_response(
            {
                "decl_name": _sanitize_tool_value(decl_name, limit=160),
                "statement": _sanitize_tool_value(statement, limit=280),
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": _sanitize_tool_value(error_kind, limit=120),
                "error": _sanitize_tool_value(error_text, limit=400),
                "decl_type": "",
                "message": message,
            }
        )

    def deadline_elapsed() -> bool:
        try:
            return bool(
                (deadline_exhausted and deadline_exhausted())
                or (
                    float(deadline_monotonic or 0.0) > 0.0
                    and time.monotonic() >= float(deadline_monotonic)
                )
            )
        except Exception:
            return True

    def retryable_deferred_response(error_kind: str, error_text: str) -> str:
        safe_kind = _sanitize_tool_value(error_kind, limit=120)
        safe_error = _sanitize_tool_value(error_text, limit=400)
        return _json_response(
            {
                "decl_name": _sanitize_tool_value(decl_name, limit=160),
                "statement": _sanitize_tool_value(statement, limit=280),
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": safe_kind,
                "error": safe_error,
                "decl_type": "",
                "neutral": True,
                "retryable": True,
                "message": f"Applicable: deferred ({safe_kind})",
            }
        )

    answer_safety_source = conv if conv is not None else dossier
    explicit_conv_answer_payload_present = (
        getattr(conv, "official_answer_payload_present", None)
        if conv is not None
        else None
    )
    explicit_dossier_answer_payload_present = (
        getattr(dossier, "official_answer_payload_present", None)
        if dossier is not None
        else None
    )
    explicit_official_answer_payload_present = (
        explicit_conv_answer_payload_present
        if explicit_conv_answer_payload_present is not None
        else explicit_dossier_answer_payload_present
    )
    official_answer_payload_present = explicit_official_answer_payload_present
    if official_answer_payload_present is None and conv is not None:
        try:
            official_answer_payload_present = _conversation_has_official_answer_payload(
                conv
            )
        except Exception:
            official_answer_payload_present = None
    if (
        official_answer_payload_present is None
        or (
            official_answer_payload_present is False
            and explicit_official_answer_payload_present is None
        )
    ):
        combined_answer_context = "\n".join([statement, decl_name, preamble])
        value_decl_names = _official_solution_value_decl_names(preamble)
        symbol_names = _official_solution_symbol_names(combined_answer_context)
        if value_decl_names and value_decl_names & symbol_names:
            official_answer_payload_present = True
    answer_safety_kwargs = {
        "suppress_solution_placeholders": bool(
            getattr(answer_safety_source, "suppress_solution_placeholders", True)
        ),
        "opaque_mode": bool(getattr(answer_safety_source, "opaque_mode", True)),
        "allow_official_answer_visibility": bool(
            getattr(answer_safety_source, "allow_official_answer_visibility", False)
        ),
        "official_answer_payload_present": official_answer_payload_present,
    }

    if not statement:
        return _json_response(
            {
                "decl_name": _sanitize_tool_value(decl_name, limit=160),
                "statement": _sanitize_tool_value(statement, limit=280),
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": "empty_statement",
                "error": "empty `statement`",
                "decl_type": "",
                "message": (
                    "Error: empty `statement`. Pass the exact theorem statement or "
                    "current goal you are testing the declaration against."
                ),
            }
        )
    if not decl_name:
        return _json_response(
            {
                "decl_name": _sanitize_tool_value(decl_name, limit=160),
                "statement": _sanitize_tool_value(statement, limit=280),
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": "empty_decl_name",
                "error": "empty `decl_name`",
                "decl_type": "",
                "message": (
                    "Error: empty `decl_name`. Pass a Lean declaration name surfaced by "
                    "`search_mathlib` or `check_lean`."
                ),
            }
        )
    if is_answer_unsafe_statement_text(decl_name, **answer_safety_kwargs):
        return _unsafe_decl_response(
            "answer_unsafe_decl_name",
            (
                "apply_decl_to_goal does not test or recommend `_solution` "
                "declarations; use mathematical lemmas, verified helpers, or "
                "prove the needed bridge directly."
            ),
        )
    execution_preamble = str(
        getattr(conv, "lean_preamble", "") if conv is not None else ""
    ).strip() or str(preamble or "")
    try:
        sync_active_root_targets = (
            _framed_active_root_targets_for_conversation(
                dossier,
                conv,
                helper_blocks=context_lemmas,
            )
            if conv is not None and dossier is not None
            else []
        )
    except Exception:
        sync_active_root_targets = []
    if proof_state is not None:
        pending_parent = _proof_state_node_for_tool_statement(
            proof_state,
            statement,
            active_root_targets=sync_active_root_targets,
        )
        pending_residual = (
            dict(
                getattr(
                    pending_parent,
                    "pending_residual_goal_extraction",
                    {},
                )
                or {}
            )
            if pending_parent is not None
            else {}
        )
        pending_helper = (
            dict(
                getattr(pending_parent, "pending_helper_acceptance", {}) or {}
            )
            if pending_parent is not None
            else {}
        )
        valid_pending_helper = bool(
            pending_parent is not None
            and str(pending_helper.get("helper_block") or "").strip()
            and str(pending_helper.get("target_hash") or "")
            == text_hash(str(getattr(pending_parent, "target", "") or ""))
        )
        if pending_residual or valid_pending_helper:
            # ProofSearchState owns one exact pending verifier frame per
            # parent/lane. Do not pay for a second declaration stub that could
            # only overwrite the first before fair replay has drained it.
            return retryable_deferred_response(
                "decl_application_pending_receipt_deferred",
                "this goal already has a paid verifier request; retry the declaration after that request rotates",
            )
    operation_timeout_s = _typed_residual_operation_timeout(lean, 0.0)
    absolute_deadline = max(0.0, float(deadline_monotonic or 0.0))
    current_task = asyncio.current_task()
    if current_task is not None and current_task.cancelling() > 0:
        raise asyncio.CancelledError
    if (
        absolute_deadline > 0.0
        and absolute_deadline - time.monotonic() < operation_timeout_s + 1.0
    ) or _fully_funded_operation_timeout(
        operation_timeout_s,
        absolute_deadline,
    ) <= 0.0:
        return retryable_deferred_response(
            "decl_application_deadline_deferred",
            "the turn cannot fund the complete declaration probe; retry it in a fresh operation window",
        )

    async def run_decl_probe() -> Any:
        return await lean.apply_decl_to_goal(
            statement,
            decl_name,
            preamble_override=execution_preamble,
            lemmas=list(context_lemmas or []),
            timeout_s=operation_timeout_s,
        )

    exception_text = ""
    try:
        result = await _await_serialized_lean_operation(
            lean,
            run_decl_probe,
            timeout_s=operation_timeout_s,
            deadline_monotonic=absolute_deadline,
            operation_label="llm_tool_decl_application_probe",
            release_unrecyclable_tail=True,
        )
    except asyncio.CancelledError:
        raise
    except (_LeanOperationDeadline, asyncio.TimeoutError) as exc:
        return retryable_deferred_response(
            "decl_application_timeout_deferred",
            str(exc or "declaration probe timed out without a mathematical verdict"),
        )
    except Exception as exc:
        return retryable_deferred_response(
            "decl_application_infrastructure_deferred",
            f"{type(exc).__name__}: {exc}",
        )

    applicable = bool(result.get("applicable", False))
    proof_stub = str(result.get("proof_stub", "") or "")
    remaining_goals = list(result.get("remaining_goals", []) or [])
    error_kind = str(result.get("error_kind", "") or "")
    error_text = str(result.get("error", "") or "")
    decl_type = str(result.get("decl_type", "") or "").strip()
    if not applicable and _decl_application_failure_is_retryable(error_kind):
        return retryable_deferred_response(
            "decl_application_infrastructure_deferred",
            f"{error_kind}: {error_text}" if error_text else error_kind,
        )
    error_text_is_lean_diagnostic = (
        not bool(exception_text)
        and _decl_application_error_is_lean_diagnostic(error_kind, error_text)
    )
    if (
        applicable
        and proof_stub
        and is_answer_unsafe_statement_text(proof_stub, **answer_safety_kwargs)
    ):
        applicable = False
        proof_stub = ""
        remaining_goals = []
        error_kind = "answer_unsafe_proof_stub"
        error_text = (
            "Lean suggested a proof stub that references a `_solution` "
            "placeholder, so the probe is treated as rejected."
        )
        error_text_is_lean_diagnostic = False
    if deadline_elapsed():
        return _json_response(
            {
                "decl_name": _sanitize_tool_value(decl_name, limit=160),
                "statement": _sanitize_tool_value(statement, limit=280),
                "applicable": False,
                "proof_stub": "",
                "remaining_goals": [],
                "error_kind": "llm_turn_elapsed_budget_exhausted",
                "error": "turn deadline expired before declaration result commit",
                "decl_type": "",
                "message": "Applicable: no (llm_turn_elapsed_budget_exhausted)",
            }
        )
    if dossier is not None:
        # Bonus #1 fix (2026-05-08): isolate the dossier write so a
        # graph-corruption / I/O / record-shape error here cannot escape
        # past this function. The B1 dispatcher try/except would catch
        # it, but the synthesized "Tool runner error" message would lose
        # the Lean-derived result the model needs (proof_stub, remaining
        # goals, decl type). Trace the dossier failure but keep rendering
        # the Lean output to the LLM.
        try:
            dossier.record_decl_application(
                turn_index=turn_index,
                tool_call_index=tool_call_index,
                statement=statement,
                decl_name=decl_name,
                applicable=applicable,
                proof_stub=proof_stub,
                remaining_goals=remaining_goals,
                error_kind=error_kind,
                error_text=error_text,
                error_text_is_lean_diagnostic=error_text_is_lean_diagnostic,
                decl_type=decl_type,
            )
        except Exception as record_exc:
            safe_record_exc = _sanitize_tool_value(
                f"{type(record_exc).__name__}: {record_exc}",
                limit=500,
            )
            _trace(
                "",
                "  [_run_apply_decl_to_goal_tool] "
                "dossier.record_decl_application failed "
                f"({safe_record_exc}); "
                "preserving Lean-derived tool result",
            )

    proof_state_update: Dict[str, Any] = {}
    try:
        proof_state_update = await _sync_apply_decl_to_proof_state(
            lean=lean,
            conv=conv
            or SimpleNamespace(preamble=preamble, lean_preamble=preamble),
            dossier=dossier,
            proof_state=proof_state,
            proof_cache=proof_cache,
            statement=statement,
            decl_name=decl_name,
            applicable=applicable,
            proof_stub=proof_stub,
            remaining_goals=remaining_goals,
            error_kind=error_kind,
            turn_index=turn_index,
            context_lemmas=context_lemmas,
            residual_preamble=execution_preamble,
            active_root_targets=sync_active_root_targets,
            max_residual_goals=max_residual_goals,
            deadline_exhausted=deadline_exhausted,
            deadline_monotonic=deadline_monotonic,
        )
    except Exception as state_exc:
        proof_state_update = {
            "status": "state_sync_error",
            "error_type": type(state_exc).__name__,
            "error": str(state_exc)[:240],
        }
    if proof_state_update and dossier is not None:
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            increment("mini_apply_decl_tool_state_updates")
            if str(proof_state_update.get("status") or "") in {
                "closed",
                "root_finalized",
            }:
                increment("mini_apply_decl_tool_state_closures")

    if applicable:
        lines = [
            "Applicable: yes — try "
            f"`{_sanitize_tool_value(proof_stub, limit=240)}`"
        ]
        if remaining_goals:
            lines.append(f"Remaining {len(remaining_goals)} goal(s):")
            for i, goal in enumerate(remaining_goals[:5], 1):
                preview = _sanitize_lean_tool_value(goal, limit=280)
                lines.append(f"  {i}. {preview}")
        else:
            lines.append("Remaining goals: none — declaration closes the target.")
        message = "\n".join(lines)
    else:
        lines = [
            "Applicable: no "
            f"({_sanitize_tool_value(error_kind or 'no_match', limit=120)})"
        ]
        if decl_type:
            # Surface the lemma's actual type signature so the LLM can see
            # what it really requires instead of repeatedly guessing wrong
            # applications. This is metadata rather than a Lean error
            # diagnostic, so keep backticked spans conservative.
            shown_decl_type = _sanitize_tool_value(decl_type, limit=280)
            lines.append(f"Declaration type: {shown_decl_type}")
        if error_text and not exception_text:
            error_sanitizer = (
                _sanitize_lean_tool_value
                if error_text_is_lean_diagnostic
                else _sanitize_tool_value
            )
            error_label = "Lean output" if error_text_is_lean_diagnostic else "Reason"
            lines.append(
                f"{error_label}: {error_sanitizer(error_text, limit=400)}"
            )
        if exception_text:
            lines.append(f"Error: {_sanitize_tool_value(exception_text, limit=240)}")
        message = "\n".join(lines)

    payload = {
        "decl_name": _sanitize_tool_value(decl_name, limit=160),
        "statement": _sanitize_tool_value(statement, limit=280),
        "applicable": applicable,
        "proof_stub": _sanitize_tool_value(proof_stub, limit=240),
        "remaining_goals": _sanitize_tool_goals(remaining_goals),
        "error_kind": _sanitize_tool_value(error_kind, limit=120),
        "error": ""
        if applicable
        else (
            _sanitize_lean_tool_value(error_text, limit=400)
            if error_text and error_text_is_lean_diagnostic and not exception_text
            else _sanitize_tool_value(error_text or exception_text, limit=400)
        ),
        "decl_type": _sanitize_tool_value(decl_type, limit=280),
        "message": message,
    }
    if statement_overridden:
        payload["requested_statement"] = _sanitize_tool_value(
            requested_statement,
            limit=280,
        )
        payload["statement_source"] = "active_goal_override"
    if proof_state_update:
        payload["proof_state_update"] = _sanitize_tool_payload(proof_state_update)
    return _json_response(payload)


async def _run_apply_decl_to_goal_tool(*args: Any, **kwargs: Any) -> str:
    """Probe a declaration without leaving a late dossier/graph mutation."""

    supplied_deadline_exhausted = kwargs.get("deadline_exhausted")
    try:
        absolute_deadline = max(
            0.0,
            float(kwargs.get("deadline_monotonic", 0.0) or 0.0),
        )
    except (TypeError, ValueError):
        absolute_deadline = 0.0

    def combined_deadline_exhausted() -> bool:
        try:
            return bool(
                (supplied_deadline_exhausted and supplied_deadline_exhausted())
                or (
                    absolute_deadline > 0.0
                    and time.monotonic() >= absolute_deadline
                )
            )
        except Exception:
            return True

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=(
            combined_deadline_exhausted
            if supplied_deadline_exhausted is not None
            or absolute_deadline > 0.0
            else None
        ),
        dossier=kwargs.get("dossier"),
        proof_state=kwargs.get("proof_state"),
        label="apply_decl_to_goal_tool",
    )
    cancelled_payload = {
        "applicable": False,
        "proof_stub": "",
        "remaining_goals": [],
        "error_kind": "llm_turn_elapsed_budget_exhausted",
        "error": "turn deadline expired before declaration result commit",
        "message": "Applicable: no (llm_turn_elapsed_budget_exhausted)",
    }
    with transaction:
        if not transaction.can_mutate():
            return json.dumps(cancelled_payload, ensure_ascii=False, sort_keys=True)
        result = await _run_apply_decl_to_goal_tool_impl(*args, **kwargs)
        if not transaction.can_mutate():
            return json.dumps(cancelled_payload, ensure_ascii=False, sort_keys=True)
    if transaction.enabled and not transaction.committed:
        failed_payload = dict(cancelled_payload)
        if not transaction.deadline_won:
            failed_payload["error_kind"] = "deadline_mutation_commit_failed"
            failed_payload["error"] = "declaration result commit was rolled back"
            failed_payload["message"] = "Applicable: no (deadline_mutation_commit_failed)"
        return json.dumps(failed_payload, ensure_ascii=False, sort_keys=True)
    return result


async def _run_check_lean_tool(
    lean: LeanRunner,
    *,
    preamble: str,
    context_lemmas: Sequence[str] = (),
    args: Dict[str, Any],
    redact_solution_refs: bool = True,
    timeout_s: float = 10.0,
) -> str:
    """Run answer-safe #check queries for the LLM tool loop."""
    from .deadline_guard import await_with_strict_deadline

    queries = _extract_check_queries(args)
    if not queries:
        return (
            "Error: no supported #check terms. Provide bare declaration names "
            "or lines like `#check tsum_subtype`. Arbitrary Lean scripts are "
            "not supported by this tool."
        )

    try:
        adapter_timeout_s = max(0.05, float(timeout_s or 10.0))
    except (TypeError, ValueError):
        adapter_timeout_s = 10.0
    configured_timeout_s = None
    for raw in (
        getattr(getattr(lean, "cfg", None), "timeout_s", None),
        getattr(lean, "timeout_s", None),
    ):
        try:
            value = float(raw)
        except (TypeError, ValueError):
            continue
        if value > 0.0:
            configured_timeout_s = value
            break
    # Keep the advertised adapter budget. The controller may wait as long as
    # the Lean runner's configured check so a late successful #check is not
    # discarded when the adapter swallows cancellation. This does not take
    # the proof-state Lean lock: #check is oracle work and must not defer a
    # later try_lean or reject just because a cancelled tail still holds it.
    controller_timeout_s = adapter_timeout_s
    if configured_timeout_s is not None:
        controller_timeout_s = max(adapter_timeout_s, configured_timeout_s)

    lines: List[str] = [f"{len(queries)} check(s):"]
    for i, query in enumerate(queries, 1):
        try:
            result = await await_with_strict_deadline(
                lean.check_term_type(
                    query,
                    preamble_override=preamble,
                    lemmas=list(context_lemmas or []),
                    timeout_s=adapter_timeout_s,
                ),
                timeout_s=controller_timeout_s,
                operation_label="mini_tool_check_lean",
                operation_ownership="result_only",
            )
        except asyncio.TimeoutError:
            result = "Note: type information unavailable (verifier busy)"
        except Exception as exc:
            safe_exc_type = _prompt_safe_inline_text(
                type(exc).__name__,
                limit=120,
                redact_solution_refs=redact_solution_refs,
            )
            safe_exc = _prompt_safe_inline_text(
                exc,
                limit=500,
                redact_solution_refs=redact_solution_refs,
            )
            result = (
                f"Error: {safe_exc_type}: "
                f"{safe_exc}"
            )
        result = str(result or "").strip() or "Error: no output"
        result = _prompt_safe_lean_diagnostic_text(
            result,
            limit=700,
            redact_solution_refs=redact_solution_refs,
        )
        safe_query = _prompt_safe_inline_text(
            query,
            limit=180,
            redact_solution_refs=redact_solution_refs,
        )
        lines.append(f"{i}. #check {safe_query}")
        lines.append(f"   {result}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Tracing — print every turn so the user can watch the loop in real time.
# ---------------------------------------------------------------------------

def _indent(text: str, prefix: str) -> str:
    return "\n".join(prefix + line for line in (text or "").splitlines())


def _trace(prefix: str, msg: str) -> None:
    print(f"{prefix}{msg}", flush=True)


def _legacy_no_proof_target_integrity_metadata(
    *,
    conv: Conversation,
    dossier: Optional[ProofDossier],
    recorder: Optional[RunRecorder],
    llm_output: str,
    phase: str,
    turn: int,
    model_id: str,
    common_record: Mapping[str, Any],
) -> Dict[str, Any]:
    """Materialize target-integrity work for legacy no-proof exits."""

    if dossier is None:
        return {}
    target = str(
        getattr(conv, "goal_statement", "") or getattr(dossier, "root_statement", "") or ""
    ).strip()
    signals = classify_target_integrity_signals(
        llm_output=str(llm_output or ""),
        proof="",
        failure_analysis={},
        target_statement=target,
        selected_work_type="",
    )
    if not signals:
        return {}
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        increment("mini_session_target_integrity_signals", len(signals))
        increment("mini_session_target_integrity_no_proof_signals", len(signals))
    derived_common_record = dict(common_record or {})
    for key in (
        "tool_calls_used",
        "tool_call_log",
        "compute_examples_tool_calls",
        "compute_examples_successes",
        "malformed_tool_call_count",
    ):
        derived_common_record.pop(key, None)
    for signal in signals:
        metric = str(signal.get("metric") or "").strip()
        if metric and callable(increment):
            increment(metric, 1)
        if recorder is not None:
            recorder.record_turn({
                **derived_common_record,
                "phase": "target_integrity_signal",
                "turn_in_phase": turn,
                "model": model_id,
                "role": phase,
                "kind": str(signal.get("kind") or ""),
                "target_integrity_signal_kind": str(signal.get("kind") or ""),
                "target_integrity_signal_kinds": [
                    str(item.get("kind") or "") for item in signals
                ],
                "target_integrity_signals": list(signals),
                "match": str(signal.get("match") or ""),
                "selected_work_type": "",
                "target_statement": target,
                "source": "no_proof_extracted",
                "verdict": "detected",
            })
    try:
        from ensemble_prover.mini_session.turn.post_failure import (
            _record_target_integrity_adjudication,
        )

        obligation_ids, replan_ids, materialized = _record_target_integrity_adjudication(
            dossier=dossier,
            target_statement=target,
            signals=signals,
            phase=phase,
            turn_index=turn,
            selected_work_type="",
            selected_work_record={},
        )
    except Exception:
        obligation_ids, replan_ids, materialized = [], [], False
    if recorder is not None and (obligation_ids or replan_ids):
        recorder.record_turn({
            **derived_common_record,
            "phase": "target_integrity_adjudication",
            "turn_in_phase": turn,
            "model": model_id,
            "role": phase,
            "selected_work_type": "",
            "target_statement": target,
            "obligation_node_ids": list(obligation_ids),
            "replan_node_ids": list(replan_ids),
            "signal_kinds": [str(signal.get("kind") or "") for signal in signals],
            "source": "no_proof_extracted",
            "verdict": "materialized" if materialized else "already_materialized",
        })
        if materialized and callable(increment):
            increment(
                "mini_session_target_integrity_no_proof_adjudication_materialized",
                1,
            )
    feedback = target_integrity_feedback(list(signals))
    if feedback:
        conv.append_user(feedback)
    return {
        "target_integrity_signals": list(signals),
        "target_integrity_bypass_local_repair": True,
        "target_integrity_disable_proof_state_repair": True,
        "target_integrity_obligation_node_ids": list(obligation_ids),
        "target_integrity_replan_node_ids": list(replan_ids),
        "target_integrity_adjudication_materialized": bool(materialized),
        "target_integrity_adjudication_available": bool(obligation_ids or replan_ids),
        "target_integrity_adjudication_created": bool(materialized),
    }


# ---------------------------------------------------------------------------
# Core conversational loop. ONE function drives prove and refine alike.
# ---------------------------------------------------------------------------

_PARALLEL_SAMPLE_CANCEL_DRAIN_TIMEOUT_S = 0.25
_PARALLEL_SAMPLE_LATE_GRACE_DEFAULT_S = 2.0


class _TurnTemperatureRecorder:
    """Recorder proxy that annotates all records from one LLM turn."""

    def __init__(self, wrapped: Any, metadata: Mapping[str, Any]) -> None:
        self._wrapped = wrapped
        self._metadata = dict(metadata or {})

    def update_metadata(self, metadata: Mapping[str, Any]) -> None:
        self._metadata = dict(metadata or {})

    def record_turn(self, record: Mapping[str, Any]) -> None:
        payload = dict(self._metadata)
        payload.update(dict(record or {}))
        self._wrapped.record_turn(payload)

    def __getattr__(self, name: str) -> Any:
        return getattr(self._wrapped, name)


def _effective_compute_examples_tool_enabled(
    raw_enabled: Any,
    *,
    searcher: Optional[MathlibApiSearcher],
    lean_check_tool_enabled: bool,
    try_lean_tool_enabled: bool,
    apply_decl_to_goal_tool_enabled: bool,
) -> bool:
    # ``None`` preserves callers' pre-compute tool schema.  The CLI passes
    # its explicit default, while programmatic callers must opt in rather
    # than silently gaining a tool that changes provider request contracts.
    del searcher, lean_check_tool_enabled, try_lean_tool_enabled
    del apply_decl_to_goal_tool_enabled
    return bool(raw_enabled)


async def run_conversation(
    *,
    conv: Conversation,
    client: OpenAICompatClient,
    lean: LeanRunner,
    max_turns: int,
    trace_prefix: str = "",
    recorder: Optional[RunRecorder] = None,
    searcher: Optional[MathlibApiSearcher] = None,
    lean_check_tool_enabled: bool = True,
    try_lean_tool_enabled: bool = False,
    compute_examples_tool_enabled: Optional[bool] = None,
    apply_decl_to_goal_tool_enabled: bool = False,
    max_tool_calls_per_turn: int = 10,
    raw_feedback: bool = False,
    dossier: Optional[ProofDossier] = None,
    proof_state: Optional[ProofSearchState] = None,
    temperature_override: Optional[float] = None,
    mini_phase_temperatures: Optional[MiniPhaseTemperatures] = None,
    repair_retrieval_enabled: bool = True,
    repair_retrieval_top_k: int = 6,
    proof_state_child_tactics_enabled: bool = True,
    proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
    proof_state_child_tactic_max_candidates: int = 32,
    proof_state_child_goal_limit: int = 3,
    proof_state_decl_application_limit: int = 6,
    proof_state_batch_parallelism: int = 1,
    proof_cache: Optional[MiniVerifiedLemmaCache] = None,
    cost_controller: Optional[CostBudgetController] = None,
    tactic_source_suppression_records: Sequence[Mapping[str, Any]] = (),
    session_scope: str = "problem",
) -> Tuple[bool, Optional[str]]:
    """Drive one prove-or-refine conversation for a bounded turn budget.

    ``max_turns`` is the public LLM-attempt budget. A reused-fragment policy
    redirect may grant a small bounded bonus turn so the model sees the local
    repair feedback that caused the redirect; telemetry reports both the base
    budget and the effective turn limit.

    Returns ``(ok, proof_text)``. The conversation history is mutated in
    place on ``conv`` so a refiner can take over the transcript afterwards.
    Per-turn records flow into ``recorder`` (if provided) for offline diagnosis.

    When tools are enabled, the LLM may invoke ``search_mathlib`` (if
    ``searcher`` is provided) and/or ``check_lean`` before producing the proof
    for that turn. Tool results are appended to the conversation history so
    the model sees them on subsequent calls within the same turn.
    """
    model_id = f"{getattr(client.cfg, 'name', '?')}/{getattr(client.cfg, 'model', '?')}"
    compute_examples_tool_enabled = _effective_compute_examples_tool_enabled(
        compute_examples_tool_enabled,
        searcher=searcher,
        lean_check_tool_enabled=bool(lean_check_tool_enabled),
        try_lean_tool_enabled=bool(try_lean_tool_enabled),
        apply_decl_to_goal_tool_enabled=bool(apply_decl_to_goal_tool_enabled),
    )
    base_use_tools = (
        searcher is not None
        or lean_check_tool_enabled
        or try_lean_tool_enabled
        or compute_examples_tool_enabled
        or apply_decl_to_goal_tool_enabled
    )
    base_tools_list: List[Dict[str, Any]] = []
    if searcher is not None:
        if _searcher_supports_static_mathlib(searcher):
            base_tools_list.append(SEARCH_MATHLIB_TOOL)
        if isinstance(searcher, MathematicalRetrievalService):
            base_tools_list.append(SEARCH_THEOREMS_TOOL)
    if lean_check_tool_enabled:
        base_tools_list.append(CHECK_LEAN_TOOL)
    if try_lean_tool_enabled:
        base_tools_list.append(TRY_LEAN_TOOL)
        base_tools_list.append(CERTIFY_COUNTEREXAMPLE_TOOL)
    if compute_examples_tool_enabled:
        base_tools_list.append(COMPUTE_EXAMPLES_TOOL)
    if apply_decl_to_goal_tool_enabled:
        base_tools_list.append(APPLY_DECL_TO_GOAL_TOOL)

    def _current_feedback_lemmas() -> List[str]:
        if dossier is None:
            return []
        return list(
            _feedback_lemmas_for_answer_safe_recheck(
                dossier.verified_helper_blocks(),
                conv,
            )
        )

    def _current_verified_helper_blocks() -> List[str]:
        if dossier is None:
            return []
        visible_helpers = list(dossier.verified_helper_blocks())
        forced_context_helpers = [
            str(block or "").strip()
            for block in list(getattr(dossier, "forced_context_helper_blocks", ()) or ())
            if str(block or "").strip()
        ]
        if forced_context_helpers:
            return ProofDossier._merge_replay_helper_blocks(
                visible_helpers,
                forced_context_helpers,
            )
        return visible_helpers

    def _current_active_root_frame_helper_blocks() -> List[str]:
        if dossier is None:
            return []
        return list(dossier.verified_helper_blocks())

    def _verified_helper_blocks_for_proof(proof_text: str) -> List[str]:
        visible_helpers = _current_verified_helper_blocks()
        if dossier is None:
            return visible_helpers
        all_helpers = [
            str(getattr(helper, "source", "") or "").strip()
            for helper in list(getattr(dossier, "verified_helpers", {}).values())
            if str(getattr(helper, "source", "") or "").strip()
        ]
        referenced = _helpers_referenced_by_proof(all_helpers, str(proof_text or ""))
        if not referenced:
            return visible_helpers
        referenced_names = _helper_names_from_blocks(referenced)
        replay_closure = getattr(dossier, "root_replay_helper_closure", None)
        if callable(replay_closure):
            closed = replay_closure(
                replay_helpers=referenced,
                support_helper_names=referenced_names,
            )
            if closed:
                referenced = list(closed)
        return ProofDossier._merge_replay_helper_blocks(
            visible_helpers,
            referenced,
        )

    def _root_tactic_helper_blocks_for_names(helper_names: Sequence[str]) -> List[str]:
        visible_helpers = _current_verified_helper_blocks()
        if dossier is None:
            return visible_helpers
        clean_names = [
            str(name or "").strip()
            for name in list(helper_names or ())
            if str(name or "").strip()
        ]
        if not clean_names:
            return visible_helpers
        replay_closure = getattr(dossier, "root_replay_helper_closure", None)
        if not callable(replay_closure):
            return visible_helpers
        closed = replay_closure(support_helper_names=clean_names)
        if not closed:
            return visible_helpers
        return ProofDossier._merge_replay_helper_blocks(
            visible_helpers,
            list(closed),
        )

    def _increment_dossier_tool_metric(key: str, amount: int = 1) -> None:
        if dossier is None:
            return
        increment = getattr(dossier, "increment_tool_metric", None)
        if callable(increment):
            try:
                increment(key, amount)
                return
            except Exception:
                pass
        metrics = getattr(dossier, "tool_metrics", None)
        if isinstance(metrics, dict):
            metrics[key] = int(metrics.get(key, 0) or 0) + int(amount or 0)

    turn = 0
    # The recursive claim controller uses this invocation-local receipt to
    # share one public turn budget across prover and refiner handoff.  Count
    # outer semantic turns, not inner provider/tool round trips.
    conv._last_run_turns_used = 0
    turn_limit = max_turns
    reused_fragment_redirect_bonus_remaining = 2
    repair_self_check_redirect_bonus_remaining = 1
    format_policy_redirect_bonus_remaining = 1
    base_recorder = recorder
    while turn < turn_limit:
        turn += 1
        conv._last_run_turns_used = turn
        handoff_compaction_record: Dict[str, Any] = {}
        if str(getattr(conv, "role", "") or "") == "refine":
            handoff_compact = getattr(conv, "compact_history_for_refine_handoff", None)
            if callable(handoff_compact):
                try:
                    handoff_compaction_record = handoff_compact()
                except Exception as exc:
                    handoff_compaction_record = {}
                    _trace(
                        trace_prefix,
                        f"  refiner handoff compaction failed: {type(exc).__name__}: {exc}",
                    )
                if handoff_compaction_record:
                    _increment_dossier_tool_metric("mini_refine_handoff_compactions", 1)
                    _increment_dossier_tool_metric(
                        "mini_refine_handoff_compacted_messages",
                        int(handoff_compaction_record.get("removed_messages", 0) or 0),
                    )
                    _increment_dossier_tool_metric(
                        "mini_refine_handoff_compacted_chars",
                        int(handoff_compaction_record.get("removed_chars", 0) or 0),
                    )
                    _increment_dossier_tool_metric(
                        "mini_refine_handoff_compacted_tool_rounds",
                        int(
                            handoff_compaction_record.get(
                                "removed_tool_rounds", 0
                            )
                            or 0
                        ),
                    )
        compaction_record = conv.compact_history_for_next_turn()
        repair_turn_active = _repair_turn_requires_self_check(conv)
        temperature_decision = resolve_mini_temperature(
            mini_phase_temperatures,
            MiniTemperatureContext(
                role=str(getattr(conv, "role", "") or "prove"),
                action_id=f"legacy_{getattr(conv, 'role', 'prove')}",
                sample_temperature=temperature_override,
                repair_turn_active=bool(repair_turn_active),
                repair_self_check=bool(repair_turn_active),
            ),
        )
        effective_temperature_override = (
            temperature_decision.provider_temperature_override()
        )
        temperature_call_metadata = mini_temperature_metadata(
            temperature_decision,
            client=client,
        )
        recorder = (
            _TurnTemperatureRecorder(base_recorder, temperature_call_metadata)
            if base_recorder is not None
            else None
        )
        effective_try_lean_tool_enabled = bool(
            try_lean_tool_enabled or repair_turn_active
        )
        tools_list = list(base_tools_list)
        if effective_try_lean_tool_enabled and not any(
            (item.get("function") or {}).get("name") == "try_lean"
            for item in tools_list
        ):
            tools_list.append(TRY_LEAN_TOOL)
            tools_list.append(CERTIFY_COUNTEREXAMPLE_TOOL)
        use_tools = bool(base_use_tools or repair_turn_active)
        _trace(
            trace_prefix,
            f"[turn {turn}/{turn_limit} base={max_turns} role={conv.role} model={model_id} "
            f"tools={'on' if use_tools else 'off'}] calling LLM "
            f"(history={len(conv.history)} msgs)...",
        )
        if compaction_record:
            _trace(
                trace_prefix,
                "  compacted stale history: "
                f"removed {compaction_record.get('removed_messages', 0)} msg(s), "
                f"{compaction_record.get('removed_chars', 0)} chars.",
            )
        if handoff_compaction_record:
            _trace(
                trace_prefix,
                "  compacted refiner handoff history: "
                f"removed {handoff_compaction_record.get('removed_messages', 0)} msg(s), "
                f"{handoff_compaction_record.get('removed_chars', 0)} chars.",
            )
        sent_messages = _messages_with_search_context(
            conv.messages_for_llm(),
            dossier,
            proof_state,
            goal_statement=(
                _active_root_tool_goal_statement(
                    dossier,
                    conv=conv,
                    helper_blocks=_current_active_root_frame_helper_blocks(),
                )
                or conv.goal_statement
            ),
            preamble=conv.preamble,
            context_lemmas=_current_feedback_lemmas(),
            session_scope=session_scope,
        )
        turn_started = time.monotonic()
        llm_error: Optional[str] = None
        llm_error_classification = classify_llm_error_text("")
        llm_retry_deadline_record: Dict[str, Any] = {}
        content = ""
        # Tool-use inner loop. We keep calling the LLM as long as it returns
        # tool calls (up to a per-turn cap). Tool results are appended to
        # ``conv.history`` so the next call sees them in scope.
        tool_calls_used = 0
        tool_call_log: List[Dict[str, Any]] = []
        authoritative_falsification = False
        proof_disproof_conflict = False
        repair_self_check_required = (
            repair_turn_active
            and use_tools
            and effective_try_lean_tool_enabled
        )
        repair_self_check_seen = False
        repair_self_check_attempted = False
        repair_self_check_budget_exhausted = False
        repair_self_check_status = ""
        repair_self_check_helper_only_allowed = False
        repair_self_check_reminder_sent = False
        repair_self_check_codes: List[str] = []
        non_verdict_repair_self_check_statuses = {
            "try_lean_infrastructure_error",
            "try_lean_malformed_arguments",
            "try_lean_preflight_error",
        }
        deepseek_dsml_reprompted_after_budget = False
        final_no_tools_policy_reprompted = False
        force_finalize_without_tools = False
        final_no_tools_recovery_attempted = False
        provider_protocol_event = ""
        provider_protocol_original_content = ""
        # One transient LLM retry is shared across all provider calls in this
        # outer conversation turn, so tool-mode and raw fallback cannot each
        # consume their own retry.
        llm_retry_count = 0

        def _set_repair_self_check_gap(*, budget_exhausted: bool = False) -> str:
            nonlocal repair_self_check_budget_exhausted, repair_self_check_status
            if budget_exhausted:
                repair_self_check_budget_exhausted = True
            if repair_self_check_seen:
                repair_self_check_status = "accepted"
            elif repair_self_check_attempted:
                repair_self_check_status = "no_accepted_try_lean"
            elif repair_self_check_status in non_verdict_repair_self_check_statuses:
                pass
            elif budget_exhausted:
                repair_self_check_status = "tool_budget_exhausted"
            else:
                repair_self_check_status = "no_try_lean_call"
            return repair_self_check_status

        def _set_repair_self_check_non_verdict_status(status: str) -> None:
            nonlocal repair_self_check_status
            if repair_self_check_seen or repair_self_check_attempted:
                return
            repair_self_check_status = (
                _merge_repair_self_check_non_verdict_status(
                    repair_self_check_status,
                    status,
                )
            )

        def _repair_self_check_gap_error(status: str) -> str:
            if _repair_self_check_non_verdict_is_compliant(status):
                return ""
            if status == "tool_budget_exhausted":
                return "repair_self_check_tool_budget_exhausted"
            if status == "no_try_lean_call":
                return "repair_self_check_no_try_lean_call"
            if (
                status in non_verdict_repair_self_check_statuses
                and repair_self_check_budget_exhausted
            ):
                return "repair_self_check_tool_budget_exhausted"
            return ""

        async def _invoke_llm_with_retry(
            kind: str,
            call: Any,
            *,
            messages_for_record: Optional[Sequence[dict]] = None,
            tools_for_cost: Sequence[dict] = (),
            max_tokens_override: Optional[int] = None,
        ) -> Any:
            nonlocal llm_retry_count
            nonlocal temperature_call_metadata

            async def _call_once() -> Any:
                nonlocal temperature_call_metadata
                request_messages = list(messages_for_record or sent_messages or ())
                # Keep the compatibility loop on the same exact-selected
                # dispatch contract as the modular loop. The lazy import
                # avoids reversing their module dependency during startup.
                from ensemble_prover.mini_session.turn.tool_loop import (
                    _validate_selected_proof_idea_dispatch_context,
                )

                _validate_selected_proof_idea_dispatch_context(
                    request_messages,
                    dossier,
                )
                try:
                    return await _metered_or_plain_call_compat(
                        cost_controller=cost_controller,
                        client=client,
                        messages=request_messages,
                        role=str(getattr(conv, "role", "") or ""),
                        scope="legacy",
                        action_id=f"legacy_{getattr(conv, 'role', 'prove')}",
                        call_kind=kind,
                        tools=list(tools_for_cost or ()),
                        # This is the same phase-local value passed to the
                        # provider call.  A role's configured maximum is a
                        # model capability and must not inflate reservation
                        # liability for a deliberately bounded phase.
                        max_tokens_override=max_tokens_override,
                        metadata=temperature_call_metadata,
                        retryable_exception_no_charge=lambda exc: (
                            llm_retry_count < 1
                            and _is_retryable_llm_exception(exc)
                        ),
                        invoke=lambda usage_callback: call(usage_callback),
                    )
                finally:
                    temperature_call_metadata = refresh_temperature_metadata_from_client(
                        temperature_call_metadata,
                        client,
                    )
                    updater = getattr(recorder, "update_metadata", None)
                    if callable(updater):
                        updater(temperature_call_metadata)

            try:
                return await _call_once()
            except Exception as exc:
                if llm_retry_count < 1 and _is_retryable_llm_exception(exc):
                    llm_retry_count += 1
                    redact_retry_solution_refs = _conversation_should_redact_solution_refs(
                        conv
                    )
                    error_text = _prompt_safe_inline_text(
                        format_exception(exc),
                        limit=1000,
                        redact_solution_refs=redact_retry_solution_refs,
                    )
                    _trace(
                        trace_prefix,
                        f"  transient LLM {kind} failed; retrying once: {error_text}",
                    )
                    if recorder is not None:
                        retry_messages = copy.deepcopy(
                            list(messages_for_record or sent_messages)
                        )
                        recorder.record_turn({
                            "phase": conv.role,
                            "turn_in_phase": turn,
                            "model": model_id,
                            "messages_sent": retry_messages,
                            "llm_error": error_text,
                            "retry_count": llm_retry_count,
                            "verdict": "llm_call_retry",
                        })
                    return await _call_once()
                raise

        try:
            while True:
                current_messages = _messages_with_search_context(
                    conv.messages_for_llm(),
                    dossier,
                    proof_state,
                    goal_statement=(
                        _active_root_tool_goal_statement(
                            dossier,
                            conv=conv,
                            helper_blocks=_current_active_root_frame_helper_blocks(),
                        )
                        or conv.goal_statement
                    ),
                    preamble=_proof_state_check_preamble(conv),
                    context_lemmas=_current_feedback_lemmas(),
                    session_scope=session_scope,
                )
                # Tools are callable iff enabled AND we still have tool-call
                # budget. Once the budget is exhausted, the provider-aware
                # finalizer must commit to proof text without opening a fresh
                # tool round.
                can_call_tools = (
                    use_tools
                    and tool_calls_used < max_tool_calls_per_turn
                    and not force_finalize_without_tools
                )
                response_data: Any = None
                raw_visible_reasoning_effort = (
                    mini_visible_output_reasoning_effort(
                        client,
                        default="",
                    )
                )
                try:
                    conversation_max_tokens_override = int(
                        getattr(conv, "max_tokens_override", 0) or 0
                    )
                except Exception:
                    conversation_max_tokens_override = 0
                request_max_tokens_override = (
                    conversation_max_tokens_override
                    if conversation_max_tokens_override > 0
                    else None
                )
                if can_call_tools:
                    content, tool_calls = await _invoke_llm_with_retry(
                        "chat_with_tools",
                        lambda usage_callback: call_with_optional_usage_callback(
                            client.chat_with_tools,
                            current_messages,
                            required_keywords=(
                                "reasoning_effort_override",
                                *(
                                    ("max_tokens_override",)
                                    if request_max_tokens_override is not None
                                    else ()
                                ),
                            ),
                            tools=tools_list,
                            temperature_override=effective_temperature_override,
                            **(
                                {
                                    "max_tokens_override": (
                                        request_max_tokens_override
                                    )
                                }
                                if request_max_tokens_override is not None
                                else {}
                            ),
                            reasoning_effort_override=(
                                mini_visible_output_reasoning_effort(
                                    client,
                                    default=MINI_TOOL_REASONING_EFFORT,
                                )
                            ),
                            usage_callback=usage_callback,
                        ),
                        messages_for_record=current_messages,
                        tools_for_cost=tools_list,
                        max_tokens_override=request_max_tokens_override,
                    )
                    raw_tool_response = getattr(
                        client, "last_raw_response_data", {}
                    )
                    response_data = (
                        dict(raw_tool_response)
                        if isinstance(raw_tool_response, dict)
                        else None
                    )
                elif use_tools and tools_list:
                    finalizer_max_tokens = mini_model_output_capacity(client)
                    if should_use_raw_final_no_tools(client):
                        _increment_dossier_tool_metric(DEEPSEEK_FINAL_RAW_NO_TOOLS_METRIC)
                        raw_final_messages = toolless_final_messages(current_messages)
                        content, response_data = await _invoke_llm_with_retry(
                            "chat_raw",
                            lambda usage_callback: call_with_optional_usage_callback(
                                client.chat_raw,
                                raw_final_messages,
                                required_keywords=(
                                    "max_tokens_override",
                                    "reasoning_effort_override",
                                ),
                                temperature_override=effective_temperature_override,
                                max_tokens_override=finalizer_max_tokens,
                                reasoning_effort_override=(
                                    mini_bounded_visible_output_reasoning_effort(
                                        client,
                                        effort="low",
                                    )
                                ),
                                usage_callback=usage_callback,
                            ),
                            messages_for_record=raw_final_messages,
                            max_tokens_override=finalizer_max_tokens,
                        )
                    else:
                        content, _ignored_tool_calls = await _invoke_llm_with_retry(
                            "chat_with_tools",
                            lambda usage_callback: call_with_optional_usage_callback(
                                client.chat_with_tools,
                                current_messages,
                                required_keywords=(
                                    "max_tokens_override",
                                    "reasoning_effort_override",
                                ),
                                tools=tools_list,
                                tool_choice="none",
                                temperature_override=effective_temperature_override,
                                max_tokens_override=finalizer_max_tokens,
                                reasoning_effort_override=(
                                    mini_bounded_visible_output_reasoning_effort(
                                        client,
                                        effort="low",
                                    )
                                ),
                                usage_callback=usage_callback,
                            ),
                            messages_for_record=current_messages,
                            tools_for_cost=tools_list,
                            max_tokens_override=finalizer_max_tokens,
                        )
                        raw_final_response = getattr(
                            client, "last_raw_response_data", {}
                        )
                        response_data = (
                            dict(raw_final_response)
                            if isinstance(raw_final_response, dict)
                            else None
                        )
                    tool_calls = []
                else:
                    content, response_data = await _invoke_llm_with_retry(
                        "chat_raw",
                        lambda usage_callback: call_with_optional_usage_callback(
                            client.chat_raw,
                            current_messages,
                            required_keywords=(
                                *(
                                    ("reasoning_effort_override",)
                                    if raw_visible_reasoning_effort
                                    else ()
                                ),
                                *(
                                    ("max_tokens_override",)
                                    if request_max_tokens_override is not None
                                    else ()
                                ),
                            ),
                            **(
                                {
                                    "max_tokens_override": (
                                        request_max_tokens_override
                                    )
                                }
                                if request_max_tokens_override is not None
                                else {}
                            ),
                            **(
                                {
                                    "reasoning_effort_override":
                                    raw_visible_reasoning_effort
                                }
                                if raw_visible_reasoning_effort
                                else {}
                            ),
                            temperature_override=effective_temperature_override,
                            usage_callback=usage_callback,
                        ),
                        messages_for_record=current_messages,
                        max_tokens_override=request_max_tokens_override,
                    )
                    tool_calls = []
                if (
                    can_call_tools
                    and not tool_calls
                    and use_tools
                    and tools_list
                    and is_deepseek_client(client)
                ):
                    simple_xml_calls = extract_simple_xml_tool_calls(
                        content,
                        allowed_tool_names=tuple(
                            str((item.get("function") or {}).get("name", "") or "")
                            for item in tools_list
                            if isinstance(item, dict)
                        ),
                    )
                    if simple_xml_calls:
                        tool_calls = simple_xml_calls
                        _increment_dossier_tool_metric(
                            DEEPSEEK_TEXT_CONTENT_TOOL_CALL_METRIC,
                            1,
                        )
                        provider_protocol_event = (
                            "deepseek_simple_xml_tool_call_normalized"
                        )
                        provider_protocol_original_content = str(content or "")
                if not tool_calls:
                    # Providers may finish without calling a tool before the
                    # tool budget is exhausted. Resolve every such response at
                    # the same final-output boundary so an empty/truncated
                    # reasoning-only completion cannot look successful.
                    final_resolution = resolve_final_no_tools_output(
                        content=content,
                        raw_response=response_data,
                        client=client,
                        accepted_proof_codes=repair_self_check_codes,
                    )
                    content = final_resolution.content
                    if final_resolution.event:
                        provider_protocol_event = final_resolution.event
                        if final_resolution.metric_key:
                            _increment_dossier_tool_metric(
                                final_resolution.metric_key
                            )
                        _trace(
                            trace_prefix,
                            "  no-tool output resolved: "
                            f"{final_resolution.event}",
                        )
                    if final_resolution.error:
                        if (
                            can_call_tools
                            and use_tools
                            and tools_list
                            and not final_no_tools_recovery_attempted
                        ):
                            final_no_tools_recovery_attempted = True
                            force_finalize_without_tools = True
                            provider_protocol_event = ""
                            content = ""
                            _trace(
                                trace_prefix,
                                "  retrying no-tool output once with bounded "
                                "visible-output reasoning",
                            )
                            continue
                        llm_error = final_resolution.error
                        break
                    if (
                        use_tools
                        and tools_list
                        and should_use_raw_final_no_tools(client)
                    ):
                        handling = handle_deepseek_dsml_after_budget(
                            client=client,
                            content=str(content or ""),
                            already_reprompted=deepseek_dsml_reprompted_after_budget,
                        )
                        banked_final_override = False
                        if handling.changed and repair_self_check_codes:
                            banked_resolution = resolve_final_no_tools_output(
                                content="",
                                raw_response=response_data,
                                client=client,
                                accepted_proof_codes=repair_self_check_codes,
                            )
                            if banked_resolution.used_accepted_proof:
                                content = banked_resolution.content
                                provider_protocol_event = banked_resolution.event
                                if banked_resolution.metric_key:
                                    _increment_dossier_tool_metric(
                                        banked_resolution.metric_key
                                    )
                                banked_final_override = True
                                _trace(
                                    trace_prefix,
                                    "  final no-tools pseudo-tool output replaced "
                                    "with current-turn Lean-accepted proof",
                                )
                        if handling.changed and not banked_final_override:
                            _increment_dossier_tool_metric(
                                handling.content_metric_key
                                or DEEPSEEK_DSML_CONTENT_TOOL_CALL_METRIC
                            )
                            if handling.metric_key:
                                _increment_dossier_tool_metric(handling.metric_key)
                            provider_protocol_event = handling.event
                            provider_protocol_original_content = handling.original_content
                            content = handling.content
                            _trace(
                                trace_prefix,
                                "  DeepSeek final tool content handled: "
                                f"{handling.event}",
                            )
                            if handling.should_reprompt:
                                # Bootstrap before the direct append so an
                                # empty history keeps the problem statement
                                # visible to later LLM calls.
                                conv.ensure_bootstrap()
                                conv.history.append(
                                    {"role": "user", "content": handling.feedback}
                                )
                                deepseek_dsml_reprompted_after_budget = True
                                content = ""
                                continue
                            if handling.event.endswith("_repeated"):
                                llm_error = "deepseek_tool_after_budget"
                                content = ""
                                break
                    forbidden_final_command = (
                        _find_forbidden_lean_command([], str(content or ""))
                        if use_tools and tools_list and is_deepseek_client(client)
                        else None
                    )
                    if forbidden_final_command is not None:
                        if not final_no_tools_policy_reprompted:
                            conv.ensure_bootstrap()
                            conv.history.append(
                                {
                                    "role": "user",
                                    "content": (
                                        "The previous final response used a top-level "
                                        f"Lean `{forbidden_final_command}` command, which "
                                        "is not an executable proof body. Do not inspect "
                                        "the environment or leave placeholders. Submit "
                                        "one fenced Lean proof block for the active goal."
                                    ),
                                }
                            )
                            final_no_tools_policy_reprompted = True
                            provider_protocol_event = (
                                "final_no_tools_policy_recovery_pending"
                            )
                            content = ""
                            continue
                        llm_error = "final_no_tools_forbidden_command"
                        provider_protocol_event = llm_error
                        content = ""
                        break
                    if (
                        repair_self_check_required
                        and not repair_self_check_seen
                        and not _repair_self_check_non_verdict_is_compliant(
                            repair_self_check_status
                        )
                    ):
                        helper_only_decomposition = False
                        try:
                            theorem_name = str(
                                getattr(dossier, "theorem_name", "")
                                if dossier is not None
                                else ""
                            )
                            helper_only_decomposition = (
                                _repair_content_is_helper_only_decomposition(
                                    content,
                                    theorem_name=theorem_name,
                                )
                            )
                        except Exception:
                            helper_only_decomposition = False
                        if helper_only_decomposition:
                            repair_self_check_helper_only_allowed = True
                            repair_self_check_status = "helper_only_decomposition"
                            break
                        if (
                            not repair_self_check_attempted
                            and not repair_self_check_reminder_sent
                            and can_call_tools
                        ):
                            conv.append_user(
                                _repair_self_check_required_message(
                                    require_try_lean=effective_try_lean_tool_enabled,
                                    role=str(getattr(conv, "role", "") or "prove"),
                                ),
                                repair_semantics=_REPAIR_FEEDBACK,
                            )
                            repair_self_check_reminder_sent = True
                            content = ""
                            continue
                        status = _set_repair_self_check_gap(
                            budget_exhausted=not can_call_tools
                        )
                        llm_error = _repair_self_check_gap_error(status) or llm_error
                    if not final_resolution.event:
                        if final_no_tools_policy_reprompted:
                            provider_protocol_event = (
                                "final_no_tools_policy_recovery_succeeded"
                            )
                        elif deepseek_dsml_reprompted_after_budget:
                            provider_protocol_event = (
                                "final_no_tools_protocol_recovery_succeeded"
                            )
                        elif final_no_tools_recovery_attempted:
                            provider_protocol_event = (
                                "final_no_tools_visibility_recovery_succeeded"
                            )
                    break

                # Per-call budget enforcement. If the model returns a batch
                # whose size would push us over the cap, run only as many as
                # the remaining budget allows and drop the rest. We append
                # only the *executed* calls to the assistant turn so OpenAI's
                # API never sees orphan tool_call ids without matching tool
                # results.
                # On repair turns the selector may intentionally run zero
                # non-self-check calls, preserving the final tool slot for
                # the mandatory try_lean call instead of exhausting the turn.
                budget_remaining = max(
                    0, max_tool_calls_per_turn - tool_calls_used
                )
                (
                    calls_to_run,
                    dropped,
                    reserved_for_try_lean,
                ) = _select_tool_calls_for_repair_budget(
                    tool_calls,
                    budget_remaining,
                    repair_self_check_required=repair_self_check_required,
                    repair_self_check_seen=repair_self_check_seen,
                    repair_self_check_attempted=repair_self_check_attempted,
                )

                if (
                    reserved_for_try_lean
                    and not calls_to_run
                    and not repair_self_check_attempted
                ):
                    conv.ensure_bootstrap()
                    if not repair_self_check_reminder_sent:
                        conv.history.append(
                            {
                                "role": "user",
                                "content": _repair_self_check_required_message(
                                    require_try_lean=effective_try_lean_tool_enabled,
                                    role=str(getattr(conv, "role", "") or "prove"),
                                ),
                            }
                        )
                        repair_self_check_reminder_sent = True
                        content = ""
                        _trace(
                            trace_prefix,
                            "  reserved final repair tool slot for try_lean; "
                            "dropped non-self-check tool call(s)",
                        )
                        continue
                    _set_repair_self_check_gap()
                    llm_error = "repair_self_check_no_try_lean_call"
                    break

                conv.ensure_bootstrap()

                # Append the assistant's tool-call message containing only the
                # calls we'll actually execute (so every tool_call has a
                # matching tool message that follows).
                assistant_tool_content = (
                    ""
                    if repair_self_check_required
                    and not repair_self_check_attempted
                    and not repair_self_check_seen
                    else content or ""
                )
                redact_solution_refs = _conversation_should_redact_solution_refs(conv)
                used_tool_call_ids: set[str] = set()
                safe_tool_call_ids: List[str] = []

                def prompt_safe_tool_args_record(
                    value: Any,
                    parse_error: str = "",
                ) -> Dict[str, Any]:
                    def sanitize_record(item: Any) -> Any:
                        if isinstance(item, str):
                            return _prompt_safe_inline_text(
                                item,
                                limit=1200,
                                redact_solution_refs=redact_solution_refs,
                            )
                        if isinstance(item, list):
                            return [sanitize_record(child) for child in item[:20]]
                        if isinstance(item, dict):
                            return {
                                _prompt_safe_inline_text(
                                    str(key),
                                    limit=120,
                                    redact_solution_refs=redact_solution_refs,
                                ): sanitize_record(child)
                                for key, child in list(item.items())[:40]
                            }
                        return item

                    if parse_error:
                        return {}
                    try:
                        payload = json.loads(
                            _prompt_safe_tool_arguments(
                                value,
                                redact_solution_refs=redact_solution_refs,
                            )
                        )
                    except Exception:
                        return {}
                    return sanitize_record(payload) if isinstance(payload, dict) else {}

                def unique_tool_call_id(tc: Mapping[str, Any], index: int) -> str:
                    raw_id = tc.get("id", "") if isinstance(tc, Mapping) else ""
                    base = str(
                        _prompt_safe_tool_call_token(
                            raw_id,
                            redact_solution_refs=redact_solution_refs,
                        )
                    ).strip()
                    if not base:
                        base = f"call_{turn}_{tool_calls_used + index + 1}"
                    candidate = base
                    suffix = 2
                    while candidate in used_tool_call_ids:
                        candidate = f"{base}_{suffix}"
                        suffix += 1
                    used_tool_call_ids.add(candidate)
                    safe_tool_call_ids.append(candidate)
                    return candidate

                assistant_message = {
                    "role": "assistant",
                    "content": assistant_tool_content,
                    "tool_calls": [
                            {
                                "id": str(
                                    unique_tool_call_id(tc, index)
                                ),
                                "type": "function",
                                "function": {
                                    "name": str(
                                        _prompt_safe_tool_name_token(
                                            (tc.get("function") or {}).get(
                                                "name", ""
                                            )
                                            or "",
                                            redact_solution_refs=redact_solution_refs,
                                        )
                                    ),
                                    "arguments": str(
                                        _prompt_safe_tool_arguments(
                                            (tc.get("function") or {}).get(
                                                "arguments", None
                                            ),
                                            redact_solution_refs=redact_solution_refs,
                                        )
                                    ),
                                },
                            }
                            for index, tc in enumerate(calls_to_run)
                    ],
                }
                reasoning_content = response_reasoning_text(response_data)
                if reasoning_content:
                    assistant_message["reasoning_content"] = reasoning_content
                reasoning_items = response_reasoning_items(response_data)
                if reasoning_items:
                    assistant_message["_responses_reasoning_items"] = reasoning_items
                output_items = response_output_items(response_data)
                if output_items and _responses_output_matches_advertised_tool_calls(
                    output_items,
                    assistant_message["tool_calls"],
                ):
                    assistant_message["_responses_output_items"] = output_items
                _bind_provider_continuation_policy_receipt(assistant_message, conv)
                conv.history.append(assistant_message)
                # Execute each retained call and append the tool result.
                # B1 fix (2026-05-08): each per-tc dispatch is wrapped in
                # its own try/except so a runner exception cannot leave an
                # ``assistant`` tool-calls message without a matching
                # ``tool`` message for every advertised tool_call_id. The
                # OpenAI API rejects orphan tool_call_ids on subsequent
                # calls (HTTP 400), so a refiner that inherits this
                # conversation would fail before doing any useful work.
                for index, tc in enumerate(calls_to_run):
                    fn = tc.get("function") or {}
                    name = str(fn.get("name", "") or "")
                    safe_log_name = _prompt_safe_tool_name_token(
                        name,
                        redact_solution_refs=redact_solution_refs,
                    )
                    safe_tcid = safe_tool_call_ids[index]
                    raw_arg_value = fn.get("arguments", None) if "arguments" in fn else None
                    raw_args = "" if raw_arg_value is None else str(raw_arg_value)
                    args, args_parse_error = parse_tool_arguments(raw_arg_value)
                    compute_runner_invoked = False
                    runner_raised = False
                    try:
                        if args_parse_error:
                            if name == "try_lean" and effective_try_lean_tool_enabled:
                                _set_repair_self_check_non_verdict_status(
                                    "try_lean_malformed_arguments"
                                )
                            result_text = (
                                f"{_prompt_safe_tool_name_token(name, redact_solution_refs=redact_solution_refs)} "
                                "error: malformed JSON arguments; pass a JSON object "
                                "matching the tool schema. Parse error: "
                                f"{args_parse_error}"
                            )
                        elif name == "search_mathlib" and searcher is not None:
                            result_text = _run_search_tool(
                                searcher,
                                args,
                                known_decl_names=getattr(conv, "known_premise_names", []),
                                local_decl_names=_local_decl_names_for_search(
                                    dossier,
                                    conv,
                                ),
                                metric_sink=(
                                    getattr(dossier, "tool_metrics", None)
                                    if dossier is not None
                                    else None
                                ),
                            )
                        elif name == "search_theorems" and isinstance(
                            searcher, MathematicalRetrievalService
                        ):
                            from .mathematical_retrieval.async_runtime import (
                                RetrievalWorkerCapacityError,
                                run_sync_abandonment_safe,
                            )

                            accepted_result_out: Dict[str, Any] = {}
                            try:
                                result_text = await run_sync_abandonment_safe(
                                    lambda: _run_search_theorems_tool(
                                        searcher,
                                        args,
                                        accepted_result_out=accepted_result_out,
                                        goal_state=_active_root_tool_goal_statement(
                                            dossier,
                                            conv,
                                        ),
                                    ),
                                    timeout_s=float(
                                        getattr(
                                            searcher,
                                            "operation_timeout_s",
                                            30.0,
                                        )
                                        or 30.0
                                    ),
                                )
                            except (
                                TimeoutError,
                                RetrievalWorkerCapacityError,
                            ) as exc:
                                publish_failure = getattr(
                                    searcher,
                                    "publish_boundary_failure",
                                    None,
                                )
                                if callable(publish_failure):
                                    publish_failure(
                                        consumer="reactive",
                                        elapsed_s=float(
                                            getattr(
                                                searcher,
                                                "operation_timeout_s",
                                                30.0,
                                            )
                                            or 30.0
                                        ),
                                        capacity_exhausted=isinstance(
                                            exc,
                                            RetrievalWorkerCapacityError,
                                        ),
                                    )
                                result_text = (
                                    "Federated search unavailable: "
                                    f"{type(exc).__name__}: {exc}"
                                )
                            else:
                                accepted_result = accepted_result_out.get("result")
                                if accepted_result is not None:
                                    searcher.last_result = accepted_result
                                    searcher.publish_result_metrics(
                                        accepted_result,
                                        consumer="reactive",
                                    )
                        elif name == "check_lean" and lean_check_tool_enabled:
                            context_lemmas = (
                                _feedback_lemmas_for_answer_safe_recheck(
                                    _current_verified_helper_blocks(),
                                    conv,
                                )
                                if dossier is not None
                                else []
                            )
                            result_text = await _run_check_lean_tool(
                                lean,
                                preamble=conv.preamble,
                                context_lemmas=context_lemmas,
                                args=args,
                                redact_solution_refs=redact_solution_refs,
                            )
                        elif name == "try_lean" and effective_try_lean_tool_enabled:
                            context_lemmas = (
                                _feedback_lemmas_for_answer_safe_recheck(
                                    _current_verified_helper_blocks(),
                                    conv,
                                )
                                if dossier is not None
                                else []
                            )
                            result_text = await run_try_lean_tool(
                                lean,
                                goal_statement=(
                                    _active_root_tool_goal_statement(
                                        dossier,
                                        conv=conv,
                                        helper_blocks=(
                                            _current_active_root_frame_helper_blocks()
                                            if dossier is not None
                                            else []
                                        ),
                                    )
                                    or conv.goal_statement
                                ),
                                preamble=conv.preamble,
                                args=args,
                                context_lemmas=context_lemmas,
                                dossier=dossier,
                                turn_index=turn,
                                tool_call_index=tool_calls_used + 1,
                                redact_solution_refs=redact_solution_refs,
                            )
                            if result_text.startswith("try_lean accepted."):
                                repair_self_check_attempted = True
                                repair_self_check_seen = True
                                repair_self_check_status = "accepted"
                                repair_self_check_codes.append(
                                    str(args.get("code", "") or "")
                                )
                            elif result_text.startswith("try_lean rejected."):
                                repair_self_check_attempted = True
                                repair_self_check_status = "no_accepted_try_lean"
                            elif result_text.startswith("try_lean infrastructure error:"):
                                _set_repair_self_check_non_verdict_status(
                                    "try_lean_infrastructure_error"
                                )
                            elif result_text.startswith(
                                (
                                    "try_lean error:",
                                    "try_lean rejected by preflight:",
                                )
                            ):
                                _set_repair_self_check_non_verdict_status(
                                    "try_lean_preflight_error"
                                )
                        elif (
                            name == "certify_counterexample"
                            and effective_try_lean_tool_enabled
                        ):
                            authoritative_context_lemmas = (
                                _current_verified_helper_blocks()
                                if dossier is not None
                                else []
                            )
                            feedback_context_lemmas = (
                                _feedback_lemmas_for_answer_safe_recheck(
                                    authoritative_context_lemmas,
                                    conv,
                                )
                                if dossier is not None
                                else []
                            )
                            result_text = await run_certify_counterexample_tool(
                                lean,
                                goal_statement=(
                                    _active_root_tool_goal_statement(
                                        dossier,
                                        conv=conv,
                                        helper_blocks=(
                                            _current_active_root_frame_helper_blocks()
                                            if dossier is not None
                                            else []
                                        ),
                                    )
                                    or conv.goal_statement
                                ),
                                preamble=_proof_state_acceptance_preamble(conv),
                                feedback_preamble=str(
                                    getattr(conv, "preamble", "") or ""
                                ),
                                args=args,
                                context_lemmas=authoritative_context_lemmas,
                                feedback_context_lemmas=feedback_context_lemmas,
                                dossier=dossier,
                                proof_state=proof_state,
                            )
                        elif (
                            name == "compute_examples"
                            and compute_examples_tool_enabled
                        ):
                            compute_runner_invoked = True
                            result_text = await run_compute_examples_tool(
                                lean,
                                preamble=conv.preamble,
                                args=args,
                                dossier=dossier,
                                redact_solution_refs=redact_solution_refs,
                            )
                        elif name == "apply_decl_to_goal" and apply_decl_to_goal_tool_enabled:
                            # Probe against the LLM-facing axiom preamble, NOT
                            # any filled checker preamble. Probing a filled
                            # value would surface hidden answer information to
                            # the LLM via three distinct paths:
                            #   1. ``remaining_goals`` — Lean reduces _solution
                            #      to True/False, so any goal still mentioning
                            #      _solution after the proof_stub renders the
                            #      reduced form.
                            #   2. ``error`` text — Lean error messages echo
                            #      reduced expressions (e.g. "expected 1 ∈ True").
                            #   3. Bisection oracle — the LLM controls both
                            #      ``statement`` and ``decl_name``, so it can
                            #      probe ``apply_decl_to_goal(statement="...x_solution",
                            #      decl_name="True.intro")`` and recover the
                            #      hidden boolean from a single yes/no
                            #      response. Against axiom view, ``True.intro``
                            #      cannot unify with the opaque ``_solution``.
                            # Cost: value-specific lemmas (e.g. iff_true_intro)
                            # falsely report inapplicable. Acceptable — those
                            # are the rubber-stamping moves we want the model
                            # to derive mathematically, not get for free.
                            context_lemmas = (
                                _feedback_lemmas_for_answer_safe_recheck(
                                    _current_verified_helper_blocks(),
                                    conv,
                                )
                                if dossier is not None
                                else []
                            )
                            result_text = await _run_apply_decl_to_goal_tool(
                                lean,
                                preamble=conv.preamble,
                                context_lemmas=context_lemmas,
                                args=args,
                                conv=conv,
                                dossier=dossier,
                                proof_state=proof_state,
                                proof_cache=proof_cache,
                                turn_index=turn,
                                tool_call_index=tool_calls_used + 1,
                                max_residual_goals=max(
                                    0,
                                    int(proof_state_child_goal_limit or 0),
                                ),
                                goal_statement_override=(
                                    _active_root_tool_goal_statement(
                                        dossier,
                                        conv=conv,
                                        helper_blocks=(
                                            _current_active_root_frame_helper_blocks()
                                            if dossier is not None
                                            else []
                                        ),
                                    )
                                    or conv.goal_statement
                                ),
                                redact_solution_refs=redact_solution_refs,
                            )
                        else:
                            safe_tool_name = _prompt_safe_tool_name_token(
                                name,
                                redact_solution_refs=redact_solution_refs,
                            )
                            result_text = (
                                "Unknown tool: "
                                f"{safe_tool_name}"
                            )
                    except asyncio.CancelledError as cancellation:
                        result_text = (
                            f"{safe_log_name} cancelled: tool runner cancelled "
                            "before this advertised tool call completed."
                        )
                        conv.history.append(
                            {
                                "role": "tool",
                                "tool_call_id": safe_tcid,
                                "content": result_text,
                            }
                        )
                        cancelled_record = {
                                "name": safe_log_name,
                                "tool_call_id": safe_tcid,
                                "args": prompt_safe_tool_args_record(
                                    raw_arg_value,
                                    args_parse_error,
                                ),
                                "result_preview": result_text[:400],
                                "protocol_attempted": True,
                                "json_parsed": not bool(args_parse_error),
                                "raw_arguments_length": len(raw_args),
                                "raw_arguments_sha256": hashlib.sha256(
                                    raw_args.encode("utf-8", errors="replace")
                                ).hexdigest(),
                                "result_length": len(result_text),
                                "result_sha256": hashlib.sha256(
                                    result_text.encode("utf-8", errors="replace")
                                ).hexdigest(),
                            }
                        if name == "compute_examples":
                            cancelled_record.update(
                                runner_invoked=bool(compute_runner_invoked),
                                execution_status=(
                                    "runner_cancelled"
                                    if compute_runner_invoked
                                    else "not_dispatched"
                                ),
                            )
                            if compute_runner_invoked:
                                cancelled_record["error_reason"] = (
                                    "tool_loop_cancelled"
                                )
                            else:
                                cancelled_record["skipped_reason"] = (
                                    "tool_loop_cancelled"
                                )
                        else:
                            cancelled_record["skipped_reason"] = "tool_loop_cancelled"
                        tool_call_log.append(cancelled_record)
                        for remaining_index, remaining_tc in enumerate(
                            calls_to_run[index + 1 :],
                            start=index + 1,
                        ):
                            remaining_fn = remaining_tc.get("function") or {}
                            remaining_name = str(
                                remaining_fn.get("name", "") or ""
                            )
                            remaining_tcid = safe_tool_call_ids[remaining_index]
                            remaining_safe_name = _prompt_safe_tool_name_token(
                                remaining_name,
                                redact_solution_refs=redact_solution_refs,
                            )
                            remaining_text = (
                                f"{remaining_safe_name} skipped: tool loop "
                                "cancelled before this advertised tool call "
                                "could run."
                            )
                            conv.history.append(
                                {
                                    "role": "tool",
                                    "tool_call_id": remaining_tcid,
                                    "content": remaining_text,
                                }
                            )
                            remaining_raw_value = (
                                remaining_fn.get("arguments", None)
                                if "arguments" in remaining_fn
                                else None
                            )
                            remaining_raw = (
                                ""
                                if remaining_raw_value is None
                                else str(remaining_raw_value)
                            )
                            remaining_record = {
                                    "name": remaining_safe_name,
                                    "tool_call_id": remaining_tcid,
                                    "args": {},
                                    "result_preview": remaining_text[:400],
                                    "skipped_reason": "tool_loop_cancelled",
                                    "protocol_attempted": False,
                                    "json_parsed": False,
                                    "raw_arguments_length": len(remaining_raw),
                                    "raw_arguments_sha256": hashlib.sha256(
                                        remaining_raw.encode("utf-8", errors="replace")
                                    ).hexdigest(),
                                    "result_length": len(remaining_text),
                                    "result_sha256": hashlib.sha256(
                                        remaining_text.encode("utf-8", errors="replace")
                                    ).hexdigest(),
                                }
                            if remaining_name == "compute_examples":
                                remaining_record.update(
                                    runner_invoked=False,
                                    execution_status="not_dispatched",
                                )
                            tool_call_log.append(remaining_record)
                        if recorder is not None:
                            try:
                                recorder.record_turn({
                                    "phase": conv.role,
                                    "turn_in_phase": turn,
                                    "model": model_id,
                                    "tool_calls_used": tool_calls_used,
                                    "tool_call_log": [
                                        dict(item) for item in tool_call_log
                                    ],
                                    "verdict": "llm_response_cancelled",
                                    "llm_recovery_event_id": (
                                        "cancelled-tool-receipt-v1:"
                                        + uuid.uuid4().hex
                                    ),
                                })
                            except Exception as receipt_error:
                                cancellation.add_note(
                                    "failed to persist cancelled tool receipts: "
                                    f"{type(receipt_error).__name__}: {receipt_error}"
                                )
                        raise
                    except Exception as exc:
                        runner_raised = True
                        # Synthesize a tool error message so the
                        # tool_call_id is matched. Without this, conv.history
                        # ends up with an ``assistant`` tool-calls message
                        # whose tool_call_ids have no matching ``tool``
                        # messages, and a downstream refiner re-sending
                        # this transcript hits an OpenAI 400.
                        safe_exc = _prompt_safe_inline_text(
                            exc,
                            limit=500,
                            redact_solution_refs=redact_solution_refs,
                        )
                        safe_exc_type = _prompt_safe_inline_text(
                            type(exc).__name__,
                            limit=120,
                            redact_solution_refs=redact_solution_refs,
                        )
                        result_text = (
                            f"Tool runner error ({safe_exc_type}): "
                            f"{safe_exc}"
                        )
                        _trace(
                            trace_prefix,
                            f"  {safe_log_name}(?) crashed: "
                            f"{safe_exc_type}: {safe_exc} "
                            "(synthesized tool error message to keep transcript well-formed)",
                        )
                    conv.history.append(
                        {
                            "role": "tool",
                            "tool_call_id": safe_tcid,
                            "content": result_text,
                        }
                    )
                    tool_calls_used += 1
                    if args_parse_error:
                        log_query = (
                            "<malformed args: "
                            f"{_prompt_safe_tool_arguments(raw_args, redact_solution_refs=redact_solution_refs).replace(chr(10), ' ')}"
                            ">"
                        )[:160]
                    else:
                        if name == "compute_examples":
                            queries = args.get("queries")
                            query_count = len(queries) if isinstance(queries, list) else 0
                            mode = str(args.get("mode", "") or "").strip()
                            purpose = str(args.get("purpose", "") or "").strip()
                            legacy_query = str(args.get("query", "") or "").strip()
                            raw_log_query = ", ".join(
                                item
                                for item in (
                                    f"queries={query_count}",
                                    f"mode={mode}" if mode else "",
                                    f"purpose={purpose}" if purpose else "",
                                    f"query={legacy_query}" if legacy_query else "",
                                )
                                if item
                            )
                        else:
                            raw_log_query = (
                                str(args.get("query", "") or "")
                                or str(args.get("term", "") or "")
                                or str(args.get("name", "") or "")
                                or str(args.get("code", "") or "").replace("\n", " ")
                            )
                        query_renderer = (
                            _prompt_safe_natural_language_text
                            if name in {"search_mathlib", "search_theorems"}
                            else _prompt_safe_inline_text
                        )
                        log_query = query_renderer(
                            raw_log_query,
                            limit=160,
                            redact_solution_refs=redact_solution_refs,
                        )
                    if args_parse_error:
                        _trace(
                            trace_prefix,
                            f"  {safe_log_name} malformed arguments; tool was not executed",
                        )
                    else:
                        log_count = display_line_count(result_text)
                        _trace(
                            trace_prefix,
                            f"  {safe_log_name}({log_query!r}) → {log_count} line(s)",
                        )
                    tool_call_record = {
                        "name": safe_log_name,
                        "tool_call_id": safe_tcid,
                        "args": prompt_safe_tool_args_record(
                            raw_arg_value,
                            args_parse_error,
                        ),
                        "result_preview": result_text[:400],
                        "protocol_attempted": True,
                        "json_parsed": not bool(args_parse_error),
                        "raw_arguments_length": len(raw_args),
                        "raw_arguments_sha256": hashlib.sha256(
                            raw_args.encode("utf-8", errors="replace")
                        ).hexdigest(),
                        "result_length": len(result_text),
                        "result_sha256": hashlib.sha256(
                            result_text.encode("utf-8", errors="replace")
                        ).hexdigest(),
                    }
                    if name == "compute_examples":
                        tool_call_record["runner_invoked"] = bool(
                            compute_runner_invoked
                        )
                        tool_call_record["execution_status"] = (
                            "protocol_rejected"
                            if args_parse_error
                            else "runner_error"
                            if compute_runner_invoked and runner_raised
                            else "runner_completed"
                            if compute_runner_invoked
                            else "not_dispatched"
                        )
                    if args_parse_error:
                        tool_call_record["args_parse_error"] = args_parse_error
                        tool_call_record["skipped_reason"] = "malformed_arguments"
                        tool_call_record["raw_arguments_preview"] = (
                            _prompt_safe_tool_arguments(
                                raw_args,
                                redact_solution_refs=redact_solution_refs,
                            )[:400]
                        )
                    tool_call_log.append(tool_call_record)

                    counterexample_result = str(result_text or "")
                    if (
                        name == "certify_counterexample"
                        and counterexample_result.startswith(
                            "certify_counterexample infrastructure error:"
                        )
                    ):
                        llm_error = counterexample_result
                        llm_error_classification = LLMErrorClassification(
                            kind=(
                                "certify_counterexample_infrastructure_error"
                            ),
                            retryable=True,
                            terminal=False,
                            # Route this through the existing bounded scoped
                            # infrastructure recovery lane. The precise source
                            # remains available in ``kind`` and the tool receipt.
                            failure_reason="llm_network_error",
                            message=counterexample_result,
                        )
                        for remaining_index, remaining_tc in enumerate(
                            calls_to_run[index + 1 :],
                            start=index + 1,
                        ):
                            remaining_fn = remaining_tc.get("function") or {}
                            remaining_name = str(
                                remaining_fn.get("name", "") or ""
                            )
                            remaining_tcid = safe_tool_call_ids[remaining_index]
                            remaining_safe_name = _prompt_safe_tool_name_token(
                                remaining_name,
                                redact_solution_refs=redact_solution_refs,
                            )
                            remaining_text = (
                                f"{remaining_safe_name} skipped: counterexample "
                                "certification infrastructure failure requires "
                                "scheduler retry."
                            )
                            conv.history.append({
                                "role": "tool",
                                "tool_call_id": remaining_tcid,
                                "content": remaining_text,
                            })
                            remaining_raw_value = (
                                remaining_fn.get("arguments", None)
                                if "arguments" in remaining_fn
                                else None
                            )
                            remaining_raw = (
                                ""
                                if remaining_raw_value is None
                                else str(remaining_raw_value)
                            )
                            remaining_record = {
                                "name": remaining_safe_name,
                                "tool_call_id": remaining_tcid,
                                "args": {},
                                "result_preview": remaining_text[:400],
                                "skipped_reason": (
                                    "certify_counterexample_infrastructure_error"
                                ),
                                "protocol_attempted": False,
                                "json_parsed": False,
                                "raw_arguments_length": len(remaining_raw),
                                "raw_arguments_sha256": hashlib.sha256(
                                    remaining_raw.encode(
                                        "utf-8",
                                        errors="replace",
                                    )
                                ).hexdigest(),
                                "result_length": len(remaining_text),
                                "result_sha256": hashlib.sha256(
                                    remaining_text.encode(
                                        "utf-8",
                                        errors="replace",
                                    )
                                ).hexdigest(),
                            }
                            if remaining_name == "compute_examples":
                                remaining_record.update(
                                    runner_invoked=False,
                                    execution_status="not_dispatched",
                                )
                            tool_call_log.append(remaining_record)
                        break
                    if name == "certify_counterexample" and counterexample_result.startswith(
                        (
                            "certify_counterexample accepted.",
                            "certify_counterexample conflict.",
                        )
                    ):
                        proof_disproof_conflict = counterexample_result.startswith(
                            "certify_counterexample conflict."
                        )
                        authoritative_falsification = not proof_disproof_conflict
                        repair_self_check_attempted = True
                        repair_self_check_seen = not proof_disproof_conflict
                        repair_self_check_status = (
                            "proof_disproof_conflict"
                            if proof_disproof_conflict
                            else "accepted_counterexample"
                        )
                        repair_self_check_codes.append(
                            str(args.get("code", "") or "")
                        )
                        for remaining_index, remaining_tc in enumerate(
                            calls_to_run[index + 1 :],
                            start=index + 1,
                        ):
                            remaining_fn = remaining_tc.get("function") or {}
                            remaining_name = str(
                                remaining_fn.get("name", "") or ""
                            )
                            remaining_tcid = safe_tool_call_ids[remaining_index]
                            remaining_safe_name = _prompt_safe_tool_name_token(
                                remaining_name,
                                redact_solution_refs=redact_solution_refs,
                            )
                            remaining_text = (
                                f"{remaining_safe_name} skipped: proof/disproof "
                                "trust boundary conflict is terminal."
                                if proof_disproof_conflict
                                else f"{remaining_safe_name} skipped: active "
                                "target already authoritatively refuted."
                            )
                            conv.history.append({
                                "role": "tool",
                                "tool_call_id": remaining_tcid,
                                "content": remaining_text,
                            })
                            remaining_raw_value = (
                                remaining_fn.get("arguments", None)
                                if "arguments" in remaining_fn
                                else None
                            )
                            remaining_raw = (
                                ""
                                if remaining_raw_value is None
                                else str(remaining_raw_value)
                            )
                            remaining_record = {
                                "name": remaining_safe_name,
                                "tool_call_id": remaining_tcid,
                                "args": {},
                                "result_preview": remaining_text[:400],
                                "skipped_reason": (
                                    "proof_disproof_conflict_terminal"
                                    if proof_disproof_conflict
                                    else "authoritative_counterexample_terminal"
                                ),
                                "protocol_attempted": False,
                                "json_parsed": False,
                                "raw_arguments_length": len(remaining_raw),
                                "raw_arguments_sha256": hashlib.sha256(
                                    remaining_raw.encode(
                                        "utf-8", errors="replace"
                                    )
                                ).hexdigest(),
                                "result_length": len(remaining_text),
                                "result_sha256": hashlib.sha256(
                                    remaining_text.encode(
                                        "utf-8", errors="replace"
                                    )
                                ).hexdigest(),
                            }
                            if remaining_name == "compute_examples":
                                remaining_record.update(
                                    runner_invoked=False,
                                    query_count=0,
                                    result_status="not_dispatched",
                                    execution_status="not_dispatched",
                                )
                            tool_call_log.append(remaining_record)
                        break

                if authoritative_falsification or proof_disproof_conflict:
                    break

                if (
                    llm_error_classification.kind
                    == "certify_counterexample_infrastructure_error"
                ):
                    break

                if (
                    reserved_for_try_lean
                    and repair_self_check_required
                    and not repair_self_check_seen
                    and not repair_self_check_attempted
                    and not _repair_self_check_non_verdict_is_compliant(
                        repair_self_check_status
                    )
                ):
                    conv.append_user(
                        _repair_self_check_required_message(
                            require_try_lean=effective_try_lean_tool_enabled,
                            role=str(getattr(conv, "role", "") or "prove"),
                        ),
                        repair_semantics=_REPAIR_FEEDBACK,
                    )
                    repair_self_check_reminder_sent = True
                    if dropped > 0:
                        _trace(
                            trace_prefix,
                            "  reserved one repair tool slot for try_lean; "
                            f"dropped {dropped} non-self-check call(s)",
                        )
                    continue

                if dropped > 0 or tool_calls_used >= max_tool_calls_per_turn:
                    # Either the model wanted more calls than budget allowed,
                    # or we just ran the last permitted call. On repair
                    # turns, never ask for a final proof after the required
                    # self-check became impossible.
                    if (
                        repair_self_check_required
                        and not repair_self_check_seen
                        and not repair_self_check_attempted
                        and not _repair_self_check_non_verdict_is_compliant(
                            repair_self_check_status
                        )
                    ):
                        status = _set_repair_self_check_gap(budget_exhausted=True)
                        llm_error = _repair_self_check_gap_error(status) or llm_error
                        break
                    msg = (
                        f"Tool budget exhausted "
                        f"({tool_calls_used}/{max_tool_calls_per_turn} calls used"
                        + (
                            f"; {dropped} additional call(s) dropped"
                            if dropped > 0
                            else ""
                        )
                        + "). Use what you have and write the proof now."
                    )
                    conv.append_user(msg, repair_semantics=_REPAIR_CONTINUATION)
                    if dropped > 0:
                        _trace(
                            trace_prefix,
                            f"  budget exhausted mid-batch; dropped {dropped} call(s)",
                        )
                # Loop back. Next iter: if budget reached, chat_raw forces
                # the model to commit to a proof using what it's seen.
        except Exception as exc:
            redact_llm_error_solution_refs = _conversation_should_redact_solution_refs(
                conv
            )
            safe_llm_error = _prompt_safe_inline_text(
                format_exception(exc),
                limit=1000,
                redact_solution_refs=redact_llm_error_solution_refs,
            )
            llm_retry_deadline_record = llm_retry_deadline_record_from_exception(exc)
            llm_error_classification = classify_llm_exception(exc)
            llm_failure_reason = str(
                llm_error_classification.failure_reason or ""
            ).strip()
            llm_error_metadata: List[str] = []
            for label, value in (
                ("kind", getattr(llm_error_classification, "kind", "")),
                ("reason", llm_failure_reason),
            ):
                text = str(value or "").strip()
                if text and text not in safe_llm_error:
                    llm_error_metadata.append(
                        f"{label}="
                        + _prompt_safe_inline_text(
                            text,
                            limit=160,
                            redact_solution_refs=redact_llm_error_solution_refs,
                        )
                    )
            llm_error = (
                f"{safe_llm_error} ({'; '.join(llm_error_metadata)})"
                if llm_error_metadata
                else safe_llm_error
            )
            llm_failure_scope_value = llm_failure_scope(llm_failure_reason)
            if llm_error_classification.terminal or llm_failure_scope_value:
                try:
                    setattr(
                        conv,
                        "_last_llm_failure_reason",
                        llm_failure_reason,
                    )
                    setattr(
                        conv,
                        "_last_llm_failure_kind",
                        llm_error_classification.kind,
                    )
                except Exception:
                    pass
            if llm_error_classification.terminal:
                try:
                    setattr(
                        dossier,
                        "session_failure_reason",
                        llm_failure_reason,
                    )
                    setattr(
                        dossier,
                        "session_failure_kind",
                        llm_error_classification.kind,
                    )
                except Exception:
                    pass
            _trace(trace_prefix, f"  LLM call failed: {llm_error}")
        llm_elapsed = round(time.monotonic() - turn_started, 3)
        if proof_disproof_conflict:
            try:
                setattr(
                    conv,
                    "_last_llm_failure_reason",
                    "falsification_trust_boundary_conflict",
                )
                setattr(conv, "_last_llm_failure_kind", "proof_disproof_conflict")
            except Exception:
                pass
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "llm_elapsed_s": llm_elapsed,
                    "terminal_failure": True,
                    "terminal_failure_reason": (
                        "falsification_trust_boundary_conflict"
                    ),
                    "terminal_failure_kind": "proof_disproof_conflict",
                    "verdict": "counterexample_tool_proof_disproof_conflict",
                })
            return False, None
        if authoritative_falsification:
            try:
                setattr(
                    conv,
                    "_last_llm_failure_reason",
                    "local_root_authoritatively_falsified",
                )
                setattr(conv, "_last_llm_failure_kind", "mathematical_disproof")
            except Exception:
                pass
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "llm_elapsed_s": llm_elapsed,
                    "authoritative_falsification": True,
                    "verdict": "counterexample_tool_authoritatively_falsified",
                })
            return False, None
        repair_self_check_accepted = bool(
            repair_self_check_seen or repair_self_check_codes
        )
        if not repair_self_check_status and repair_self_check_required:
            if repair_self_check_accepted:
                repair_self_check_status = "accepted"
            elif repair_self_check_attempted:
                repair_self_check_status = "no_accepted_try_lean"
            elif repair_self_check_budget_exhausted:
                repair_self_check_status = "tool_budget_exhausted"
            elif repair_self_check_helper_only_allowed:
                repair_self_check_status = "helper_only_decomposition"
            else:
                repair_self_check_status = "no_try_lean_call"
        if (
            llm_error == "repair_self_check_missing"
            and repair_self_check_status == "no_accepted_try_lean"
        ):
            llm_error = None
        repair_self_check_record_fields: Dict[str, Any] = {}
        if repair_self_check_required:
            repair_self_check_record_fields = {
                "repair_self_check_required": True,
                "repair_self_check_attempted": repair_self_check_attempted,
                "repair_self_check_accepted": repair_self_check_accepted,
                "repair_self_check_status": repair_self_check_status,
                "repair_self_check_missing_kind": repair_self_check_status,
                "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                "repair_self_check_helper_only_allowed": (
                    repair_self_check_helper_only_allowed
                ),
            }
        if provider_protocol_event:
            repair_self_check_record_fields.update(
                {
                    "provider_protocol_event": provider_protocol_event,
                    "provider_protocol_original_response": (
                        provider_protocol_original_content
                    ),
                }
            )

        repair_self_check_policy_reasons = {
            "repair_self_check_missing",
            "repair_self_check_no_try_lean_call",
            "repair_self_check_tool_budget_exhausted",
        }
        if llm_error in repair_self_check_policy_reasons:
            # A rejected try_lean attempt or genuine verifier-infrastructure
            # fault proves the model invoked the required tool, but grants no
            # proof authority. The independent final Lean check still decides
            # the candidate. Zero or malformed calls remain policy failures —
            # unless the unchanged submission matches a durably accepted
            # try_lean stub for this exact goal/preamble/context. Re-verifying
            # an identical accepted body is a wasted Lean call, and rejecting it burned
            # the repair continuation on rational behavior).
            durable_submission_evidence = False
            if (
                repair_self_check_status == "no_try_lean_call"
                and dossier is not None
            ):
                try:
                    durable_submission_evidence = (
                        _repair_self_check_durable_submission_evidence(
                            content,
                            dossier=dossier,
                            goal_statement=str(
                                getattr(conv, "goal_statement", "") or ""
                            ),
                            preamble=str(getattr(conv, "preamble", "") or ""),
                            context_lemmas=(
                                _feedback_lemmas_for_answer_safe_recheck(
                                    dossier.verified_helper_blocks(),
                                    conv,
                                )
                            ),
                        )
                    )
                except Exception:
                    durable_submission_evidence = False
                if durable_submission_evidence:
                    # Sol audit 2026-07-29 F3: rewrite the status so a later
                    # GENUINE Lean failure cannot be reclassified from the
                    # stale "no_try_lean_call" back into a policy refusal.
                    # attempted stays False — no tool ran this turn.
                    repair_self_check_status = "accepted_durable"
                    repair_self_check_record_fields.update(
                        {
                            "repair_self_check_status": "accepted_durable",
                            "repair_self_check_missing_kind": "",
                            "repair_self_check_compliant": True,
                            "repair_self_check_evidence_source": (
                                "durable_prior_stub"
                            ),
                        }
                    )
                    _increment_dossier_tool_metric(
                        "mini_repair_self_check_durable_evidence_accepted",
                        1,
                    )
            if (
                repair_self_check_status == "no_accepted_try_lean"
                or _repair_self_check_non_verdict_is_compliant(
                    repair_self_check_status
                )
                or durable_submission_evidence
            ):
                llm_error = None

        if llm_error is not None:
            if (
                not llm_error_classification.terminal
                and llm_error_classification.kind
                != "certify_counterexample_infrastructure_error"
            ):
                llm_error_classification = classify_llm_error_text(llm_error)
            if llm_error in repair_self_check_policy_reasons:
                repair_self_check_missing_kind = (
                    repair_self_check_status or "no_try_lean_call"
                )
                if llm_error == "repair_self_check_tool_budget_exhausted":
                    repair_policy_reason = "repair_self_check_tool_budget_exhausted"
                elif llm_error == "repair_self_check_no_try_lean_call":
                    repair_policy_reason = "repair_self_check_no_try_lean_call"
                elif repair_self_check_missing_kind == "tool_budget_exhausted":
                    repair_policy_reason = "repair_self_check_tool_budget_exhausted"
                else:
                    repair_policy_reason = "repair_self_check_no_try_lean_call"
                _trace(
                    trace_prefix,
                    "  rejected repair turn that did not call try_lean before "
                    "submitting a repair proof.",
                )
                helpers, _proof = _extract_helpers_and_main(
                    content or "",
                    theorem_name=getattr(dossier, "theorem_name", "")
                    if dossier is not None
                    else "",
                    goal_statement=(
                        _active_root_tool_goal_statement(
                            dossier,
                            conv=conv,
                            helper_blocks=_current_active_root_frame_helper_blocks(),
                        )
                        or str(getattr(conv, "goal_statement", "") or "")
                    ),
                    allow_decl_main=True,
                )
                lemma_dag_candidates = _extract_lemma_dag_helper_declarations(
                    content or "",
                    theorem_name=getattr(dossier, "theorem_name", "")
                    if dossier is not None
                    else "",
                    suppress_solution_placeholders=bool(
                        getattr(conv, "suppress_solution_placeholders", False)
                    ),
                )
                repair_has_sorry_stub_helper = bool(_sorry_stub_helper_names(helpers))
                repair_giveup = _classify_giveup_signal(
                    content or "",
                    _proof,
                    require_structural_collapse=(
                        _proof is not None and not repair_has_sorry_stub_helper
                    ),
                )
                if repair_giveup is not None:
                    _banked = []
                else:
                    _banked = _bank_helpers_as_proposed(
                        dossier,
                        helpers,
                        phase=str(conv.role or "prove"),
                        turn_index=turn,
                        fallback_helpers=lemma_dag_candidates,
                        goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                        allow_helper_decomposition=bool(
                            getattr(conv, "allow_helper_decomposition", True)
                        )
                        and repair_giveup is None,
                    )
                policy_repair_redirect = bool(
                    repair_giveup is None
                    and effective_try_lean_tool_enabled
                    and max_tool_calls_per_turn > 0
                    and repair_self_check_redirect_bonus_remaining > 0
                )
                if policy_repair_redirect:
                    repair_self_check_redirect_bonus_remaining -= 1
                    turn_limit += 1
                _record_repair_policy_attempt(
                    dossier,
                    phase=conv.role,
                    turn_index=turn,
                    proof=content or "",
                    reason=repair_policy_reason,
                    metadata={
                        "tool_calls_used": tool_calls_used,
                        "repair_self_check_attempted": repair_self_check_attempted,
                        "repair_self_check_accepted": repair_self_check_accepted,
                        "repair_self_check_status": repair_self_check_missing_kind,
                        "repair_self_check_missing_kind": repair_self_check_missing_kind,
                        "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                        "policy_repair_redirect": policy_repair_redirect,
                        "policy_repair_redirect_bonus_remaining": (
                            repair_self_check_redirect_bonus_remaining
                        ),
                    },
                )
                if recorder is not None:
                    record_verdict = (
                        "proof_policy_repair_redirect"
                        if policy_repair_redirect
                        else "proof_policy_rejected"
                    )
                    recorder.record_turn({
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "max_turns_base": max_turns,
                        "turn_limit_effective": turn_limit,
                        "policy_repair_redirect_bonus_turn": turn > max_turns,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": list(helpers or lemma_dag_candidates or []),
                        "rejection_reason": repair_policy_reason,
                        "lean_error_type": repair_policy_reason,
                        "banked_proposed_helpers": list(_banked),
                        "giveup_cluster": (
                            repair_giveup["cluster"]
                            if repair_giveup is not None
                            else None
                        ),
                        "giveup_match": (
                            repair_giveup["match"] if repair_giveup is not None else ""
                        ),
                        "banking_suppressed_by_giveup": bool(repair_giveup),
                        "repair_self_check_attempted": repair_self_check_attempted,
                        "repair_self_check_accepted": repair_self_check_accepted,
                        "repair_self_check_status": repair_self_check_missing_kind,
                        "repair_self_check_missing_kind": repair_self_check_missing_kind,
                        "repair_self_check_budget_exhausted": repair_self_check_budget_exhausted,
                        "policy_repair_redirect": policy_repair_redirect,
                        "repair_redirect_reason": (
                            repair_policy_reason
                            if policy_repair_redirect
                            else ""
                        ),
                        "policy_repair_redirect_bonus_remaining": (
                            repair_self_check_redirect_bonus_remaining
                        ),
                        "verdict": record_verdict,
                    })
                if repair_giveup is not None:
                    conv.append_user(
                        _with_turn_budget_footer(
                            _giveup_decomposition_nudge(
                                repair_giveup["cluster"],
                                opaque_mode=bool(getattr(conv, "opaque_mode", False)),
                                allow_official_answer_visibility=bool(
                                    getattr(
                                        conv,
                                        "allow_official_answer_visibility",
                                        False,
                                    )
                                ),
                                official_answer_payload_present=getattr(
                                    conv,
                                    "official_answer_payload_present",
                                    None,
                                ),
                                matched_phrase=repair_giveup["match"],
                                recursion_depth=0,
                                max_recursion_depth=3,
                                role=str(getattr(conv, "role", "") or "prove"),
                                allow_helper_decomposition=bool(
                                    getattr(
                                        conv,
                                        "allow_helper_decomposition",
                                        True,
                                    )
                                ),
                            ),
                            role=conv.role,
                            turn=turn,
                            max_turns=turn_limit,
                        )
                    )
                else:
                    conv.append_user(
                        _format_repair_self_check_missing_feedback(
                            content,
                            require_try_lean=effective_try_lean_tool_enabled,
                            goal_statement=str(
                                getattr(conv, "goal_statement", "") or ""
                            ),
                            theorem_name=str(
                                getattr(dossier, "theorem_name", "")
                                if dossier is not None
                                else ""
                            ),
                            role=str(getattr(conv, "role", "") or "prove"),
                        )
                    )
                continue
            if recorder is not None:
                llm_failure_reason = str(
                    llm_error_classification.failure_reason or ""
                ).strip()
                llm_failure_scope_value = llm_failure_scope(llm_failure_reason)
                terminal_failure_reason = (
                    llm_failure_reason
                    if llm_error_classification.terminal
                    and llm_failure_scope_value != "scoped"
                    else ""
                )
                scoped_failure_reason = (
                    llm_failure_reason if llm_failure_scope_value == "scoped" else ""
                )
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_error": llm_error,
                    "llm_failure_kind": llm_error_classification.kind,
                    "llm_retryable": bool(llm_error_classification.retryable),
                    "terminal_failure_reason": terminal_failure_reason,
                    "scoped_failure_reason": scoped_failure_reason,
                    "llm_failure_scope": llm_failure_scope_value,
                    **llm_retry_deadline_record,
                    "provider_attempts": list(
                        _sanitize_model_facing_value(
                            list(getattr(client, "last_attempts", []) or []),
                            redact_solution_refs=_conversation_should_redact_solution_refs(
                                conv
                            ),
                            limit=1000,
                        )
                        or []
                    ),
                    "retry_count": llm_retry_count,
                    "llm_elapsed_s": llm_elapsed,
                    "verdict": "llm_call_failed",
                })
            return False, None

        conv.append_assistant(content)
        try:
            setattr(conv, "_last_llm_content", content)
        except Exception:
            pass
        _trace(
            trace_prefix,
            f"  assistant ({len(content)} chars, {llm_elapsed}s):",
        )
        print(_indent(content[:1600], trace_prefix + "    "), flush=True)
        if len(content) > 1600:
            _trace(trace_prefix, f"    ...({len(content) - 1600} more chars)")

        extraction_goal_statement = (
            _active_root_tool_goal_statement(
                dossier,
                conv=conv,
                helper_blocks=_current_active_root_frame_helper_blocks(),
            )
            or str(getattr(conv, "goal_statement", "") or "")
        )
        helpers, proof = _extract_helpers_and_main(
            content,
            theorem_name=getattr(dossier, "theorem_name", "") if dossier is not None else "",
            goal_statement=extraction_goal_statement,
            allow_decl_main=True,
        )
        extraction_chunks = _top_level_chunks_from_reply(content)
        helpers, proof, demoted_main_chunks_dropped = (
            _salvage_small_multiple_main_submission(
                helpers,
                proof,
                extraction_chunks,
                max_extra_mains=2,
            )
        )
        if demoted_main_chunks_dropped:
            repair_self_check_record_fields[
                "extra_main_salvaged_last_main_checked"
            ] = demoted_main_chunks_dropped
            repair_self_check_record_fields[
                "demoted_main_chunks_dropped"
            ] = demoted_main_chunks_dropped
            _increment_dossier_tool_metric(
                "mini_extra_main_salvaged_last_main_checked",
                demoted_main_chunks_dropped,
            )
        (
            helpers,
            preamble_redeclarations_dropped,
            preamble_redeclaration_conflicts,
        ) = _partition_preamble_redeclarations(
            helpers,
            str(
                getattr(conv, "lean_preamble", "")
                or getattr(conv, "preamble", "")
                or ""
            ),
        )
        if preamble_redeclarations_dropped:
            repair_self_check_record_fields[
                "preamble_redeclarations_dropped"
            ] = list(preamble_redeclarations_dropped)
            _increment_dossier_tool_metric(
                "mini_preamble_redeclarations_dropped",
                len(preamble_redeclarations_dropped),
            )
        # Bonus #7 fix (2026-05-08): hoist the lemma-DAG candidate
        # extraction so both downstream branches (no-proof at :3517 and
        # proof-extracted at :4028) share ONE extraction. Two sites
        # previously called ``_extract_lemma_dag_helper_declarations``
        # independently — only one ran per turn (they're mutually
        # exclusive on ``proof is None``), but the source duplication
        # was a maintenance hazard and meant any future signature
        # change had to be made in two places. Memoizing also opens the
        # door to the observability trace below.
        _lemma_dag_extracted_from_content = (
            _extract_lemma_dag_helper_declarations(
                content,
                theorem_name=getattr(dossier, "theorem_name", "")
                if dossier is not None
                else "",
                suppress_solution_placeholders=bool(
                    getattr(conv, "suppress_solution_placeholders", False)
                ),
            )
            if not helpers
            else []
        )
        turn_has_sorry_stub_helper = bool(_sorry_stub_helper_names(helpers))
        turn_giveup = _classify_giveup_signal(
            content,
            proof,
            require_structural_collapse=(
                proof is not None and not turn_has_sorry_stub_helper
            ),
        )
        can_bank_turn_proposals = (
            bool(getattr(conv, "allow_helper_decomposition", True))
            and turn_giveup is None
        )
        if turn_giveup is not None and (
            helpers or _lemma_dag_extracted_from_content
        ):
            _trace(
                trace_prefix,
                "  suppressed helper proposal banking after give-up/off-ramp prose.",
            )
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                _with_turn_budget_footer(
                    _giveup_decomposition_nudge(
                        turn_giveup["cluster"],
                        opaque_mode=bool(getattr(conv, "opaque_mode", False)),
                        allow_official_answer_visibility=bool(
                            getattr(
                                conv,
                                "allow_official_answer_visibility",
                                False,
                            )
                        ),
                        official_answer_payload_present=getattr(
                            conv,
                            "official_answer_payload_present",
                            None,
                        ),
                        matched_phrase=turn_giveup["match"],
                        recursion_depth=0,
                        max_recursion_depth=3,
                        role=str(getattr(conv, "role", "") or "prove"),
                        allow_helper_decomposition=bool(
                            getattr(conv, "allow_helper_decomposition", True)
                        ),
                    ),
                    role=conv.role,
                    turn=turn,
                    max_turns=turn_limit,
                )
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": list(
                        helpers or _lemma_dag_extracted_from_content or []
                    ),
                    "extracted_proof": proof,
                    "rejection_reason": (
                        "giveup_no_proof_active_proof_redirect"
                        if proof is None
                        else "giveup_policy_active_proof_redirect"
                    ),
                    "banked_proposed_helpers": [],
                    "giveup_cluster": turn_giveup["cluster"],
                    "giveup_match": turn_giveup["match"],
                    "banking_suppressed_by_giveup": True,
                    "verdict": (
                        "no_proof_extracted"
                        if proof is None
                        else "proof_policy_rejected"
                    ),
                })
            continue
        sorry_stub_names = _sorry_stub_helper_names(helpers)
        if proof is not None and sorry_stub_names:
            root_equivalent_names = _root_equivalent_sorry_stub_helper_names_from_blocks(
                helpers,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            )
            _drop_last_assistant_if_content(conv, content)
            _trace(
                trace_prefix,
                "  rejected Lean block mixing sorry-stub helper(s) with a main proof.",
            )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "rejection_reason": "helper_stub_with_main_proof",
                    "rejection_match": ", ".join(sorry_stub_names),
                    "banked_proposed_helpers": list(_banked),
                    "verdict": "proof_policy_rejected",
                })
            conv.append_user(
                _format_invalid_helper_stub_with_main_feedback(
                    stub_names=sorry_stub_names,
                    root_equivalent_names=root_equivalent_names,
                )
            )
            continue

        post_main_declarations = (
            _find_helpers_after_final_main(extraction_chunks)
            if demoted_main_chunks_dropped
            else _find_post_main_helper_declarations(extraction_chunks)
        )
        if post_main_declarations:
            _trace(
                trace_prefix,
                "  main proof was followed by helper declaration(s); asking "
                "for helpers-before-proof ordering.",
            )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            format_policy_redirect_granted = False
            if (
                turn >= turn_limit
                and format_policy_redirect_bonus_remaining > 0
                and turn_giveup is None
            ):
                format_policy_redirect_bonus_remaining -= 1
                turn_limit += 1
                format_policy_redirect_granted = True
                _increment_dossier_tool_metric(
                    "mini_format_policy_redirect_granted",
                    1,
                )
            elif turn >= turn_limit:
                _increment_dossier_tool_metric(
                    "mini_policy_rejection_final_turn_no_retry",
                    1,
                )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "rejection_reason": "post_main_helper_declaration",
                    "post_main_declarations": post_main_declarations,
                    "banked_proposed_helpers": list(_banked),
                    "policy_repair_redirect": format_policy_redirect_granted,
                    "format_policy_redirect_bonus_remaining": (
                        format_policy_redirect_bonus_remaining
                    ),
                    "verdict": (
                        "proof_policy_repair_redirect"
                        if format_policy_redirect_granted
                        else "proof_policy_rejected"
                    ),
                })
            names = ", ".join(
                f"`{_prompt_safe_helper_name(name)}`"
                for name in post_main_declarations
            )
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                "Your Lean block contains helper declaration(s) after the "
                f"main proof: {names}. Helper declarations must come BEFORE "
                "the final `example : <main_goal_type> := by ...` or bare "
                "`by ...` proof block. Move those helpers above the main "
                "proof, then end the fenced Lean block with the main proof."
            )
            continue

        # Catch the second-most-common ordering bug: multiple main-proof-
        # shaped chunks (e.g. two ``example`` blocks, or a stray bare
        # ``by`` followed by an ``example``). The extractor silently uses
        # only the LAST one and demotes the rest into the lemma_block as
        # anonymous declarations — so ``_find_post_main_helper_declarations``
        # (which only walks NAMED post-main helpers) won't fire. Issue a
        # dedicated nudge instead of letting Lean see competing proofs.
        extra_main_chunks = _find_extra_main_proof_chunks(
            extraction_chunks
        )
        if demoted_main_chunks_dropped:
            extra_main_chunks = []
        if extra_main_chunks:
            _trace(
                trace_prefix,
                f"  reply contained {len(extra_main_chunks)} extra main-proof "
                f"candidate(s); asking for a single proof.",
            )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            format_policy_redirect_granted = False
            if (
                turn >= turn_limit
                and format_policy_redirect_bonus_remaining > 0
                and turn_giveup is None
            ):
                format_policy_redirect_bonus_remaining -= 1
                turn_limit += 1
                format_policy_redirect_granted = True
                _increment_dossier_tool_metric(
                    "mini_format_policy_redirect_granted",
                    1,
                )
            elif turn >= turn_limit:
                _increment_dossier_tool_metric(
                    "mini_policy_rejection_final_turn_no_retry",
                    1,
                )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "rejection_reason": "multiple_main_proofs",
                    "extra_main_chunks": extra_main_chunks,
                    "banked_proposed_helpers": list(_banked),
                    "policy_repair_redirect": format_policy_redirect_granted,
                    "format_policy_redirect_bonus_remaining": (
                        format_policy_redirect_bonus_remaining
                    ),
                    "verdict": (
                        "proof_policy_repair_redirect"
                        if format_policy_redirect_granted
                        else "proof_policy_rejected"
                    ),
                })
            extras = "; ".join(
                f"`{_prompt_safe_inline_text(c, limit=120)}`"
                for c in extra_main_chunks
            )
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                "Your Lean block contains multiple main-proof candidates. "
                "The verifier checks only ONE: the LAST `example` or bare "
                f"`by` block. Earlier one(s) are demoted to "
                f"anonymous helpers in the compilation context: {extras}. "
                "Submit exactly one main proof. If you needed intermediate "
                "facts, write them as NAMED helpers (`theorem h_foo : ... "
                ":= by ...`) above the single main proof."
            )
            continue

        if preamble_redeclaration_conflicts:
            conflict_names = ", ".join(
                f"`{_prompt_safe_helper_name(name)}`"
                for name in preamble_redeclaration_conflicts[:4]
            )
            _trace(
                trace_prefix,
                f"  reply redefines immutable preamble declaration(s) with "
                f"different content; rejecting: {conflict_names}",
            )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            format_policy_redirect_granted = False
            if (
                turn >= turn_limit
                and format_policy_redirect_bonus_remaining > 0
                and turn_giveup is None
            ):
                format_policy_redirect_bonus_remaining -= 1
                turn_limit += 1
                format_policy_redirect_granted = True
                _increment_dossier_tool_metric(
                    "mini_format_policy_redirect_granted",
                    1,
                )
            elif turn >= turn_limit:
                _increment_dossier_tool_metric(
                    "mini_policy_rejection_final_turn_no_retry",
                    1,
                )
            _increment_dossier_tool_metric(
                "mini_preamble_redeclaration_conflicts",
                len(preamble_redeclaration_conflicts),
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "rejection_reason": "preamble_redeclaration_conflict",
                    "preamble_redeclaration_conflicts": list(
                        preamble_redeclaration_conflicts
                    ),
                    "banked_proposed_helpers": list(_banked),
                    "policy_repair_redirect": format_policy_redirect_granted,
                    "format_policy_redirect_bonus_remaining": (
                        format_policy_redirect_bonus_remaining
                    ),
                    "verdict": (
                        "proof_policy_repair_redirect"
                        if format_policy_redirect_granted
                        else "proof_policy_rejected"
                    ),
                })
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                "Your Lean block redefines declaration(s) already fixed by "
                f"the immutable preamble with DIFFERENT content: "
                f"{conflict_names}. The preamble's definitions are "
                "authoritative and cannot be shadowed or replaced. Remove "
                "the redeclaration(s) and write the proof against the "
                "existing definitions; if you believe a definition unfolds "
                "differently, derive that as a proved local `have` step "
                "instead of redefining the name."
            )
            continue

        repair_context_lemmas = (
            _feedback_lemmas_for_answer_safe_recheck(
                dossier.verified_helper_blocks(),
                conv,
            )
            if dossier is not None
            else []
        )
        repair_has_accepted_evidence = _repair_self_check_has_accepted_evidence(
            repair_self_check_codes,
            goal_statement=conv.goal_statement,
            preamble=conv.preamble,
            context_lemmas=repair_context_lemmas,
        )
        repair_self_check_mismatch_observed = (
            repair_self_check_required
            and effective_try_lean_tool_enabled
            and proof is not None
            and repair_has_accepted_evidence
            and not _repair_self_check_matches_submission(
                repair_self_check_codes,
                proof,
                (),
                goal_statement=conv.goal_statement,
                preamble=_proof_state_check_preamble(conv),
                context_lemmas=repair_context_lemmas,
            )
        )
        if repair_self_check_mismatch_observed:
            _trace(
                trace_prefix,
                "  repair self-check differed from final proof; continuing to final Lean verifier.",
            )
            repair_self_check_record_fields[
                "repair_self_check_mismatch_observed"
            ] = True

        reuse_scan_text = "\n\n".join([*helpers, proof or ""])
        reused_rejected_fragments = _proof_reuses_rejected_fragments(
            conv,
            reuse_scan_text,
        )
        # Narrow companion gate (2026-05-13 round-2 fix): detect
        # goal-as-sorry-helper repackaging WITHOUT banning the goal
        # expression context-free, AND without merging into
        # ``reused_rejected_fragments`` — that merge routed the goal
        # target through ``_format_reused_fragment_feedback``, which
        # wrote it under _REJECTED_FRAGMENT_HEADER, which the next
        # turn's append_user re-parsed into ``rejected_code_fragments``,
        # re-poisoning the strict channel after one round-trip.
        repackaged_goal_targets = _proof_repackages_transient_goal_target(
            conv,
            reuse_scan_text,
        )
        if reused_rejected_fragments or repackaged_goal_targets:
            # Bank any proposed helpers BEFORE rejecting (Claim 1 banking
            # ordering fix): the no_proof_extracted path at line ~7000
            # is unreachable from here because we ``continue`` below.
            # Helpers proposed in a turn that the policy gate rejects
            # still encode the prover's decomposition signal, so they
            # belong in the dossier so the planner can seed claims from
            # them on the next phase.
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            # Route the two channels through their own
            # rejection-reason tags and feedback formatters so the
            # narrow-gate hits don't poison ``rejected_code_fragments``
            # via the strict-fragment feedback formatter on the next
            # round-trip (the round-2 regression Agent A surfaced).
            primary_reason = (
                "reused_rejected_lean_fragment"
                if reused_rejected_fragments
                else "transient_goal_target_sorry_helper"
            )
            policy_repair_redirect = bool(
                (reused_rejected_fragments or repackaged_goal_targets)
                and reused_fragment_redirect_bonus_remaining > 0
            )
            if policy_repair_redirect:
                reused_fragment_redirect_bonus_remaining -= 1
                turn_limit += 1
            _trace(
                trace_prefix,
                "  rejected repair: "
                + ("reused " + ", ".join(repr(f) for f in reused_rejected_fragments)
                   if reused_rejected_fragments else "")
                + ("; repackaged goal target(s): "
                   + ", ".join(repr(t) for t in repackaged_goal_targets)
                   if repackaged_goal_targets else ""),
            )
            _record_repair_policy_attempt(
                dossier,
                phase=conv.role,
                turn_index=turn,
                proof=reuse_scan_text,
                reason=primary_reason,
                metadata={
                        "tool_calls_used": tool_calls_used,
                        "rejection_fragments": list(reused_rejected_fragments),
                        "repackaged_goal_targets": list(repackaged_goal_targets),
                        "policy_repair_redirect": policy_repair_redirect,
                        "policy_repair_redirect_bonus_remaining": (
                            reused_fragment_redirect_bonus_remaining
                        ),
                    },
                )
            if recorder is not None:
                record_verdict = (
                    "proof_policy_repair_redirect"
                    if policy_repair_redirect
                    else "proof_policy_rejected"
                )
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "rejection_reason": primary_reason,
                    "rejection_fragments": list(reused_rejected_fragments),
                    "repackaged_goal_targets": list(repackaged_goal_targets),
                    "lean_error_type": primary_reason,
                    "policy_repair_redirect": policy_repair_redirect,
                    "repair_redirect_reason": (
                        primary_reason if policy_repair_redirect else ""
                    ),
                    "policy_repair_redirect_bonus_remaining": (
                        reused_fragment_redirect_bonus_remaining
                    ),
                    "banked_proposed_helpers": list(_banked),
                    "verdict": record_verdict,
                })
            _drop_last_assistant_if_content(conv, content)
            # Emit channel-specific feedback messages. If BOTH channels
            # fired, send the strict-fragment feedback first then the
            # repackaging feedback — the LLM sees both prohibitions
            # without crosstalk.
            if reused_rejected_fragments:
                conv.append_user(
                    _format_reused_fragment_feedback(
                        reused_rejected_fragments,
                        _rejected_fragments_from_latest_feedback(conv),
                    ),
                    repair_payload={
                        "fragments": [
                            *reused_rejected_fragments,
                            *_rejected_fragments_from_latest_feedback(conv),
                        ],
                        "transient_goal_targets": [],
                    },
                )
            if repackaged_goal_targets:
                conv.append_user(
                    _format_repackaged_goal_target_feedback(
                        repackaged_goal_targets,
                        _transient_goal_targets_from_latest_feedback(conv),
                    ),
                    repair_payload={
                        "fragments": [],
                        "transient_goal_targets": [
                            *repackaged_goal_targets,
                            *_transient_goal_targets_from_latest_feedback(conv),
                        ],
                    },
                )
            continue

        if proof is None:
            forbidden_command = _find_forbidden_lean_command(helpers, "")
            if forbidden_command is not None:
                _trace(
                    trace_prefix,
                    f"  rejected Lean block containing forbidden command: {forbidden_command!r}",
                )
                _banked = _bank_helpers_as_proposed(
                    dossier,
                    helpers,
                    phase=str(conv.role or "prove"),
                    turn_index=turn,
                    goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                    allow_helper_decomposition=can_bank_turn_proposals,
                )
                if recorder is not None:
                    recorder.record_turn({
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": None,
                        "rejection_reason": "forbidden_lean_command",
                        "rejection_match": forbidden_command,
                        "banked_proposed_helpers": list(_banked),
                        "verdict": "proof_policy_rejected",
                    })
                _drop_last_assistant_if_content(conv, content)
                conv.append_user(
                    "Your Lean block contains a top-level command "
                    f"({forbidden_command!r}). The proof block may contain helper "
                    "declarations and the main proof only; do not use `#eval`, "
                    "`#check`, `#print`, `import`, or `axiom` commands in proof "
                    "submissions."
                )
                continue
            if turn_giveup is not None:
                _trace(
                    trace_prefix,
                    "  suppressed helper-only decomposition after give-up/off-ramp prose.",
                )
                _drop_last_assistant_if_content(conv, content)
                feedback = _with_turn_budget_footer(
                    _giveup_decomposition_nudge(
                        turn_giveup["cluster"],
                        opaque_mode=bool(getattr(conv, "opaque_mode", False)),
                        allow_official_answer_visibility=bool(
                            getattr(conv, "allow_official_answer_visibility", False)
                        ),
                        official_answer_payload_present=getattr(
                            conv,
                            "official_answer_payload_present",
                            None,
                        ),
                        matched_phrase=turn_giveup["match"],
                        recursion_depth=0,
                        max_recursion_depth=3,
                        role=str(getattr(conv, "role", "") or "prove"),
                        allow_helper_decomposition=bool(
                            getattr(conv, "allow_helper_decomposition", True)
                        ),
                    ),
                    role=conv.role,
                    turn=turn,
                    max_turns=turn_limit,
                )
                conv.append_user(feedback)
                no_proof_target_integrity = _legacy_no_proof_target_integrity_metadata(
                    conv=conv,
                    dossier=dossier,
                    recorder=recorder,
                    llm_output=content,
                    phase=str(conv.role or "prove"),
                    turn=turn,
                    model_id=model_id,
                    common_record={
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                    },
                )
                if recorder is not None:
                    recorder.record_turn({
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": None,
                        "rejection_reason": "giveup_no_proof_active_proof_redirect",
                        "banked_proposed_helpers": [],
                        "giveup_cluster": turn_giveup["cluster"],
                        "giveup_match": turn_giveup["match"],
                        "banking_suppressed_by_giveup": True,
                        **no_proof_target_integrity,
                        "verdict": "no_proof_extracted",
                    })
                continue
            lemma_dag_helpers: List[str] = []
            # Bonus #7 fix: reuse the memoized extraction from the top of
            # the per-turn block instead of re-running it here.
            lemma_dag_candidate_helpers = helpers or _lemma_dag_extracted_from_content
            root_equivalent_names = _root_equivalent_sorry_stub_helper_names_from_blocks(
                lemma_dag_candidate_helpers,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            )
            if root_equivalent_names:
                _trace(
                    trace_prefix,
                    "  rejected helper-only decomposition that restated the root goal.",
                )
                # Bank the NON-root-equivalent helpers (the root-shaped
                # ones would never be useful as proposed claims since
                # they're verbatim restatements of the root).
                _bankable = [
                    src
                    for src in (helpers or ())
                    if isinstance(src, str)
                    and (helper_decl_name(src) or "") not in set(root_equivalent_names)
                ]
                _banked = _bank_helpers_as_proposed(
                    dossier,
                    _bankable,
                    phase=str(conv.role or "prove"),
                    turn_index=turn,
                    goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                    allow_helper_decomposition=can_bank_turn_proposals,
                )
                if recorder is not None:
                    recorder.record_turn({
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": None,
                        "rejection_reason": "root_equivalent_helper_stub",
                        "rejection_match": ", ".join(root_equivalent_names),
                        "banked_proposed_helpers": list(_banked),
                        "verdict": "proof_policy_rejected",
                    })
                _drop_last_assistant_if_content(conv, content)
                conv.append_user(
                    _format_root_equivalent_helper_feedback(root_equivalent_names)
                )
                continue

            # D2 gate-side fix (2026-05-09): if the LLM emitted sorry-stub
            # helpers (decomposition request), open a task ad hoc so the
            # subsequent gate passes and helpers materialize as child_goals.
            # See ensure_decomposition_task_open_for_sorry_stubs docstring.
            if (
                lemma_dag_candidate_helpers
                and proof_state is not None
                and dossier is not None
                and bool(getattr(conv, "allow_helper_decomposition", True))
                and not proof_state.has_open_decomposition_task()
            ):
                from ensemble_prover.proof_state_executor import (
                    ensure_decomposition_task_open_for_lemma_dag_candidates,
                )
                lemma_dag_open_attempt = ensure_decomposition_task_open_for_lemma_dag_candidates(
                    proof_state,
                    lemma_dag_candidate_helpers,
                    source=f"lemma_dag_helpers_volunteered:legacy_post_failure:turn={turn}",
                )
            else:
                lemma_dag_open_attempt = {}
            if (
                lemma_dag_candidate_helpers
                and proof_state is not None
                and dossier is not None
                and bool(getattr(conv, "allow_helper_decomposition", True))
                and not proof_state.has_open_decomposition_task()
            ):
                # Observability for candidates that could not open a
                # decomposition task. This includes non-sorry helper DAGs,
                # missing proof-state APIs, and real closed-task cases.
                open_reason = str(
                    (lemma_dag_open_attempt or {}).get("reason") or "not_open"
                )
                _trace(
                    trace_prefix,
                    "  lemma-DAG candidates available but no decomposition task "
                    f"could be opened ({open_reason}); skipping. "
                    f"({len(lemma_dag_candidate_helpers)} candidate(s).)",
                )
                if recorder is not None:
                    recorder.record_turn({
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": proof,
                        "lemma_dag_candidate_count": len(
                            lemma_dag_candidate_helpers
                        ),
                        "lemma_dag_open_attempt": dict(lemma_dag_open_attempt or {}),
                        "verdict": "lemma_dag_no_decomposition_task_opened",
                    })
            if (
                lemma_dag_candidate_helpers
                and proof_state is not None
                and dossier is not None
                and bool(getattr(conv, "allow_helper_decomposition", True))
                and proof_state.has_open_decomposition_task()
            ):
                child_goal_ids_before = {
                    nid
                    for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                    if getattr(node, "kind", "") == "child_goal"
                }
                lemma_dag_helpers = await _try_proof_state_lemma_dag_helpers(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    helpers=lemma_dag_candidate_helpers,
                    recorder=recorder,
                    trace_prefix=trace_prefix,
                    turn=turn,
                    timeout_s=proof_state_child_tactic_timeout_s,
                    proof_cache=proof_cache,
                )
                child_goal_ids_after = {
                    nid
                    for nid, node in (getattr(proof_state, "nodes", {}) or {}).items()
                    if getattr(node, "kind", "") == "child_goal"
                }
                lemma_dag_child_node_ids = sorted(
                    child_goal_ids_after - child_goal_ids_before
                )
                if (
                    proof_state.has_open_decomposition_task() is False
                    or lemma_dag_helpers
                    or lemma_dag_child_node_ids
                ):
                    proof_state.sync_to_graph(
                        dossier,
                        phase="proof_state_lemma_dag_decomposition",
                        turn_index=turn,
                    )
                    if (
                        (lemma_dag_helpers or lemma_dag_child_node_ids)
                        and proof_state_child_tactics_enabled
                    ):
                        (
                            state_ok,
                            state_proof,
                            proof_state_helpers,
                        ) = await _try_proof_state_child_closures(
                            conv=conv,
                            lean=lean,
                            dossier=dossier,
                            proof_state=proof_state,
                            recorder=recorder,
                            trace_prefix=trace_prefix,
                            turn=turn,
                            timeout_s=proof_state_child_tactic_timeout_s,
                            max_candidates=proof_state_child_tactic_max_candidates,
                            max_nodes=proof_state_child_goal_limit,
                            max_decl_applications=proof_state_decl_application_limit,
                            batch_parallelism=proof_state_batch_parallelism,
                            proof_cache=proof_cache,
                            target_node_ids=(
                                tuple(lemma_dag_child_node_ids)
                                if lemma_dag_child_node_ids
                                else None
                            ),
                        )
                        proof_state.sync_to_graph(
                            dossier,
                            phase="proof_state_lemma_dag_root_check",
                            turn_index=turn,
                        )
                        if state_ok and state_proof:
                            if recorder is not None:
                                recorder.record_turn(
                                    {
                                        "phase": "proof_state_lemma_dag_root_check",
                                        "turn_in_phase": turn,
                                        **repair_self_check_record_fields,
                                        "accepted_helpers": list(proof_state_helpers),
                                        "proof_state": proof_state.to_record(),
                                        "verdict": "solved_after_lemma_dag_helper",
                                    }
                                )
                            return True, state_proof
                    if lemma_dag_helpers:
                        _drop_last_assistant_if_content(conv, content)
                        conv.append_user(
                            "The controller processed your helper declarations as "
                            "lemma-DAG decomposition work. Now submit one main proof "
                            "that assembles the root from verified helpers only. "
                            "Open proof-state child goals are not facts yet; prove "
                            "or repair them before using them in root assembly."
                        )
                    else:
                        _drop_last_assistant_if_content(conv, content)
                        conv.append_user(
                            "The controller recorded your helper declarations as "
                            "open proof-state child goals and started deterministic "
                            "closure on them. Open proof-state child goals are "
                            "not facts yet; prove or repair them before root "
                            "assembly. The scheduler will continue with "
                            "retrieval, tactic search, and recursive helper proving "
                            "before re-engaging the root proof."
                        )
                    continue
            helper_probe_timeout = float(proof_state_child_tactic_timeout_s or 0.0)
            if (
                lemma_dag_candidate_helpers
                and dossier is not None
                and bool(getattr(conv, "allow_helper_decomposition", True))
                and helper_probe_timeout > 0.0
            ):
                _trace(
                    trace_prefix,
                    "  attempting answer-safe helper salvage from helper-only reply...",
                )
                from ensemble_prover.helper_salvage import collect_open_child_targets

                salvager = HelperSalvager(
                    lean,
                    preamble=_proof_state_check_preamble(conv),
                    answer_safe_preamble=str(getattr(conv, "preamble", "") or ""),
                    timeout_s=helper_probe_timeout,
                    relevance_gate_root_statement=str(
                        getattr(dossier, "root_statement", "") or ""
                    ),
                    relevance_gate_open_targets=collect_open_child_targets(proof_state),
                )
                salvage_result = await salvager.salvage(
                    lemma_dag_candidate_helpers,
                    dossier=dossier,
                    phase=f"{conv.role}:helper_only_salvage",
                    turn_index=turn,
                )
                invalidated_helpers = [
                    *list(getattr(salvage_result, "replaced", []) or []),
                    *list(getattr(salvage_result, "evicted", []) or []),
                ]
                if invalidated_helpers and proof_state is not None:
                    try:
                        proof_state.reconcile_with_dossier(dossier)
                        proof_state.invalidate_assembly_contracts_for_helpers(
                            invalidated_helpers,
                            phase=f"{conv.role}:helper_only_salvage",
                            turn_index=turn,
                            conservative=True,
                        )
                    except Exception:
                        pass
                if recorder is not None:
                    recorder.record_turn(
                        {
                            "phase": "helper_only_salvage",
                            "turn_in_phase": turn,
                            "candidate_count": len(lemma_dag_candidate_helpers),
                            "accepted_helpers": list(salvage_result.accepted),
                            "rejected_helpers": list(salvage_result.rejected),
                            "skipped_helpers": list(salvage_result.skipped),
                            "verdict": (
                                "helpers_accepted"
                                if salvage_result.accepted
                                else "helpers_rejected"
                            ),
                        }
                    )
                if salvage_result.accepted:
                    if proof_cache is not None:
                        for helper_name in salvage_result.accepted:
                            helper_record = dossier.verified_helpers.get(helper_name)
                            if helper_record is not None:
                                store_verified_helper_for_dossier(
                                    proof_cache,
                                    helper_record.source,
                                    preamble=_proof_state_check_preamble(conv),
                                    dossier=dossier,
                                    phase=f"{conv.role}:helper_only_salvage",
                                )
                    if proof_state is not None:
                        proof_state.sync_to_graph(
                            dossier,
                            phase="helper_only_salvage",
                            turn_index=turn,
                        )
                    if proof_state is not None and proof_state_child_tactics_enabled:
                        (
                            state_ok,
                            state_proof,
                            salvaged_state_helpers,
                        ) = await _try_proof_state_salvaged_helper_assembly(
                            conv=conv,
                            lean=lean,
                            dossier=dossier,
                            proof_state=proof_state,
                            helper_names=salvage_result.accepted,
                            recorder=recorder,
                            trace_prefix=trace_prefix,
                            turn=turn,
                            timeout_s=helper_probe_timeout,
                            max_nodes=proof_state_child_goal_limit,
                            proof_cache=proof_cache,
                            phase="helper_only_salvage",
                        )
                        proof_state.sync_to_graph(
                            dossier,
                            phase="helper_only_salvage_proof_state_assembly",
                            turn_index=turn,
                        )
                        if state_ok and state_proof:
                            if recorder is not None:
                                recorder.record_turn(
                                    {
                                        "phase": "helper_only_salvage_proof_state_assembly",
                                        "turn_in_phase": turn,
                                        **repair_self_check_record_fields,
                                        "accepted_helpers": list(salvaged_state_helpers),
                                        "proof_state": proof_state.to_record(),
                                        "verdict": "solved_after_helper_only_salvage",
                                    }
                                )
                            return True, state_proof
                    if proof_state is not None and proof_state_child_tactics_enabled:
                        (
                            state_ok,
                            state_proof,
                            proof_state_helpers,
                        ) = await _try_proof_state_child_closures(
                            conv=conv,
                            lean=lean,
                            dossier=dossier,
                            proof_state=proof_state,
                            recorder=recorder,
                            trace_prefix=trace_prefix,
                            turn=turn,
                            timeout_s=helper_probe_timeout,
                            max_candidates=proof_state_child_tactic_max_candidates,
                            max_nodes=proof_state_child_goal_limit,
                            max_decl_applications=proof_state_decl_application_limit,
                            batch_parallelism=proof_state_batch_parallelism,
                            proof_cache=proof_cache,
                        )
                        proof_state.sync_to_graph(
                            dossier,
                            phase="helper_only_salvage_root_check",
                            turn_index=turn,
                        )
                        if state_ok and state_proof:
                            if recorder is not None:
                                recorder.record_turn(
                                    {
                                        "phase": "helper_only_salvage_root_check",
                                        "turn_in_phase": turn,
                                        **repair_self_check_record_fields,
                                        "accepted_helpers": list(proof_state_helpers),
                                        "proof_state": proof_state.to_record(),
                                        "verdict": "solved_after_helper_only_salvage",
                                    }
                                )
                            return True, state_proof
                    if (
                        int(proof_state_child_tactic_max_candidates or 0) > 0
                    ):
                        # Use the proof-state acceptance preamble so this
                        # tactic-close arm validates against the same preamble
                        # as the proof-state assembly arm immediately above.
                        helper_blocks = _root_tactic_helper_blocks_for_names(
                            salvage_result.accepted
                        )
                        root_tactic = await try_close_root_with_active_lift(
                            lean=lean,
                            goal_statement=conv.goal_statement,
                            preamble=_proof_state_acceptance_preamble(conv),
                            helpers=helper_blocks,
                            active_root_targets=tuple(
                                item
                                for item in list(getattr(dossier, "active_root_targets", []) or ())
                                if isinstance(item, dict)
                            ),
                            active_root_frame_helper_blocks=dossier.verified_helper_blocks(),
                            timeout_s=helper_probe_timeout,
                            max_candidates=max(
                                1,
                                int(proof_state_child_tactic_max_candidates or 1),
                            ),
                            suppress_solution_placeholders=bool(
                                getattr(conv, "suppress_solution_placeholders", True)
                            ),
                            opaque_mode=bool(getattr(conv, "opaque_mode", True)),
                            allow_official_answer_visibility=bool(
                                getattr(conv, "allow_official_answer_visibility", False)
                            ),
                            official_answer_payload_present=getattr(
                                conv,
                                "official_answer_payload_present",
                                getattr(
                                    dossier,
                                    "official_answer_payload_present",
                                    None,
                                ),
                            ),
                            tactic_source_suppression_records=tactic_source_suppression_records,
                            tactic_source_suppression_helper_blocks=helper_blocks,
                            tactic_closer=try_close_with_tactics,
                            attempt_observer=dossier_lean_attempt_observer(
                                dossier,
                                "salvage_root_tactic",
                            ),
                        )
                        success_attempt = next(
                            (
                                attempt
                                for attempt in root_tactic.attempts
                                if isinstance(attempt, dict) and attempt.get("ok")
                            ),
                            None,
                        )
                        root_tactic_record = {
                            "phase": "helper_only_salvage_root_tactic",
                            "turn_in_phase": turn,
                            **repair_self_check_record_fields,
                            "accepted_helpers": list(salvage_result.accepted),
                            "tactic_candidate_count": root_tactic.candidate_count,
                            **tactic_attempt_telemetry_fields(root_tactic.attempts),
                            "tactic_attempts": root_tactic.attempts[:10],
                            "tactic_success_attempt": success_attempt,
                            "tactic_elapsed_s": root_tactic.elapsed_s,
                            "tactic_exit_reason": root_tactic.exit_reason,
                            "active_root_target_statement": dict(
                                getattr(root_tactic, "cache_metadata", {}) or {}
                            ).get("active_root_target_statement"),
                            "active_root_lift_attempted": bool(
                                dict(getattr(root_tactic, "cache_metadata", {}) or {}).get(
                                    "active_root_lift_attempted"
                                )
                            ),
                            "active_root_lift_succeeded": bool(
                                dict(getattr(root_tactic, "cache_metadata", {}) or {}).get(
                                    "active_root_lift_succeeded"
                                )
                            ),
                            "verdict": (
                                "tactic_solved"
                                if root_tactic.ok
                                else "tactic_rejected"
                            ),
                        }
                        root_tactic_contract_status: Dict[str, Any] = {}
                        if root_tactic.ok and root_tactic.proof:
                            root_tactic_contract_status = root_tactic_success_contract_status(
                                dossier,
                                proof=root_tactic.proof,
                                helper_blocks=helper_blocks,
                                success_attempt=success_attempt,
                                phase="helper_only_salvage_root_tactic",
                                turn_index=turn,
                                target_statement=conv.goal_statement,
                            )
                            root_tactic_record["route_assembly_contract_status"] = (
                                root_tactic_contract_status
                            )
                            if not bool(root_tactic_contract_status.get("ready")):
                                root_tactic_record["verdict"] = (
                                    "root_route_contract_not_ready"
                                )
                                root_tactic_record["route_contract_verdict"] = str(
                                    root_tactic_contract_status.get("verdict") or ""
                                )
                        if recorder is not None:
                            recorder.record_turn(root_tactic_record)
                        if (
                            root_tactic.ok
                            and root_tactic.proof
                            and bool(root_tactic_contract_status.get("ready"))
                        ):
                            route_helper_names = [
                                str(name or "").strip()
                                for name in list(
                                    root_tactic_contract_status.get("helper_names") or []
                                )
                                if str(name or "").strip()
                            ]
                            replay_helpers = _helper_blocks_for_names(
                                helper_blocks,
                                route_helper_names,
                            )
                            if not replay_helpers:
                                replay_helpers = helper_blocks
                            replay_closure = getattr(
                                dossier, "root_replay_helper_closure", None
                            )
                            if callable(replay_closure):
                                closed = replay_closure(
                                    replay_helpers=replay_helpers,
                                    support_helper_names=route_helper_names,
                                )
                                if closed:
                                    replay_helpers = list(closed)
                            helper_names = _helper_names_from_blocks(
                                replay_helpers
                            ) or route_helper_names
                            from ensemble_prover.root_finalization import (
                                finalize_root_solution,
                                root_verification_certificate,
                            )

                            finalization = finalize_root_solution(
                                dossier=dossier,
                                proof_state=proof_state,
                                proof=root_tactic.proof,
                                replay_helpers=replay_helpers,
                                helper_names=helper_names,
                                phase="helper_only_salvage_root_tactic",
                                turn_index=turn,
                                route_id=str(
                                    root_tactic_contract_status.get("route_id")
                                    or root_tactic_contract_status.get("created_route_id")
                                    or ""
                                ),
                                dependency_node_ids=tuple(
                                    str(node_id or "").strip()
                                    for node_id in list(
                                        root_tactic_contract_status.get("dependency_node_ids")
                                        or root_tactic_contract_status.get("required_node_ids")
                                        or []
                                    )
                                    if str(node_id or "").strip()
                                ),
                                dependency_helper_names=(
                                    route_helper_names or helper_names
                                ),
                                target_statement=str(
                                    getattr(conv, "goal_statement", "") or ""
                                ),
                                # A helper-free close (verdict
                                # root_tactic_no_helper_dependencies) has no route
                                # to bind; requiring one would reject a
                                # Lean-accepted proof.  Match try_root_tactic_close.
                                require_route_contract=(
                                    str(root_tactic_contract_status.get("verdict") or "")
                                    != "root_tactic_no_helper_dependencies"
                                ),
                                verification_certificate=root_verification_certificate(
                                    accepted=True,
                                    proof=root_tactic.proof,
                                    phase="helper_only_salvage_root_tactic",
                                    turn_index=turn,
                                    target_statement=str(
                                        getattr(conv, "goal_statement", "") or ""
                                    ),
                                    replay_helpers=replay_helpers,
                                    helper_names=helper_names,
                                    output=str(
                                        (success_attempt or {}).get("output")
                                        or (success_attempt or {}).get("output_preview")
                                        or ""
                                    ),
                                    source="legacy_helper_only_salvage_root_tactic",
                                ),
                                require_verification_certificate=True,
                            )
                            if finalization.accepted:
                                return True, root_tactic.proof
                        if root_tactic.ok and root_tactic.proof:
                            replay_helpers = dossier.verified_helper_blocks()
                            helper_names = _helper_names_from_blocks(replay_helpers)
                            dossier.record_attempt(
                                phase="helper_only_salvage_root_tactic",
                                turn_index=turn,
                                proof=root_tactic.proof,
                                helper_names=helper_names,
                                verdict="root_route_contract_not_ready",
                                metadata={
                                    "route_assembly_contract_status": (
                                        root_tactic_contract_status
                                    ),
                                },
                            )
                    _drop_last_assistant_if_content(conv, content)
                    conv.append_user(
                        "The controller verified helper declaration(s) from your "
                        "reply. Now submit the main proof that assembles the root "
                        "from those named helpers."
                    )
                    continue
            construction_collapse = (
                _detect_known_answer_no_construction_collapse(
                    content,
                    helpers,
                    None,
                    goal_statement=conv.goal_statement,
                )
                if bool(getattr(conv, "opaque_mode", True))
                and bool(getattr(conv, "suppress_solution_placeholders", True))
                else None
            )
            if construction_collapse is not None:
                reason = str(construction_collapse.get("reason") or "").strip()
                match = str(construction_collapse.get("match") or "").strip()
                _trace(
                    trace_prefix,
                    "  detected no-proof construction collapse; forcing graph decomposition.",
                )
                proof_state_update = None
                if proof_state is not None:
                    proof_state_update = proof_state.record_construction_collapse(
                        phase=conv.role,
                        turn_index=turn,
                        reason=reason,
                        proof_preview="",
                        response_preview=content,
                    )
                    if dossier is not None:
                        proof_state.sync_to_graph(
                            dossier,
                            phase="proof_state_construction_collapse",
                            turn_index=turn,
                        )
                _banked = _bank_helpers_as_proposed(
                    dossier,
                    helpers,
                    phase=str(conv.role or "prove"),
                    turn_index=turn,
                    goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                    allow_helper_decomposition=can_bank_turn_proposals,
                )
                if recorder is not None:
                    record = {
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": None,
                        "collapse_reason": reason,
                        "collapse_match": match,
                        "proof_state_update": proof_state_update,
                        "banked_proposed_helpers": list(_banked),
                        "verdict": "known_answer_no_construction_collapse",
                    }
                    if proof_state is not None:
                        record["proof_state"] = proof_state.to_record()
                    recorder.record_turn(record)
                _drop_last_assistant_if_content(conv, content)
                conv.append_user(
                    "Controller detected known-answer/no-construction collapse "
                    "without a Lean proof block. Stop describing why the root is "
                    "large. Submit one active-goal Lean proof attempt next; any "
                    "named helper theorem/lemma declarations in that block must "
                    "be fully proved before the final proof body."
                )
                continue
            _trace(
                trace_prefix,
                "  no main `by`/`example` block found; asking again.",
            )
            # Bank the helper proposals into the dossier so downstream
            # phases (most importantly the recursive planner) can seed
            # claims from the prover's own decomposition signal instead of
            # asking the LLM to re-invent helpers it already named.
            banked_proposed_names: List[str] = []
            if dossier is not None:
                # Mirror the lemma_dag_candidate_helpers fallback used at
                # line ~6757 so banking sees helpers the lemma-DAG
                # extractor recovers when the primary extractor missed
                # them. Without this, no_proof turns whose helpers were
                # extracted only via the lemma-DAG fallback would not
                # be banked. (Adversarial-review 2026-05-13.)
                bankable_sources = list(helpers or ())
                if not bankable_sources:
                    bankable_sources = list(lemma_dag_candidate_helpers or ())
                banked_proposed_names = _bank_helpers_as_proposed(
                    dossier,
                    bankable_sources,
                    phase=str(conv.role or "prove"),
                    turn_index=turn,
                    goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                    allow_helper_decomposition=can_bank_turn_proposals,
                )
                if banked_proposed_names:
                    _trace(
                        trace_prefix,
                        f"  banked {len(banked_proposed_names)} proposed helper(s) "
                        f"for the recursive planner: {banked_proposed_names[:6]}",
                    )
            no_proof_target_integrity = _legacy_no_proof_target_integrity_metadata(
                conv=conv,
                dossier=dossier,
                recorder=recorder,
                llm_output=content,
                phase=str(conv.role or "prove"),
                turn=turn,
                model_id=model_id,
                common_record={
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                },
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": None,
                    "rejection_reason": "no_main_proof",
                    "post_main_declarations": [],
                    "banked_proposed_helpers": list(banked_proposed_names),
                    **no_proof_target_integrity,
                    "verdict": "no_proof_extracted",
                })
            try:
                no_proof_responses = list(
                    getattr(conv, "_no_proof_llm_responses", []) or []
                )
                no_proof_responses.append(content)
                setattr(conv, "_no_proof_llm_responses", no_proof_responses[-8:])
                if not str(getattr(conv, "_last_no_proof_llm_response", "") or ""):
                    setattr(conv, "_last_no_proof_llm_response", content)
            except Exception:
                pass
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                _format_no_proof_extracted_feedback(
                    helpers=helpers,
                    lemma_dag_candidate_helpers=lemma_dag_candidate_helpers,
                    role=str(conv.role or "prove"),
                    banked_names=banked_proposed_names,
                )
            )
            continue

        if helpers:
            _trace(trace_prefix, f"  extracted {len(helpers)} helper(s) + main proof ({len(proof)} chars).")
            for i, h in enumerate(helpers, 1):
                _trace(trace_prefix, f"    helper {i} ({len(h)} chars): {h.splitlines()[0][:120]}")
        else:
            _trace(trace_prefix, f"  extracted main proof ({len(proof)} chars), no helpers.")

        context_helpers = _verified_helper_blocks_for_proof(str(proof or ""))
        correction_names = [
            name
            for helper in helpers
            if (name := helper_decl_name(helper))
            and (existing := dossier.verified_helpers.get(name)) is not None
            and verified_helper_surface_statement_changed(
                existing,
                SimpleNamespace(source=helper),
            )
        ] if dossier is not None else []
        if dossier is not None:
            correction_recheck = merge_helpers_for_correction_recheck(
                dossier,
                context_helpers,
                helpers,
                correction_names,
            )
            check_lemmas = list(correction_recheck.check_lemmas)
            stale_dependents_by_correction = dict(
                correction_recheck.stale_dependents_by_correction
            )
            context_helpers = list(correction_recheck.context_helpers)
            lean_verification_helpers = list(
                correction_recheck.verification_helpers
            )
            correction_recheck_fallback_lemmas = (
                correction_recheck.fallback_check_lemmas
            )
            correction_recheck_fallback_context_helpers = (
                correction_recheck.fallback_context_helpers
            )
        else:
            check_lemmas = merge_context_helpers(context_helpers, helpers)
            stale_dependents_by_correction = {}
            lean_verification_helpers = list(helpers)
            correction_recheck_fallback_lemmas = None
            correction_recheck_fallback_context_helpers = None
        if context_helpers:
            _trace(
                trace_prefix,
                f"  using {len(context_helpers)} verified dossier helper(s) "
                "in Lean context.",
            )

        forbidden_command = _find_forbidden_lean_command(helpers, proof)
        if forbidden_command is not None:
            _trace(
                trace_prefix,
                f"  rejected Lean block containing forbidden command: {forbidden_command!r}",
            )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "dossier_context_helpers": context_helpers,
                    "replay_helpers": context_helpers,
                    "rejection_reason": "forbidden_lean_command",
                    "rejection_match": forbidden_command,
                    "banked_proposed_helpers": list(_banked),
                    "verdict": "proof_policy_rejected",
                })
            check_hint = (
                "Use the `check_lean` tool for #check queries."
                if lean_check_tool_enabled
                else "Do not include #check queries in proof submissions."
            )
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                "Your Lean block contains a top-level command "
                f"({forbidden_command!r}). The proof block may contain helper "
                "declarations and the main proof only; do not use `#eval`, "
                "`#check`, `#print`, `import`, or `axiom` commands in proof "
                f"submissions. {check_hint}"
            )
            continue

        construction_collapse = (
            _detect_known_answer_no_construction_collapse(
                content,
                check_lemmas,
                proof,
                goal_statement=conv.goal_statement,
            )
            if bool(getattr(conv, "opaque_mode", True))
            and bool(getattr(conv, "suppress_solution_placeholders", True))
            else None
        )
        if construction_collapse is not None:
            reason = str(construction_collapse.get("reason") or "").strip()
            match = str(construction_collapse.get("match") or "").strip()
            _trace(
                trace_prefix,
                "  detected known-answer/no-construction collapse; forcing graph decomposition.",
            )
            proof_state_update = None
            if proof_state is not None:
                proof_state_update = proof_state.record_construction_collapse(
                    phase=conv.role,
                    turn_index=turn,
                    reason=reason,
                    proof_preview=str(proof or ""),
                    response_preview=content,
                )
                if dossier is not None:
                    proof_state.sync_to_graph(
                        dossier,
                        phase="proof_state_construction_collapse",
                        turn_index=turn,
                    )
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            if recorder is not None:
                record = {
                        "phase": conv.role,
                        "turn_in_phase": turn,
                        "model": model_id,
                        **repair_self_check_record_fields,
                        "tool_calls_used": tool_calls_used,
                        "tool_call_log": tool_call_log,
                        "messages_sent": sent_messages,
                        "llm_response": content,
                        "llm_elapsed_s": llm_elapsed,
                        "extracted_helpers": helpers,
                        "extracted_proof": proof,
                        "dossier_context_helpers": context_helpers,
                        "replay_helpers": check_lemmas,
                        "collapse_reason": reason,
                        "collapse_match": match,
                        "proof_state_update": proof_state_update,
                        "banked_proposed_helpers": list(_banked),
                        "verdict": "known_answer_no_construction_collapse",
                }
                if proof_state is not None:
                    record["proof_state"] = proof_state.to_record()
                recorder.record_turn(record)
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(
                "Controller detected known-answer/no-construction collapse: "
                "you gave no durable helper lemma construction and only a no-op "
                "root tactic. Retry the root proof with a concrete mathematical "
                "construction. In the next Lean block, submit one active-goal "
                "proof attempt. Do not submit unproved intermediate facts as "
                "local placeholders; if an intermediate fact will not close, "
                "prove it locally or pivot instead of stopping at prose."
            )
            continue

        # Bonus #7 fix: reuse the memoized extraction from the top of
        # the per-turn block (the proof-extracted branch shares the
        # same content as the no-proof branch above).
        lemma_dag_candidate_helpers = helpers or _lemma_dag_extracted_from_content
        # D2 gate-side fix (2026-05-09): open task if sorry-stub helpers
        # are present so the lemma-DAG path proceeds.
        if (
            lemma_dag_candidate_helpers
            and proof_state is not None
            and dossier is not None
            and turn_giveup is None
            and bool(getattr(conv, "allow_helper_decomposition", True))
            and not proof_state.has_open_decomposition_task()
        ):
            from ensemble_prover.proof_state_executor import (
                ensure_decomposition_task_open_for_lemma_dag_candidates,
            )
            lemma_dag_open_attempt = ensure_decomposition_task_open_for_lemma_dag_candidates(
                proof_state,
                lemma_dag_candidate_helpers,
                source=f"lemma_dag_helpers_volunteered:legacy_pre_lean:turn={turn}",
            )
        else:
            lemma_dag_open_attempt = {}
        if (
            lemma_dag_candidate_helpers
            and proof_state is not None
            and dossier is not None
            and turn_giveup is None
            and bool(getattr(conv, "allow_helper_decomposition", True))
            and not proof_state.has_open_decomposition_task()
        ):
            open_reason = str(
                (lemma_dag_open_attempt or {}).get("reason") or "not_open"
            )
            _trace(
                trace_prefix,
                "  lemma-DAG candidates available but no decomposition task "
                f"could be opened ({open_reason}); skipping. "
                f"({len(lemma_dag_candidate_helpers)} candidate(s).)",
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "lemma_dag_candidate_count": len(lemma_dag_candidate_helpers),
                    "lemma_dag_open_attempt": dict(lemma_dag_open_attempt or {}),
                    "verdict": "lemma_dag_no_decomposition_task_opened",
                })
        if (
            lemma_dag_candidate_helpers
            and proof_state is not None
            and dossier is not None
            and turn_giveup is None
            and bool(getattr(conv, "allow_helper_decomposition", True))
            and proof_state.has_open_decomposition_task()
        ):
            await _try_proof_state_lemma_dag_helpers(
                conv=conv,
                lean=lean,
                dossier=dossier,
                proof_state=proof_state,
                helpers=lemma_dag_candidate_helpers,
                recorder=recorder,
                trace_prefix=trace_prefix,
                turn=turn,
                timeout_s=proof_state_child_tactic_timeout_s,
                proof_cache=proof_cache,
            )
            proof_state.sync_to_graph(
                dossier,
                phase="proof_state_lemma_dag_decomposition",
                turn_index=turn,
            )
        elif lemma_dag_candidate_helpers and (
            turn_giveup is not None
            or not bool(getattr(conv, "allow_helper_decomposition", True))
        ):
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "lemma_dag_candidate_count": len(lemma_dag_candidate_helpers),
                    "giveup_cluster": (
                        turn_giveup["cluster"] if turn_giveup is not None else None
                    ),
                    "giveup_match": (
                        turn_giveup["match"] if turn_giveup is not None else ""
                    ),
                    "verdict": (
                        "pre_lean_lemma_dag_suppressed_by_giveup"
                        if turn_giveup is not None
                        else "pre_lean_lemma_dag_suppressed_proof_only"
                    ),
                })

        _trace(trace_prefix, "  checking with Lean...")
        lean_started = time.monotonic()
        lean_error: Optional[str] = None
        result = None
        submitted_proof = proof
        proof_for_checks = str(proof or "")
        primary_source = "submitted"
        accepted = False
        feedback_result = None
        lean_feedback_source = "primary_check"
        lean_feedback_error: Optional[str] = None
        lean_feedback_elapsed: Optional[float] = None
        try:
            from ensemble_prover.mini_session.turn.lean_check import verify_with_lean

            lean_verdict = await verify_with_lean(
                conv=conv,
                lean=lean,
                proof=proof,
                helpers=lean_verification_helpers,
                context_helpers=context_helpers,
                check_lemmas=check_lemmas,
                active_root_targets=_framed_active_root_targets_for_conversation(
                    dossier,
                    conv,
                    helper_blocks=context_helpers,
                ),
            )
            if (
                not bool(lean_verdict.accepted)
                and correction_recheck_fallback_lemmas is not None
                and correction_recheck_fallback_context_helpers is not None
            ):
                context_helpers = list(
                    correction_recheck_fallback_context_helpers
                )
                check_lemmas = list(correction_recheck_fallback_lemmas)
                lean_verification_helpers = list(helpers)
                lean_verdict = await verify_with_lean(
                    conv=conv,
                    lean=lean,
                    proof=proof,
                    helpers=lean_verification_helpers,
                    context_helpers=context_helpers,
                    check_lemmas=check_lemmas,
                    active_root_targets=_framed_active_root_targets_for_conversation(
                        dossier,
                        conv,
                        helper_blocks=context_helpers,
                    ),
                )
            accepted = bool(lean_verdict.accepted)
            result = (
                lean_verdict.safe_result
                if accepted and lean_verdict.safe_result is not None
                else lean_verdict.primary_result
            )
            proof_for_checks = lean_verdict.accepted_proof or proof_for_checks
            primary_source = lean_verdict.primary_source
            feedback_result = lean_verdict.feedback_result
            lean_feedback_source = lean_verdict.feedback_source
            lean_feedback_error = lean_verdict.lean_feedback_error
            lean_feedback_elapsed = lean_verdict.safe_elapsed_s
            lean_elapsed = lean_verdict.primary_elapsed_s
        except Exception as exc:
            lean_error = f"{type(exc).__name__}: {exc}"
            _trace(trace_prefix, f"  Lean check raised: {lean_error}")
            lean_elapsed = round(time.monotonic() - lean_started, 3)

        if lean_error is not None or result is None:
            _banked = _bank_helpers_as_proposed(
                dossier,
                helpers,
                phase=str(conv.role or "prove"),
                turn_index=turn,
                goal_statement=str(getattr(conv, "goal_statement", "") or ""),
                allow_helper_decomposition=can_bank_turn_proposals,
            )
            if turn_giveup is not None:
                infra_feedback = _with_turn_budget_footer(
                    _giveup_decomposition_nudge(
                        turn_giveup["cluster"],
                        opaque_mode=bool(getattr(conv, "opaque_mode", False)),
                        allow_official_answer_visibility=bool(
                            getattr(
                                conv,
                                "allow_official_answer_visibility",
                                False,
                            )
                        ),
                        official_answer_payload_present=getattr(
                            conv,
                            "official_answer_payload_present",
                            None,
                        ),
                        allow_helper_decomposition=bool(
                            getattr(conv, "allow_helper_decomposition", True)
                        ),
                        matched_phrase=turn_giveup["match"],
                        recursion_depth=0,
                        max_recursion_depth=3,
                        role=conv.role,
                    ),
                    role=conv.role,
                    turn=turn,
                    max_turns=turn_limit,
                )
            else:
                infra_feedback = (
                    f"Lean infrastructure error: {lean_error}\n\n"
                    "Try a different approach."
                )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "dossier_context_helpers": context_helpers,
                    "replay_helpers": check_lemmas,
                    "lean_error": lean_error,
                    "lean_elapsed_s": lean_elapsed,
                    "banked_proposed_helpers": list(_banked),
                    "giveup_cluster": (
                        turn_giveup["cluster"] if turn_giveup is not None else None
                    ),
                    "giveup_match": (
                        turn_giveup["match"] if turn_giveup is not None else ""
                    ),
                    "banking_suppressed_by_giveup": bool(turn_giveup),
                    "lean_feedback_mode": (
                        "giveup_active_proof_redirect"
                        if turn_giveup is not None
                        else "infra_error"
                    ),
                    "verdict": "lean_infra_error",
                })
            if turn_giveup is not None:
                _drop_last_assistant_if_content(conv, content)
            conv.append_user(infra_feedback)
            continue

        if accepted:
            if proof_for_checks != proof:
                proof = proof_for_checks
            _trace(trace_prefix, f"  ✓ Lean accepted ({lean_elapsed}s). Proof found.")
            helper_names = _helper_names_from_blocks(check_lemmas)
            if dossier is not None:
                checked_helper_sources = set(check_lemmas)
                semantic_replacement_names: List[str] = []
                for helper in helpers:
                    name = helper_decl_name(helper)
                    if not name or helper not in checked_helper_sources:
                        continue
                    prior_helper = dossier.verified_helpers.get(name)
                    checked_index = check_lemmas.index(helper)
                    helper_replay_context_names = _helper_names_from_blocks(
                        check_lemmas[:checked_index]
                    )
                    helper_record = dossier.record_verified_helper(
                        helper,
                        phase=conv.role,
                        turn_index=turn,
                        replay_context_names=helper_replay_context_names,
                        replace_existing_same_name=True,
                    )
                    if helper_record is None:
                        continue
                    if (
                        prior_helper is not None
                        and verified_helper_semantic_statement_changed(
                            prior_helper,
                            helper_record,
                        )
                    ):
                        semantic_replacement_names.append(name)
                    if proof_cache is not None:
                        store_verified_helper_for_dossier(
                            proof_cache,
                            helper,
                            preamble=_proof_state_check_preamble(conv),
                            dossier=dossier,
                            phase=conv.role,
                        )
                if semantic_replacement_names:
                    stale_dependents = set().union(
                        *(
                            stale_dependents_by_correction.get(name, set())
                            for name in semantic_replacement_names
                        )
                    )
                    checked_names = set(_helper_names_from_blocks(check_lemmas))
                    checked_sources = {
                        helper_decl_name(block) or "": block
                        for block in check_lemmas
                        if helper_decl_name(block)
                    }
                    for stale_name in sorted(stale_dependents - checked_names):
                        dossier.remove_verified_helper(stale_name)
                    for stale_name in sorted(stale_dependents & checked_names):
                        recorded = dossier.verified_helpers.get(stale_name)
                        if str(getattr(recorded, "source", "") or "") != str(
                            checked_sources.get(stale_name, "") or ""
                        ):
                            dossier.remove_verified_helper(stale_name)
                    for replacement_name in semantic_replacement_names:
                        refresh_revalidated_dependent_support_hashes(
                            dossier,
                            replacement_name,
                        )
                    for stale_name in sorted(stale_dependents & checked_names):
                        if stale_name not in dossier.verified_helpers:
                            continue
                        integrity = dossier.root_replay_integrity_status(
                            helper_names=[stale_name]
                        )
                        if not bool(integrity.get("ready")):
                            dossier.remove_verified_helper(stale_name)
                from ensemble_prover.root_finalization import (
                    finalize_root_solution,
                    root_verification_certificate,
                )

                finalization = finalize_root_solution(
                    dossier=dossier,
                    proof_state=proof_state,
                    proof=proof,
                    replay_helpers=check_lemmas,
                    helper_names=helper_names,
                    phase=conv.role,
                    turn_index=turn,
                    target_statement=str(
                        getattr(dossier, "root_statement", "")
                        or getattr(conv, "goal_statement", "")
                        or ""
                    ),
                    verification_certificate=root_verification_certificate(
                        accepted=True,
                        proof=proof,
                        phase=conv.role,
                        turn_index=turn,
                        target_statement=str(
                            getattr(dossier, "root_statement", "")
                            or getattr(conv, "goal_statement", "")
                            or ""
                        ),
                        replay_helpers=check_lemmas,
                        helper_names=helper_names,
                        output=str(getattr(result, "output", "") or ""),
                        source="legacy_conversation_turn",
                    ),
                    require_verification_certificate=True,
                )
                if not finalization.accepted:
                    if recorder is not None:
                        recorder.record_turn({
                            "phase": conv.role,
                            "turn_in_phase": turn,
                            "lean_ok": True,
                            "lean_output": result.output,
                            "lean_elapsed_s": lean_elapsed,
                            "root_finalization_verdict": finalization.verdict,
                            "verdict": "root_finalization_blocked",
                        })
                    return False, None
                proof = finalization.proof or proof
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "max_turns_base": max_turns,
                    "turn_limit_effective": turn_limit,
                    "policy_repair_redirect_bonus_turn": turn > max_turns,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": submitted_proof,
                    "accepted_proof": proof
                    if primary_source == "active_root_lift"
                    else None,
                    "accepted_proof_source": primary_source,
                    "dossier_context_helpers": context_helpers,
                    "replay_helpers": check_lemmas,
                    "lean_ok": True,
                    "lean_output": result.output,
                    "lean_elapsed_s": lean_elapsed,
                    "verdict": "solved",
                })
            return True, proof

        if feedback_result is not None:
            err = (feedback_result.output or "").strip() or "(no output)"
        else:
            err = (
                "answer-safe Lean feedback unavailable; raw checker-preamble "
                "output suppressed"
            )
        _trace(
            trace_prefix,
            f"  ✗ Lean rejected ({lean_elapsed}s). Feedback output ({len(err)} chars):",
        )
        print(_indent(err[:1200], trace_prefix + "    "), flush=True)
        if len(err) > 1200:
            _trace(trace_prefix, f"    ...({len(err) - 1200} more chars)")

        if feedback_result is not None:
            lean_failure_analysis = _analyze_lean_failure(feedback_result)
        else:
            note = (
                "answer-safe Lean feedback check accepted while the full check "
                "rejected; avoid relying on `_solution` unfolding"
                if lean_feedback_source
                in {"answer_safe_check_accepted", "primary_check_with_answer_safe_pass"}
                else "answer-safe Lean feedback check failed; checker-preamble output was suppressed"
            )
            lean_failure_analysis = _manual_lean_failure_analysis(
                "answer_safe_feedback_unavailable",
                note,
            )
        synthetic_active_root_lift_feedback = _is_active_root_lift_feedback_source(
            lean_feedback_source
        )

        repair_retrieval_block = ""
        repair_retrieval_record: Optional[Dict[str, Any]] = None
        if (
            repair_retrieval_enabled
            and searcher is not None
            and not synthetic_active_root_lift_feedback
            and not raw_feedback
        ):
            repair_retrieval_block, repair_retrieval_record = (
                await _retrieve_repair_candidates_async(
                    searcher,
                    conv,
                    lean_failure_analysis,
                    max_results=repair_retrieval_top_k,
                    goal_statement_override=(
                        active_root_target_statement(
                            dossier,
                            require_single=True,
                            require_no_hypotheses=False,
                            include_hypotheses=True,
                        )
                        or conv.goal_statement
                    ),
                    timeout_s=float(
                        getattr(searcher, "operation_timeout_s", 30.0) or 30.0
                    ),
                    redact_solution_refs=(
                        _conversation_should_redact_solution_refs(conv)
                    ),
                )
            )
            if repair_retrieval_record:
                _trace(
                    trace_prefix,
                    "  repair retrieval query "
                    f"({repair_retrieval_record.get('result_count', 0)} hit(s)): "
                    f"{str(repair_retrieval_record.get('query', ''))[:160]!r}",
                )

        helper_names = _helper_names_from_blocks(check_lemmas)
        if dossier is not None:
            dossier.record_attempt(
                phase=conv.role,
                turn_index=turn,
                proof=proof,
                helper_names=helper_names,
                verdict="lean_rejected",
                error_type=str(lean_failure_analysis.get("error_type") or ""),
            )

        proof_state_update: Optional[Dict[str, Any]] = None
        proof_state_retrieval: List[Dict[str, Any]] = []
        proof_state_helpers: List[str] = []
        if proof_state is not None and not synthetic_active_root_lift_feedback:
            proof_state_update = proof_state.record_failure(
                phase=conv.role,
                turn_index=turn,
                analysis=lean_failure_analysis,
                repair_retrieval=repair_retrieval_record,
            )
            node_retrieval_top_k = max(
                0,
                min(6, int(repair_retrieval_top_k or 0)),
            )
            local_helper_blocks = (
                dossier.verified_helper_blocks()
                if dossier is not None
                else ()
            )
            retrieval_searcher = searcher if repair_retrieval_enabled else None
            if node_retrieval_top_k <= 0 and local_helper_blocks:
                node_retrieval_top_k = 3
            if (
                (retrieval_searcher is not None or local_helper_blocks)
                and node_retrieval_top_k > 0
            ):
                proof_state_retrieval = await _retrieve_proof_state_node_candidates_async(
                    retrieval_searcher,
                    proof_state,
                    max_nodes=proof_state_child_goal_limit,
                    max_results=node_retrieval_top_k,
                    local_helper_blocks=local_helper_blocks,
                    timeout_s=float(
                        getattr(retrieval_searcher, "operation_timeout_s", 30.0)
                        if retrieval_searcher is not None
                        else 30.0
                    ),
                )
                for retrieval in proof_state_retrieval:
                    _trace(
                        trace_prefix,
                        "  proof-state retrieval "
                        f"{retrieval.get('node_id')}: "
                        f"{retrieval.get('result_count', 0)} hit(s)",
                    )
            proof_state.sync_to_graph(
                dossier,
                phase="proof_state_update",
                turn_index=turn,
            )
            if recorder is not None:
                recorder.record_turn(
                    {
                        "phase": "proof_state_update",
                        "turn_in_phase": turn,
                        "update": proof_state_update,
                        "node_retrieval": proof_state_retrieval,
                        "proof_state": proof_state.to_record(),
                        "verdict": "proof_state_updated",
                    }
                )
            if proof_state_child_tactics_enabled and turn_giveup is None:
                (
                    state_ok,
                    state_proof,
                    proof_state_helpers,
                ) = await _try_proof_state_child_closures(
                    conv=conv,
                    lean=lean,
                    dossier=dossier,
                    proof_state=proof_state,
                    recorder=recorder,
                    trace_prefix=trace_prefix,
                    turn=turn,
                    timeout_s=proof_state_child_tactic_timeout_s,
                    max_candidates=proof_state_child_tactic_max_candidates,
                    max_nodes=proof_state_child_goal_limit,
                    max_decl_applications=proof_state_decl_application_limit,
                    batch_parallelism=proof_state_batch_parallelism,
                    proof_cache=proof_cache,
                )
                proof_state.sync_to_graph(
                    dossier,
                    phase="proof_state_child_closure",
                    turn_index=turn,
                )
                if state_ok and state_proof:
                    if recorder is not None:
                        recorder.record_turn(
                            {
                                "phase": conv.role,
                                "turn_in_phase": turn,
                                "model": model_id,
                                **repair_self_check_record_fields,
                                "tool_calls_used": tool_calls_used,
                                "tool_call_log": tool_call_log,
                                "messages_sent": sent_messages,
                                "llm_response": content,
                                "llm_elapsed_s": llm_elapsed,
                                "extracted_helpers": helpers,
                                "extracted_proof": proof,
                                "dossier_context_helpers": context_helpers,
                                "replay_helpers": check_lemmas,
                                "lean_ok": False,
                                "lean_output": err,
                                "lean_failure_analysis": lean_failure_analysis,
                                "lean_feedback_source": lean_feedback_source,
                                "lean_feedback_mode": "proof_state_child_solved",
                                "repair_retrieval": repair_retrieval_record,
                                "proof_state_update": proof_state_update,
                                "proof_state_retrieval": proof_state_retrieval,
                                "proof_state_helpers": proof_state_helpers,
                                "lean_elapsed_s": lean_elapsed,
                                "verdict": "solved_after_proof_state_child",
                            }
                        )
                    return True, state_proof

        if turn_giveup is not None:
            lean_feedback = _with_turn_budget_footer(
                _giveup_decomposition_nudge(
                    turn_giveup["cluster"],
                    opaque_mode=bool(getattr(conv, "opaque_mode", False)),
                    allow_official_answer_visibility=bool(
                        getattr(conv, "allow_official_answer_visibility", False)
                    ),
                    official_answer_payload_present=getattr(
                        conv,
                        "official_answer_payload_present",
                        None,
                    ),
                    matched_phrase=turn_giveup["match"],
                    recursion_depth=0,
                    max_recursion_depth=3,
                    role=str(getattr(conv, "role", "") or "prove"),
                    allow_helper_decomposition=bool(
                        getattr(conv, "allow_helper_decomposition", True)
                    ),
                ),
                role=conv.role,
                turn=turn,
                max_turns=turn_limit,
            )
            if recorder is not None:
                recorder.record_turn({
                    "phase": conv.role,
                    "turn_in_phase": turn,
                    "model": model_id,
                    **repair_self_check_record_fields,
                    "tool_calls_used": tool_calls_used,
                    "tool_call_log": tool_call_log,
                    "messages_sent": sent_messages,
                    "llm_response": content,
                    "llm_elapsed_s": llm_elapsed,
                    "extracted_helpers": helpers,
                    "extracted_proof": proof,
                    "dossier_context_helpers": context_helpers,
                    "replay_helpers": check_lemmas,
                    "lean_ok": False,
                    "lean_output": err,
                    "lean_failure_analysis": lean_failure_analysis,
                    "lean_feedback_source": lean_feedback_source,
                    "lean_feedback_mode": "giveup_active_proof_redirect",
                    "repair_retrieval": repair_retrieval_record,
                    "proof_state_update": proof_state_update,
                    "proof_state_retrieval": proof_state_retrieval,
                    "proof_state_helpers": [],
                    "banked_proposed_helpers": [],
                    "giveup_cluster": turn_giveup["cluster"],
                    "giveup_match": turn_giveup["match"],
                    "banking_suppressed_by_giveup": True,
                    "lean_elapsed_s": lean_elapsed,
                    "verdict": "lean_rejected",
                })
            _drop_last_assistant_if_content(conv, content)
            conv.append_user(lean_feedback)
            continue

        salvage_result = None
        salvage_candidates = list(helpers or lemma_dag_candidate_helpers or [])
        helper_probe_timeout = float(proof_state_child_tactic_timeout_s or 0.0)
        helper_probe_candidates = int(proof_state_child_tactic_max_candidates or 0)
        if salvage_candidates and dossier is not None and helper_probe_timeout > 0.0:
            _trace(trace_prefix, "  attempting answer-safe helper salvage...")
            from ensemble_prover.helper_salvage import collect_open_child_targets

            salvager = HelperSalvager(
                lean,
                preamble=_proof_state_check_preamble(conv),
                answer_safe_preamble=str(getattr(conv, "preamble", "") or ""),
                timeout_s=helper_probe_timeout,
                relevance_gate_root_statement=str(
                    getattr(dossier, "root_statement", "") or ""
                ),
                relevance_gate_open_targets=collect_open_child_targets(proof_state),
            )
            salvage_result = await salvager.salvage(
                salvage_candidates,
                dossier=dossier,
                phase=conv.role,
                turn_index=turn,
            )
            invalidated_helpers = [
                *list(getattr(salvage_result, "replaced", []) or []),
                *list(getattr(salvage_result, "evicted", []) or []),
            ]
            if invalidated_helpers and proof_state is not None:
                try:
                    proof_state.reconcile_with_dossier(dossier)
                    proof_state.invalidate_assembly_contracts_for_helpers(
                        invalidated_helpers,
                        phase=conv.role,
                        turn_index=turn,
                        conservative=True,
                    )
                except Exception:
                    pass
            if salvage_result.accepted:
                _trace(
                    trace_prefix,
                    "  salvaged helper(s): "
                    + ", ".join(salvage_result.accepted),
                )
                if proof_cache is not None:
                    for helper_name in salvage_result.accepted:
                        helper_record = dossier.verified_helpers.get(helper_name)
                        if helper_record is not None:
                            store_verified_helper_for_dossier(
                                proof_cache,
                                helper_record.source,
                                preamble=_proof_state_check_preamble(conv),
                                dossier=dossier,
                                phase=f"{conv.role}:helper_salvage",
                            )
                if proof_state is not None and proof_state_child_tactics_enabled:
                    (
                        state_ok,
                        state_proof,
                        salvaged_state_helpers,
                    ) = await _try_proof_state_salvaged_helper_assembly(
                        conv=conv,
                        lean=lean,
                        dossier=dossier,
                        proof_state=proof_state,
                        helper_names=salvage_result.accepted,
                        recorder=recorder,
                        trace_prefix=trace_prefix,
                        turn=turn,
                        timeout_s=helper_probe_timeout,
                        max_nodes=proof_state_child_goal_limit,
                        proof_cache=proof_cache,
                        phase="helper_salvage",
                    )
                    proof_state_helpers.extend(salvaged_state_helpers)
                    proof_state.sync_to_graph(
                        dossier,
                        phase="helper_salvage_proof_state_assembly",
                        turn_index=turn,
                    )
                    if state_ok and state_proof:
                        if recorder is not None:
                            recorder.record_turn(
                                {
                                    "phase": "helper_salvage_proof_state_assembly",
                                    "turn_in_phase": turn,
                                    **repair_self_check_record_fields,
                                    "accepted_helpers": list(salvaged_state_helpers),
                                    "proof_state": proof_state.to_record(),
                                    "verdict": "solved_after_helper_salvage",
                                }
                            )
                        return True, state_proof
                root_tactic = None
                if helper_probe_candidates > 0:
                    # B3 fix (2026-05-08): see helper-only-reply path above.
                    # The post-failure salvage cascade must use the same
                    # preamble as the proof-state assembly arm.
                    helper_blocks = _root_tactic_helper_blocks_for_names(
                        salvage_result.accepted
                    )
                    root_tactic = await try_close_root_with_active_lift(
                        lean=lean,
                        goal_statement=conv.goal_statement,
                        preamble=_proof_state_acceptance_preamble(conv),
                        helpers=helper_blocks,
                        active_root_targets=tuple(
                            item
                            for item in list(getattr(dossier, "active_root_targets", []) or ())
                            if isinstance(item, dict)
                        ),
                        active_root_frame_helper_blocks=dossier.verified_helper_blocks(),
                        timeout_s=helper_probe_timeout,
                        max_candidates=max(1, helper_probe_candidates),
                        suppress_solution_placeholders=bool(
                            getattr(conv, "suppress_solution_placeholders", True)
                        ),
                        opaque_mode=bool(getattr(conv, "opaque_mode", True)),
                        allow_official_answer_visibility=bool(
                            getattr(conv, "allow_official_answer_visibility", False)
                        ),
                        official_answer_payload_present=getattr(
                            conv,
                            "official_answer_payload_present",
                            getattr(dossier, "official_answer_payload_present", None),
                        ),
                        tactic_source_suppression_records=tactic_source_suppression_records,
                        tactic_source_suppression_helper_blocks=helper_blocks,
                        tactic_closer=try_close_with_tactics,
                        attempt_observer=dossier_lean_attempt_observer(
                            dossier,
                            "salvage_root_tactic",
                        ),
                    )
                if root_tactic is None:
                    root_tactic = SimpleNamespace(
                        ok=False,
                        proof=None,
                        attempts=[],
                        candidate_count=0,
                        elapsed_s=0.0,
                        exit_reason="tactic_budget_disabled",
                    )
                success_attempt = next(
                    (
                        attempt
                        for attempt in root_tactic.attempts
                        if isinstance(attempt, dict) and attempt.get("ok")
                    ),
                    None,
                )
                root_tactic_record = {
                    "phase": "helper_salvage_root_tactic",
                    "turn_in_phase": turn,
                    **repair_self_check_record_fields,
                    "accepted_helpers": list(salvage_result.accepted),
                    "tactic_candidate_count": root_tactic.candidate_count,
                    **tactic_attempt_telemetry_fields(root_tactic.attempts),
                    "tactic_attempts": root_tactic.attempts[:10],
                    "tactic_success_attempt": success_attempt,
                    "tactic_success_index": (
                        success_attempt.get("index") if success_attempt else None
                    ),
                    "tactic_elapsed_s": root_tactic.elapsed_s,
                    "tactic_exit_reason": root_tactic.exit_reason,
                    "active_root_target_statement": dict(
                        getattr(root_tactic, "cache_metadata", {}) or {}
                    ).get("active_root_target_statement"),
                    "active_root_lift_attempted": bool(
                        dict(getattr(root_tactic, "cache_metadata", {}) or {}).get(
                            "active_root_lift_attempted"
                        )
                    ),
                    "active_root_lift_succeeded": bool(
                        dict(getattr(root_tactic, "cache_metadata", {}) or {}).get(
                            "active_root_lift_succeeded"
                        )
                    ),
                    "verdict": (
                        "tactic_solved"
                        if root_tactic.ok
                        else (
                            "tactic_skipped"
                            if root_tactic.exit_reason == "tactic_budget_disabled"
                            else "tactic_rejected"
                        )
                    ),
                }
                root_tactic_contract_status: Dict[str, Any] = {}
                if root_tactic.ok and root_tactic.proof:
                    root_tactic_contract_status = root_tactic_success_contract_status(
                        dossier,
                        proof=root_tactic.proof,
                        helper_blocks=helper_blocks,
                        success_attempt=success_attempt,
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        target_statement=conv.goal_statement,
                    )
                    root_tactic_record["route_assembly_contract_status"] = (
                        root_tactic_contract_status
                    )
                    if not bool(root_tactic_contract_status.get("ready")):
                        root_tactic_record["verdict"] = (
                            "root_route_contract_not_ready"
                        )
                        root_tactic_record["route_contract_verdict"] = str(
                            root_tactic_contract_status.get("verdict") or ""
                        )
                if recorder is not None:
                    recorder.record_turn(root_tactic_record)
                if not root_tactic.ok:
                    first_attempt = (
                        root_tactic.attempts[0]
                        if root_tactic.attempts
                        and isinstance(root_tactic.attempts[0], dict)
                        else {}
                    )
                    dossier.record_attempt(
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        proof="",
                        helper_names=list(salvage_result.accepted),
                        verdict="tactic_rejected",
                        error_type=str(first_attempt.get("error_type", "") or ""),
                        metadata={
                            "tactic_candidate_count": root_tactic.candidate_count,
                            "tactic_exit_reason": root_tactic.exit_reason,
                        },
                    )
                if (
                    root_tactic.ok
                    and root_tactic.proof
                    and bool(root_tactic_contract_status.get("ready"))
                ):
                    route_helper_names = [
                        str(name or "").strip()
                        for name in list(
                            root_tactic_contract_status.get("helper_names") or []
                        )
                        if str(name or "").strip()
                    ]
                    replay_helpers = _helper_blocks_for_names(
                        helper_blocks,
                        route_helper_names,
                    )
                    if not replay_helpers:
                        replay_helpers = helper_blocks
                    replay_closure = getattr(dossier, "root_replay_helper_closure", None)
                    if callable(replay_closure):
                        closed = replay_closure(
                            replay_helpers=replay_helpers,
                            support_helper_names=route_helper_names,
                        )
                        if closed:
                            replay_helpers = list(closed)
                    helper_names = _helper_names_from_blocks(
                        replay_helpers
                    ) or route_helper_names
                    from ensemble_prover.root_finalization import (
                        finalize_root_solution,
                        root_verification_certificate,
                    )

                    finalization = finalize_root_solution(
                        dossier=dossier,
                        proof_state=proof_state,
                        proof=root_tactic.proof,
                        replay_helpers=replay_helpers,
                        helper_names=helper_names,
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        route_id=str(
                            root_tactic_contract_status.get("route_id")
                            or root_tactic_contract_status.get("created_route_id")
                            or ""
                        ),
                        dependency_node_ids=tuple(
                            str(node_id or "").strip()
                            for node_id in list(
                                root_tactic_contract_status.get("dependency_node_ids")
                                or root_tactic_contract_status.get("required_node_ids")
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
                        # Helper-free closes have no route to bind; requiring a
                        # route contract would reject a Lean-accepted proof.
                        # Match try_root_tactic_close's conditional flag.
                        require_route_contract=(
                            str(root_tactic_contract_status.get("verdict") or "")
                            != "root_tactic_no_helper_dependencies"
                        ),
                        verification_certificate=root_verification_certificate(
                            accepted=True,
                            proof=root_tactic.proof,
                            phase="helper_salvage_root_tactic",
                            turn_index=turn,
                            target_statement=str(
                                getattr(dossier, "root_statement", "")
                                or getattr(conv, "goal_statement", "")
                                or ""
                            ),
                            replay_helpers=replay_helpers,
                            helper_names=helper_names,
                            output=str(
                                (success_attempt or {}).get("output")
                                or (success_attempt or {}).get("output_preview")
                                or ""
                            ),
                            source="legacy_helper_salvage_root_tactic",
                        ),
                        require_verification_certificate=True,
                    )
                    if finalization.accepted:
                        return True, root_tactic.proof
                if root_tactic.ok and root_tactic.proof:
                    replay_helpers = dossier.verified_helper_blocks()
                    helper_names = _helper_names_from_blocks(replay_helpers)
                    dossier.record_attempt(
                        phase="helper_salvage_root_tactic",
                        turn_index=turn,
                        proof=root_tactic.proof,
                        helper_names=helper_names,
                        verdict="root_route_contract_not_ready",
                        metadata={
                            "route_assembly_contract_status": (
                                root_tactic_contract_status
                            ),
                        },
                    )
            elif salvage_result.rejected:
                _trace(
                    trace_prefix,
                    f"  helper salvage rejected {len(salvage_result.rejected)} helper(s).",
                )

        if raw_feedback and feedback_result is not None:
            # A/B path: pass the raw Lean transcript verbatim. We still gate
            # on ``feedback_result`` so the answer-safe contract is preserved
            # — when only the full check has output (full rejected, safe
            # accepted), feedback_result is None and we fall back to the
            # structured ``answer_safe_feedback_unavailable`` hint.
            lean_feedback = _format_raw_lean_feedback(feedback_result)
            lean_feedback_mode = "raw"
        else:
            lean_feedback = _format_lean_failure_feedback(
                lean_failure_analysis,
                search_enabled=searcher is not None,
                check_enabled=lean_check_tool_enabled,
                role=str(getattr(conv, "role", "") or "prove"),
                dossier=dossier,
            )
            lean_feedback = _prepend_repeated_failure_notice(
                lean_feedback,
                conv,
                lean_failure_analysis,
            )
            lean_feedback_mode = (
                "structured_fallback_no_feedback_result"
                if raw_feedback
                else "structured"
            )
        if repair_retrieval_block and not synthetic_active_root_lift_feedback:
            lean_feedback = (
                lean_feedback.rstrip()
                + "\n\n"
                + repair_retrieval_block
            )
        if synthetic_active_root_lift_feedback:
            lean_feedback = _suppress_active_root_lift_feedback_text(lean_feedback)
        lean_feedback = _with_turn_budget_footer(
            lean_feedback,
            role=conv.role,
            turn=turn,
            max_turns=turn_limit,
        )
        if salvage_result is not None and salvage_result.accepted:
            lean_feedback = (
                lean_feedback.rstrip()
                + "\n\n"
                + "Verified helper salvage: the following helper declarations "
                + "compiled in the answer-safe Lean environment and will be "
                + "available in future turns: "
                + ", ".join(
                    f"`{_prompt_safe_inline_text(name, limit=120)}`"
                    for name in salvage_result.accepted
                )
                + "."
            )
        if proof_state_helpers:
            lean_feedback = (
                lean_feedback.rstrip()
                + "\n\n"
                + "Proof-state scheduler proved these child helper(s), but "
                + "root assembly still needs one more step: "
                + ", ".join(
                    f"`{_prompt_safe_inline_text(name, limit=120)}`"
                    for name in proof_state_helpers
                )
                + ". Use them directly in the next root proof."
            )
        banked_proposed_names = _bank_helpers_as_proposed(
            dossier,
            helpers,
            phase=str(conv.role or "prove"),
            turn_index=turn,
            fallback_helpers=lemma_dag_candidate_helpers,
            goal_statement=str(getattr(conv, "goal_statement", "") or ""),
            allow_helper_decomposition=can_bank_turn_proposals,
        )
        if banked_proposed_names:
            _trace(
                trace_prefix,
                f"  banked {len(banked_proposed_names)} proposed helper(s) "
                f"after Lean rejection: {banked_proposed_names[:6]}",
            )
        if recorder is not None:
            recorder.record_turn({
                "phase": conv.role,
                "turn_in_phase": turn,
                "model": model_id,
                **repair_self_check_record_fields,
                "tool_calls_used": tool_calls_used,
                "tool_call_log": tool_call_log,
                "messages_sent": sent_messages,
                "llm_response": content,
                "llm_elapsed_s": llm_elapsed,
                "extracted_helpers": helpers,
                "extracted_proof": proof,
                "dossier_context_helpers": context_helpers,
                "replay_helpers": check_lemmas,
                "lean_ok": False,
                "lean_output": err,
                "lean_failure_analysis": lean_failure_analysis,
                "lean_feedback_source": lean_feedback_source,
                "lean_feedback_mode": lean_feedback_mode,
                "repair_retrieval": repair_retrieval_record,
                "proof_state_update": proof_state_update,
                "proof_state_retrieval": proof_state_retrieval,
                "proof_state_helpers": proof_state_helpers,
                "banked_proposed_helpers": list(banked_proposed_names),
                "lean_feedback_error": lean_feedback_error,
                "lean_feedback_elapsed_s": lean_feedback_elapsed,
                "helper_salvage": (
                    {
                        "accepted": salvage_result.accepted,
                        "rejected": salvage_result.rejected,
                        "skipped": salvage_result.skipped,
                    }
                    if salvage_result is not None
                    else None
                ),
                "lean_elapsed_s": lean_elapsed,
                "verdict": "lean_rejected",
            })
        conv.append_user(
            lean_feedback,
            repair_payload=None
            if synthetic_active_root_lift_feedback
            else _repair_payload_from_failure_analysis(lean_failure_analysis),
        )

    _trace(
        trace_prefix,
        f"[role={conv.role}] exhausted {max_turns} turns without success.",
    )
    return False, None


# ---------------------------------------------------------------------------
# Driver: prove → optional refine.
# ---------------------------------------------------------------------------


def _feedback_lemmas_for_answer_safe_recheck(
    lemmas: Sequence[str],
    conv: Conversation,
) -> List[str]:
    """Return helper context safe for prompt-visible checker feedback."""

    if (
        not _needs_answer_safe_feedback_check(conv)
        or getattr(conv, "official_answer_payload_present", None) is False
    ):
        # When the adapter authoritatively reports that no official-answer
        # payload exists, these are ordinary kernel-verified proof blocks.
        # Axiomatizing them makes an otherwise closed assembly fail the axiom
        # audit merely because the prompt/checker preambles differ for some
        # unrelated reason.
        return [str(item or "") for item in (lemmas or ())]
    return [_axiomatize_helper_for_feedback(str(item or "")) for item in (lemmas or ())]


async def _try_root_tactic_close(
    *,
    phase: str,
    theorem_name: str,
    goal_statement: str,
    preamble: str,
    lean: LeanRunner,
    dossier: ProofDossier,
    recorder: Optional[RunRecorder],
    trace_prefix: str,
    timeout_s: float,
    max_candidates: int,
    pattern_cache: Optional[TacticPatternCache] = None,
    pattern_context: Optional[Dict[str, Any]] = None,
    helper_blocks: Optional[List[str]] = None,
    finalize_root: bool = True,
    opaque_mode: Optional[bool] = None,
    allow_official_answer_visibility: Optional[bool] = None,
    excluded_source_prefixes: Sequence[str] = (),
    suppressed_proofs: Sequence[str] = (),
    suppressed_proof_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_records: Sequence[Mapping[str, Any]] = (),
    tactic_source_suppression_helper_blocks: Sequence[str] = (),
    tactic_closer: Optional[Any] = None,
) -> Tuple[bool, Optional[str]]:
    """Compatibility adapter for the extracted root-tactic close helper."""

    effective_opaque_mode = bool(
        getattr(dossier, "opaque_mode", True) if opaque_mode is None else opaque_mode
    )
    effective_allow_official_answer_visibility = bool(
        getattr(dossier, "allow_official_answer_visibility", False)
        if allow_official_answer_visibility is None
        else allow_official_answer_visibility
    )
    return await _run_root_tactic_close(
        phase=phase,
        theorem_name=theorem_name,
        goal_statement=goal_statement,
        preamble=preamble,
        lean=lean,
        dossier=dossier,
        recorder=recorder,
        trace_prefix=trace_prefix,
        timeout_s=timeout_s,
        max_candidates=max_candidates,
        pattern_cache=pattern_cache,
        pattern_context=pattern_context,
        helper_blocks=helper_blocks,
        excluded_source_prefixes=excluded_source_prefixes,
        suppressed_proofs=suppressed_proofs,
        suppressed_proof_records=suppressed_proof_records,
        tactic_source_suppression_records=tactic_source_suppression_records,
        tactic_source_suppression_helper_blocks=(
            tactic_source_suppression_helper_blocks or helper_blocks or ()
        ),
        active_root_targets=tuple(
            item
            for item in list(getattr(dossier, "active_root_targets", []) or ())
            if isinstance(item, dict)
        ),
        tactic_closer=tactic_closer or try_close_with_tactics,
        transient_checker=is_transient_tactic_close_failure,
        trace=_trace,
        finalize_root=finalize_root,
        opaque_mode=effective_opaque_mode,
        allow_official_answer_visibility=effective_allow_official_answer_visibility,
    )


_PROVE_PROBLEM_COMPAT_DEFAULTS: Dict[str, Any] = {
    "max_tool_calls_per_turn": 10,
    "premise_retrieval_top_k": PREMISE_DEFAULT_TOP_K,
    "proof_state_child_tactic_max_candidates": 32,
    "proof_state_cache_enabled": False,
    "mini_recursive_enabled": False,
    "adaptive_recursive_on_stall": False,
    "mini_recursive_passes": 1,
    "mini_recursive_max_claims": 4,
    "mini_recursive_turns_per_claim": 3,
    "mini_recursive_tactic_timeout_s": 20.0,
    "mini_recursive_tactic_max_candidates": 48,
    "recursive_helper_prover_enabled": False,
    "recursive_helper_refine": False,
    "mini_phase_temperatures_enabled": False,
    "formal_state_search_enabled": False,
    "startup_root_fast_lane_enabled": False,
    "run_wall_clock_budget_s": 0.0,
    "no_strong_progress_budget_s": 0.0,
}


_PROVE_PROBLEM_OPERATIONAL_DEFAULTS: Dict[str, Any] = {
    **_PROVE_PROBLEM_COMPAT_DEFAULTS,
    "max_tool_calls_per_turn": 60,
    "premise_retrieval_top_k": max(PREMISE_DEFAULT_TOP_K, 64),
    "proof_state_child_tactic_max_candidates": 36,
    "proof_state_cache_enabled": True,
    "mini_recursive_enabled": True,
    "adaptive_recursive_on_stall": True,
    "mini_recursive_passes": 6,
    "mini_recursive_max_claims": PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
    "mini_recursive_turns_per_claim": 3,
    "mini_recursive_tactic_timeout_s": 60.0,
    "mini_recursive_tactic_max_candidates": max(48, 36),
    "recursive_helper_prover_enabled": True,
    "recursive_helper_refine": True,
    "mini_phase_temperatures_enabled": True,
    "formal_state_search_enabled": False,
    # The fast lane is intentionally destructive to unfinished speculative
    # work when its small deadline expires.  Keep it available as an explicit
    # optimization, but never put that behavior on the operational default
    # path; the durable session owns ordinary root tactics and authoring.
    "startup_root_fast_lane_enabled": False,
    "run_wall_clock_budget_s": 0.0,
    "no_strong_progress_budget_s": 0.0,
}


def _prove_problem_default_profile_values(default_profile: str) -> Dict[str, Any]:
    """Return public prove_problem omitted-argument defaults for a profile."""

    profile = str(default_profile or "operational").strip().lower()
    if profile in {"operational", "cli", "default"}:
        return dict(_PROVE_PROBLEM_OPERATIONAL_DEFAULTS)
    if profile in {"compat", "conservative", "legacy"}:
        return dict(_PROVE_PROBLEM_COMPAT_DEFAULTS)
    raise ValueError(
        "default_profile must be one of operational/cli/default or "
        "compat/conservative/legacy"
    )


def _prove_problem_default_mini_phase_temperatures(
    defaults: Mapping[str, Any],
) -> Optional[MiniPhaseTemperatures]:
    if not bool(defaults.get("mini_phase_temperatures_enabled")):
        return None
    return MiniPhaseTemperatures(enabled=True)


@fresh_provider_lane_health_run
async def prove_problem(
    *,
    problem: TheoremProblem,
    prover_client: OpenAICompatClient,
    refiner_client: Optional[OpenAICompatClient],
    planner_escalation_client: Optional[OpenAICompatClient] = None,
    lean: LeanRunner,
    max_prove_turns: int,
    max_refine_turns: int,
    trace_prefix: str = "",
    recorder: Optional[RunRecorder] = None,
    searcher: Optional[MathlibApiSearcher] = None,
    mathematical_retrieval_enabled: bool = True,
    lean_check_tool_enabled: bool = True,
    try_lean_tool_enabled: bool = True,
    compute_examples_tool_enabled: Optional[bool] = None,
    apply_decl_to_goal_tool_enabled: bool = True,
    max_tool_calls_per_turn: Optional[int] = None,
    raw_feedback: bool = False,
    dossier: Optional[ProofDossier] = None,
    llm_preamble_override: Optional[str] = None,
    lean_preamble_override: Optional[str] = None,
    opaque_mode: bool = True,
    allow_official_answer_visibility: bool = False,
    premise_retrieval_enabled: bool = False,
    premise_retrieval_top_k: Optional[int] = None,
    premise_zero_hit_policy: str = "off",
    premise_zero_hit_suppress_library_first: bool = True,
    premise_zero_hit_max_local_turns: int = 1,
    premise_zero_hit_allow_api_grounding_after_lean_failure: bool = True,
    repair_retrieval_enabled: bool = True,
    proof_state_retrieval_enabled: bool = False,
    repair_retrieval_top_k: int = 6,
    parallel_samples: int = 1,
    parallel_temperatures: Sequence[float] = (),
    parallel_late_sample_grace_s: float = _PARALLEL_SAMPLE_LATE_GRACE_DEFAULT_S,
    mini_phase_temperatures: Optional[MiniPhaseTemperatures] = None,
    proof_state_engine_enabled: bool = True,
    proof_state_child_tactics_enabled: bool = True,
    proof_state_child_tactic_timeout_s: float = DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
    proof_state_child_tactic_max_candidates: Optional[int] = None,
    proof_state_child_goal_limit: int = 3,
    proof_state_decl_application_limit: int = 6,
    proof_state_batch_parallelism: int = 1,
    formal_state_search_enabled: Optional[bool] = None,
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
    proof_state_cache_enabled: Optional[bool] = None,
    proof_state_cache_path: Optional[Path] = None,
    root_tactic_prepass_enabled: bool = False,
    root_tactic_timeout_s: float = 40.0,
    root_tactic_max_candidates: int = 64,
    startup_root_fast_lane_enabled: Optional[bool] = None,
    startup_root_fast_lane_tactic_timeout_s: float = 300.0,
    startup_root_fast_lane_tactic_max_candidates: int = 12,
    mini_recursive_enabled: Optional[bool] = None,
    adaptive_recursive_on_stall: Optional[bool] = None,
    mini_recursive_passes: Optional[int] = None,
    mini_recursive_max_claims: Optional[int] = None,
    mini_recursive_turns_per_claim: Optional[int] = None,
    mini_recursive_tactic_timeout_s: Optional[float] = None,
    mini_recursive_tactic_max_candidates: Optional[int] = None,
    session_scope: Optional[str] = None,
    cost_controller: Any = None,
    run_wall_clock_budget_s: Optional[float] = None,
    no_strong_progress_budget_s: Optional[float] = None,
    default_profile: str = "operational",
    # Phase 2 (2026-05-09) — recursive helper prover.
    recursive_helper_prover_enabled: Optional[bool] = None,
    recursive_helper_budget: int = 0,
    recursive_helper_max_depth: int = 3,
    recursive_helper_max_attempts_per_node: int = 2,
    recursive_helper_turns: int = 5,
    recursive_helper_refine: Optional[bool] = None,
    theory_library: Optional[Any] = None,
    theory_candidate_builder: Optional[Any] = None,
    theory_domain: str = "general mathematics",
    theory_bundle_ids: Sequence[str] = (),
    theory_default_imports: Sequence[str] = ("Mathlib",),
    theory_promote_verified_helpers: bool = False,
    graph_execution_projection_mode: Optional[str] = None,
    graph_execution_project_environment_hash: Optional[str] = None,
    worker_ready_callback: Optional[Callable[[], None]] = None,
) -> Tuple[bool, Optional[str]]:
    """Public entry point for the MiniSession prover.

    Omitted capability knobs use the operational profile by default, matching
    the CLI. Callers that need the older lightweight omitted-value behavior can
    pass ``default_profile="compat"``; explicit keyword values always win over
    the profile. Persistent domain theory is owned by the CLI composition root;
    programmatic callers opt in by injecting ``theory_library`` and
    ``theory_candidate_builder`` explicitly.
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

    if bool(getattr(cost_controller, "budget_enabled", False)):
        await _validate_cost_budget_pricing(
            max_cost_usd=float(getattr(cost_controller, "max_cost_usd", 0.0) or 0.0),
            role_clients=(
                ("prover", prover_client),
                ("refiner", refiner_client),
                ("planner_escalation", planner_escalation_client),
            ),
        )

    profile_defaults = _prove_problem_default_profile_values(default_profile)
    def _defaulted(name: str, value: Any) -> Any:
        return profile_defaults[name] if value is None else value

    max_tool_calls_per_turn = int(
        _defaulted("max_tool_calls_per_turn", max_tool_calls_per_turn)
    )
    premise_retrieval_top_k = int(
        _defaulted("premise_retrieval_top_k", premise_retrieval_top_k)
    )
    proof_state_child_tactic_max_candidates = int(
        _defaulted(
            "proof_state_child_tactic_max_candidates",
            proof_state_child_tactic_max_candidates,
        )
    )
    proof_state_cache_enabled = bool(
        _defaulted("proof_state_cache_enabled", proof_state_cache_enabled)
    )
    mini_recursive_enabled = bool(
        _defaulted("mini_recursive_enabled", mini_recursive_enabled)
    )
    adaptive_recursive_on_stall = bool(
        _defaulted("adaptive_recursive_on_stall", adaptive_recursive_on_stall)
    )
    mini_recursive_passes = int(
        _defaulted("mini_recursive_passes", mini_recursive_passes)
    )
    mini_recursive_max_claims = int(
        _defaulted("mini_recursive_max_claims", mini_recursive_max_claims)
    )
    mini_recursive_turns_per_claim = int(
        _defaulted("mini_recursive_turns_per_claim", mini_recursive_turns_per_claim)
    )
    mini_recursive_tactic_timeout_s = float(
        _defaulted(
            "mini_recursive_tactic_timeout_s",
            mini_recursive_tactic_timeout_s,
        )
    )
    mini_recursive_tactic_max_candidates = int(
        _defaulted(
            "mini_recursive_tactic_max_candidates",
            mini_recursive_tactic_max_candidates,
        )
    )
    formal_state_search_enabled = bool(
        _defaulted(
            "formal_state_search_enabled",
            formal_state_search_enabled,
        )
    )
    startup_root_fast_lane_enabled = bool(
        _defaulted(
            "startup_root_fast_lane_enabled",
            startup_root_fast_lane_enabled,
        )
    )
    recursive_helper_prover_enabled = bool(
        _defaulted(
            "recursive_helper_prover_enabled",
            recursive_helper_prover_enabled,
        )
    )
    recursive_helper_refine = bool(
        _defaulted("recursive_helper_refine", recursive_helper_refine)
    )
    run_wall_clock_budget_s = float(
        _defaulted("run_wall_clock_budget_s", run_wall_clock_budget_s)
    )
    no_strong_progress_budget_s = float(
        _defaulted(
            "no_strong_progress_budget_s",
            no_strong_progress_budget_s,
        )
    )
    if mini_phase_temperatures is None:
        mini_phase_temperatures = _prove_problem_default_mini_phase_temperatures(
            profile_defaults
        )

    from .mathematical_retrieval.async_runtime import run_sync_abandonment_safe

    # First-time project/dense composition can legitimately run for a long
    # time across many individually watched embedding batches. Keep that work
    # off the caller's event loop without imposing a global build-duration cap.
    searcher = await run_sync_abandonment_safe(
        lambda: _ensure_default_mathematical_retrieval_service(
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
        ),
        timeout_s=float("inf"),
    )

    # A shared retrieval service may index the theorem project itself. Bind a
    # session-local held-out view before either the legacy or MiniSession path
    # performs eager retrieval, so the target declaration/source cannot leak
    # into its own proof search.
    fork_retrieval = getattr(searcher, "fork_session_context", None)
    if callable(fork_retrieval):
        searcher = fork_retrieval()
    bind_answer_safe_preamble = getattr(
        searcher,
        "with_answer_safe_preamble",
        None,
    )
    if callable(bind_answer_safe_preamble):
        answer_safe_preamble = str(
            llm_preamble_override
            if llm_preamble_override is not None
            else getattr(problem, "preamble", "")
            or ""
        )
        active_lean_preamble = str(
            lean_preamble_override
            if lean_preamble_override is not None
            else getattr(problem, "preamble", "")
            or ""
        )
        searcher = bind_answer_safe_preamble(
            answer_safe_preamble,
            lean_preamble=active_lean_preamble,
            theorem_name=str(getattr(problem, "theorem_name", "") or ""),
            source_path=str(getattr(problem, "path", "") or ""),
            # Candidate identity must follow the exact Lean environment in
            # which an advertised prompt-visible declaration is usable.  A
            # shared Mathlib/project source hash omits target-local preamble
            # declarations and would alias distinct external theorem inputs.
            environment_hash=text_hash(active_lean_preamble),
        )
    set_excluded_target = getattr(searcher, "set_excluded_target", None)
    if callable(set_excluded_target):
        set_excluded_target(
            declaration_names=(problem.theorem_name,),
            source_paths=(
                (getattr(problem, "path", ""),)
                if bool(
                    getattr(problem, "exclude_entire_source_from_retrieval", False)
                )
                else ()
            ),
        )

    normalized_zero_hit_policy = str(premise_zero_hit_policy or "off").strip().lower()
    if normalized_zero_hit_policy not in {"off", "shadow", "enforce"}:
        normalized_zero_hit_policy = "off"
    from .mini_session.factory import prove_problem_via_session

    return await prove_problem_via_session(
        problem=problem,
        prover_client=prover_client,
        refiner_client=refiner_client,
        planner_escalation_client=planner_escalation_client,
        lean=lean,
        max_prove_turns=max_prove_turns,
        max_refine_turns=max_refine_turns,
        trace_prefix=trace_prefix,
        recorder=recorder,
        searcher=searcher,
        mathematical_retrieval_enabled=bool(
            mathematical_retrieval_enabled
        ),
        lean_check_tool_enabled=lean_check_tool_enabled,
        try_lean_tool_enabled=try_lean_tool_enabled,
        compute_examples_tool_enabled=compute_examples_tool_enabled,
        apply_decl_to_goal_tool_enabled=apply_decl_to_goal_tool_enabled,
        max_tool_calls_per_turn=max_tool_calls_per_turn,
        raw_feedback=raw_feedback,
        dossier=dossier,
        llm_preamble_override=llm_preamble_override,
        lean_preamble_override=lean_preamble_override,
        opaque_mode=opaque_mode,
        allow_official_answer_visibility=allow_official_answer_visibility,
        premise_retrieval_enabled=premise_retrieval_enabled,
        proof_state_retrieval_enabled=proof_state_retrieval_enabled,
        premise_retrieval_top_k=premise_retrieval_top_k,
        premise_zero_hit_policy=normalized_zero_hit_policy,
        premise_zero_hit_suppress_library_first=(
            premise_zero_hit_suppress_library_first
        ),
        premise_zero_hit_max_local_turns=premise_zero_hit_max_local_turns,
        premise_zero_hit_allow_api_grounding_after_lean_failure=(
            premise_zero_hit_allow_api_grounding_after_lean_failure
        ),
        repair_retrieval_enabled=repair_retrieval_enabled,
        repair_retrieval_top_k=repair_retrieval_top_k,
        parallel_samples=parallel_samples,
        parallel_temperatures=parallel_temperatures,
        parallel_late_sample_grace_s=parallel_late_sample_grace_s,
        mini_phase_temperatures=mini_phase_temperatures,
        proof_state_engine_enabled=proof_state_engine_enabled,
        proof_state_child_tactics_enabled=proof_state_child_tactics_enabled,
        proof_state_child_tactic_timeout_s=proof_state_child_tactic_timeout_s,
        proof_state_child_tactic_max_candidates=proof_state_child_tactic_max_candidates,
        proof_state_child_goal_limit=proof_state_child_goal_limit,
        proof_state_decl_application_limit=proof_state_decl_application_limit,
        proof_state_batch_parallelism=proof_state_batch_parallelism,
        formal_state_search_enabled=formal_state_search_enabled,
        formal_state_search_timeout_s=formal_state_search_timeout_s,
        formal_state_search_operation_timeout_s=(
            formal_state_search_operation_timeout_s
        ),
        formal_state_search_provider_timeout_s=(
            formal_state_search_provider_timeout_s
        ),
        formal_state_search_provider_max_tokens=(
            formal_state_search_provider_max_tokens
        ),
        formal_state_search_provider_reasoning_effort=(
            formal_state_search_provider_reasoning_effort
        ),
        formal_state_search_provider_max_attempts=(
            formal_state_search_provider_max_attempts
        ),
        formal_state_search_provider_retry_backoff_s=(
            formal_state_search_provider_retry_backoff_s
        ),
        formal_state_search_beam_width=formal_state_search_beam_width,
        formal_state_search_max_steps=formal_state_search_max_steps,
        formal_state_search_max_candidates=formal_state_search_max_candidates,
        formal_state_search_backtrack_limit=(
            formal_state_search_backtrack_limit
        ),
        formal_state_search_max_no_improvement_quanta=(
            formal_state_search_max_no_improvement_quanta
        ),
        falsification_enabled=falsification_enabled,
        falsification_max_checks=falsification_max_checks,
        falsification_operation_timeout_s=falsification_operation_timeout_s,
        falsification_engine_timeout_s=falsification_engine_timeout_s,
        proof_state_cache_enabled=proof_state_cache_enabled,
        proof_state_cache_path=proof_state_cache_path,
        root_tactic_prepass_enabled=root_tactic_prepass_enabled,
        root_tactic_timeout_s=root_tactic_timeout_s,
        root_tactic_max_candidates=root_tactic_max_candidates,
        startup_root_fast_lane_enabled=startup_root_fast_lane_enabled,
        startup_root_fast_lane_tactic_timeout_s=(
            startup_root_fast_lane_tactic_timeout_s
        ),
        startup_root_fast_lane_tactic_max_candidates=(
            startup_root_fast_lane_tactic_max_candidates
        ),
        mini_recursive_enabled=mini_recursive_enabled,
        adaptive_recursive_on_stall=adaptive_recursive_on_stall,
        mini_recursive_passes=mini_recursive_passes,
        mini_recursive_max_claims=mini_recursive_max_claims,
        mini_recursive_turns_per_claim=mini_recursive_turns_per_claim,
        mini_recursive_tactic_timeout_s=mini_recursive_tactic_timeout_s,
        mini_recursive_tactic_max_candidates=mini_recursive_tactic_max_candidates,
        **(
            {"session_scope": session_scope}
            if session_scope is not None
            else {}
        ),
        recursive_helper_prover_enabled=recursive_helper_prover_enabled,
        recursive_helper_budget=recursive_helper_budget,
        recursive_helper_max_depth=recursive_helper_max_depth,
        recursive_helper_max_attempts_per_node=recursive_helper_max_attempts_per_node,
        recursive_helper_turns=recursive_helper_turns,
        recursive_helper_refine=recursive_helper_refine,
        run_wall_clock_budget_s=max(0.0, run_wall_clock_budget_s),
        no_strong_progress_budget_s=max(
            0.0,
            no_strong_progress_budget_s,
        ),
        cost_controller=cost_controller,
        theory_library=theory_library,
        theory_candidate_builder=theory_candidate_builder,
        theory_domain=theory_domain,
        theory_bundle_ids=theory_bundle_ids,
        theory_default_imports=theory_default_imports,
        theory_promote_verified_helpers=theory_promote_verified_helpers,
        graph_execution_projection_mode=graph_execution_projection_mode,
        graph_execution_project_environment_hash=(
            graph_execution_project_environment_hash
        ),
        worker_ready_callback=worker_ready_callback,
    )

async def _preflight_theorem_project_input(
    runner: Any,
    problem: TheoremProblem,
    *,
    timeout_s: float,
) -> TheoremProblem:
    """Elaborate the exact source declaration and return its canonical type.

    A parsed header is not a semantic theorem type: scoped ``open``,
    ``include``, and ``set_option ... in`` commands can change elaboration.
    Compile the exact sound prefix plus a proof-stub form of the selected
    declaration and ask Lean for its type. The target's old proof body and downstream
    declarations are intentionally outside the requested theorem boundary. Lake
    revalidates local/external import dependency graphs once per project
    request; a current build is a no-op, including on read-only projects.
    """

    validate_theorem_project_source(problem)

    ensure_imports = getattr(runner, "ensure_project_imports_built", None)
    # Lake's trace graph, rather than hand-rolled mtimes, is authoritative for
    # direct and transitive module freshness. A current build is a no-op and
    # remains compatible with already-built read-only projects.
    revalidate_environment = getattr(
        runner,
        "revalidate_theorem_project_environment",
        None,
    )
    if callable(revalidate_environment):
        await revalidate_environment()
    elif callable(ensure_imports):
        await ensure_imports()
    validate_theorem_project_source(problem)

    source_type_probe = getattr(runner, "check_source_declaration_type", None)
    source_bound_problem = problem
    if callable(source_type_probe) and str(problem.elaboration_source or "").strip():
        exact_source = str(problem.elaboration_source)
        ok, elaborated_type, output = await source_type_probe(
            exact_source,
            problem.theorem_name,
            timeout_s=max(1.0, float(timeout_s)),
        )
        if not ok:
            raise ValueError(
                "theorem-project source declaration elaboration failed before "
                f"proof search: {str(output or '')[:4000]}"
            )
        mark_ready = getattr(runner, "mark_project_imports_ready", None)
        if callable(mark_ready):
            mark_ready()
        problem = with_elaborated_statement_type(problem, elaborated_type)
        validate_theorem_project_source(problem)
    elif callable(ensure_imports):
        await ensure_imports()

    source_equivalence_probe = getattr(
        runner,
        "check_source_declaration_type_equivalence",
        None,
    )
    exact_source = str(source_bound_problem.elaboration_source or "").strip()
    check_statement_type_raw = getattr(runner, "check_statement_type_raw", None)
    check_with_sorry_raw = getattr(runner, "check_with_sorry_raw", None)
    check_input = getattr(runner, "check", None)

    async def validate_rendered_candidate(
        candidate_problem: TheoremProblem,
        *,
        label: str,
        require_source_equivalence: bool = True,
    ) -> tuple[bool, str]:
        parsed: Any
        candidate_output: str
        returncode: int
        if callable(check_statement_type_raw):
            parsed, output, returncode = await check_statement_type_raw(
                candidate_problem.statement_type,
                preamble_override=str(candidate_problem.lean_preamble or ""),
                timeout_s=max(1.0, float(timeout_s)),
            )
            candidate_output = str(output or "")
        elif callable(check_with_sorry_raw):
            parsed, output, returncode = await check_with_sorry_raw(
                candidate_problem.statement_type,
                "by\n  sorry",
                [],
                preamble_override=str(candidate_problem.lean_preamble or ""),
                timeout_s=max(1.0, float(timeout_s)),
            )
            candidate_output = str(output or "")
        elif callable(check_input):
            result = await check_input(
                candidate_problem.statement_type,
                "by\n  sorry",
                [],
                preamble_override=str(candidate_problem.lean_preamble or ""),
                timeout_s=max(1.0, float(timeout_s)),
                check_kind="theorem_project_preflight",
            )
            parsed = result
            candidate_output = str(getattr(result, "output", "") or "")
            returncode = 0 if bool(getattr(result, "ok", False)) else 1
        else:
            raise TypeError("Lean runner does not provide a theorem preflight method")
        if int(returncode) != 0 or not bool(getattr(parsed, "ok", False)):
            if bool(getattr(parsed, "infra_failure", False)):
                raise ValueError(
                    f"theorem-project {label} validation hit transient "
                    "infrastructure (retry the run): "
                    f"{candidate_output[:2000]}"
                )
            return False, candidate_output
        if require_source_equivalence and callable(source_type_probe) and exact_source:
            if not callable(source_equivalence_probe):
                return False, "source-bound definitional-equivalence probe unavailable"
            equivalent, equivalence_output, equivalence_returncode = (
                await source_equivalence_probe(
                    exact_source,
                    source_bound_problem.theorem_name,
                    candidate_problem.statement_type,
                    timeout_s=max(1.0, float(timeout_s)),
                    preamble_override=str(candidate_problem.lean_preamble or ""),
                )
            )
            if int(equivalence_returncode) != 0 or not bool(
                getattr(equivalent, "ok", False)
            ):
                semantic_output = str(equivalence_output or "")
                if bool(getattr(equivalent, "infra_failure", False)):
                    raise ValueError(
                        f"theorem-project {label} source-equivalence "
                        "validation hit transient infrastructure (retry "
                        f"the run): {semantic_output[:2000]}"
                    )
                return False, (
                    "rendering elaborates independently but is not "
                    "definitionally equal to the source declaration:\n"
                    f"{semantic_output}"
                )
        return True, candidate_output

    compact_ok, compact_output = await validate_rendered_candidate(
        problem,
        label="compact-render",
    )
    if compact_ok:
        validate_theorem_project_source(problem)
        return refresh_theorem_project_environment(problem)
    if not (callable(source_type_probe) and exact_source):
        raise ValueError(
            "theorem-project target elaboration failed before proof search: "
            f"{compact_output[:4000]}"
        )

    # ``#check`` output is a display, not a source serializer. Try a fully
    # explicit display, then the exact parser-bound source syntax. Rendered
    # displays must also be definitionally equal to the theorem constant. The
    # parser-bound fallback is the declaration text captured from that exact
    # source, so independently re-elaborating it is the source-bound check; it
    # must not depend on optional meta-command imports in the user's project.
    explicit_ok, explicit_type, explicit_probe_output = await source_type_probe(
        exact_source,
        source_bound_problem.theorem_name,
        timeout_s=max(1.0, float(timeout_s)),
        pp_explicit=True,
    )
    explicit_failure = str(explicit_probe_output or "")[:4000]
    if explicit_ok:
        explicit_problem = with_elaborated_statement_type(
            source_bound_problem,
            explicit_type,
            rendering="lean_pp_explicit",
        )
        explicit_valid, explicit_failure = await validate_rendered_candidate(
            explicit_problem,
            label="explicit-render",
        )
        if explicit_valid:
            validate_theorem_project_source(explicit_problem)
            return refresh_theorem_project_environment(explicit_problem)

    source_statement = str(
        dict(source_bound_problem.input_spec or {}).get("source_statement_type")
        or source_bound_problem.statement_type
        or ""
    ).strip()
    source_failure = "source statement type unavailable"
    if source_statement:
        source_problem = source_bound_problem
        if source_statement != str(source_bound_problem.statement_type or "").strip():
            source_problem = with_elaborated_statement_type(
                source_bound_problem,
                source_statement,
                rendering="source_statement",
            )
        source_valid, source_failure = await validate_rendered_candidate(
            source_problem,
            label="source-statement",
        )
        if source_valid:
            validate_theorem_project_source(source_problem)
            return refresh_theorem_project_environment(source_problem)

    raise ValueError(
        "theorem-project target elaboration failed before proof search: all "
        "source-derived target renderings failed source-bound validation. "
        "compact failure:\n"
        f"{compact_output[:4000]}\nexplicit fallback failure:\n"
        f"{explicit_failure[:4000]}\nsource statement fallback failure:\n"
        f"{source_failure[:4000]}"
    )


async def prove_theorem_project(
    *,
    request: TheoremProjectRequest,
    prover_client: OpenAICompatClient,
    refiner_client: Optional[OpenAICompatClient] = None,
    lean: Optional[LeanRunner] = None,
    scratch_dir: Optional[Path] = None,
    max_prove_turns: int = 30,
    max_refine_turns: int = 25,
    **prove_kwargs: Any,
) -> Tuple[bool, Optional[str]]:
    """Resolve and prove one arbitrary theorem-project request."""

    if "problem" in prove_kwargs:
        raise TypeError("prove_theorem_project derives problem from request")
    # Reject invalid proof-policy inputs before resolving paths, constructing a
    # Lean runner, activating a theory library, or running the project probe.
    require_falsification_search_bound(
        prove_kwargs.get("falsification_max_checks", 32),
        field="falsification_max_checks",
    )
    require_falsification_watchdog(
        prove_kwargs.get(
            "falsification_operation_timeout_s",
            DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
        ),
        field="falsification_operation_timeout_s",
    )
    require_falsification_watchdog(
        prove_kwargs.get(
            "falsification_engine_timeout_s",
            DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
        ),
        field="falsification_engine_timeout_s",
    )
    problem = resolve_theorem_project(request)
    lean_timeout_s = max(1, int(prove_kwargs.pop("lean_timeout_s", 300) or 300))
    owned_lean = lean is None
    runner = lean or LeanRunner(
        LeanConfig(
            project_dir=str(problem.project_path),
            scratch_dir=str(
                Path(scratch_dir).expanduser().resolve()
                if scratch_dir is not None
                else Path(tempfile.gettempdir())
                / "ensemble_mini"
                / problem.artifact_slug
                / uuid.uuid4().hex
            ),
            timeout_s=lean_timeout_s,
            max_parallel=1,
            backend_mode="auto",
            module_search_paths=[str(path) for path in problem.module_search_paths],
            project_imports=list(problem.project_imports),
            project_import_sources=dict(
                getattr(problem, "project_import_sources", {}) or {}
            ),
            support_project_builds={
                str(project): list(targets)
                for project, targets in dict(
                    getattr(problem, "support_project_builds", {}) or {}
                ).items()
            },
        )
    )
    runner_cfg = getattr(runner, "cfg", None)
    if lean is not None and isinstance(runner_cfg, LeanConfig):
        runner_project = Path(runner_cfg.project_dir).expanduser().resolve()
        if runner_project != problem.project_path:
            raise ValueError(
                "injected LeanRunner project does not match theorem request: "
                f"{runner_project} != {problem.project_path}"
            )
        configured_module_roots = {
            Path(path).expanduser().resolve()
            for path in list(runner_cfg.module_search_paths or ())
        }
        missing_module_roots = [
            path
            for path in problem.module_search_paths
            if path.resolve() not in configured_module_roots
        ]
        if missing_module_roots:
            raise ValueError(
                "injected LeanRunner omits theorem support module roots: "
                + ", ".join(str(path) for path in missing_module_roots)
            )
        configured_project_imports = set(runner_cfg.project_imports or ())
        missing_project_imports = [
            module
            for module in problem.project_imports
            if module not in configured_project_imports
        ]
        if missing_project_imports:
            raise ValueError(
                "injected LeanRunner omits project import build targets: "
                + ", ".join(missing_project_imports)
            )
        required_import_sources = dict(
            getattr(problem, "project_import_sources", {}) or {}
        )
        configured_import_sources = dict(
            getattr(runner_cfg, "project_import_sources", {}) or {}
        )
        mismatched_import_sources = [
            module
            for module, source in required_import_sources.items()
            if str(configured_import_sources.get(module, "")) != str(source)
        ]
        if mismatched_import_sources:
            raise ValueError(
                "injected LeanRunner omits theorem import source provenance: "
                + ", ".join(mismatched_import_sources)
            )
        required_support_builds = {
            str(project): list(targets)
            for project, targets in dict(
                getattr(problem, "support_project_builds", {}) or {}
            ).items()
        }
        configured_support_builds = {
            str(project): list(targets)
            for project, targets in dict(
                getattr(runner_cfg, "support_project_builds", {}) or {}
            ).items()
        }
        if configured_support_builds != required_support_builds:
            raise ValueError(
                "injected LeanRunner support-project build graph does not "
                "match theorem request"
            )
    try:
        theory_library = prove_kwargs.get("theory_library")
        if (
            theory_library is not None
            and getattr(theory_library, "mode", "off") != "off"
        ):
            # Match the CLI lifecycle invariant: a theorem-project preflight
            # is a real Lean operation and may initialize a cached backend.
            # Every environment-contributing library must be active first.
            theory_library.activate_lean_runner(runner)
        prepared_problem = await _preflight_theorem_project_input(
            runner,
            problem,
            timeout_s=float(lean_timeout_s),
        )
        if isinstance(prepared_problem, TheoremProblem):
            problem = prepared_problem
        return await prove_problem(
            problem=problem,
            prover_client=prover_client,
            refiner_client=refiner_client,
            lean=runner,
            max_prove_turns=max_prove_turns,
            max_refine_turns=max_refine_turns,
            **prove_kwargs,
        )
    finally:
        if owned_lean:
            await runner.aclose()


def _format_lean_signature(problem: TheoremProblem) -> str:
    """Reconstruct the theorem signature for the LLM to see.

    We keep the natural-language docstring and the Lean signature shape, but
    leave ordinary abbrev/def declarations in the preamble intact. The
    PutnamBench adapter separately replaces its answer declarations with
    opaque axioms in answer-safe mode; generic inputs are never rewritten.
    """
    declaration_name = str(
        getattr(problem, "declaration_name", "") or problem.theorem_name
    )
    universe_suffix = str(
        getattr(problem, "declaration_universe_suffix", "") or ""
    )
    public_prefix = "public " if bool(
        getattr(problem, "declaration_public", False)
    ) else ""
    return (
        f"{public_prefix}theorem {declaration_name}{universe_suffix} : "
        f"{problem.statement_type} := sorry"
    )


def _mini_solved_export_status(
    status: str,
    *,
    path: str = "",
    diagnostic: str = "",
) -> Dict[str, Any]:
    rejected_by_verifier = str(status or "") in {
        "kernel_rejected",
        "lean_rejected",
        "axiom_rejected",
        "axiom_audit_failed",
    }
    return {
        "mini_solved_export_status": str(status or ""),
        "mini_solved_export_path": str(path or ""),
        "mini_solved_export_diagnostic_preview": str(diagnostic or "")[:4000],
        "mini_solved_export_attempts": 1 if status != "not_attempted" else 0,
        "mini_solved_export_successes": 1 if status == "verified" else 0,
        "mini_solved_export_skipped": (
            1
            if status in {"not_reconstructable", "import_error"}
            else 0
        ),
        "mini_solved_export_kernel_rejected": 1 if rejected_by_verifier else 0,
        "solved_export_kernel_rejected": 1 if rejected_by_verifier else 0,
        "mini_solved_export_exceptions": 1 if status == "exception" else 0,
        "mini_solved_export_verified": 1 if status == "verified" else 0,
        "mini_solved_export_downgrades_solved": 0,
        "solved_export_status": str(status or ""),
        "solved_export_verified": bool(status == "verified"),
    }


def _mini_solved_export_verified_payload(status: Mapping[str, Any]) -> bool:
    return solved_export_verified_payload(status)


def _mini_solved_export_failure_counter_present(status: Mapping[str, Any]) -> bool:
    return solved_export_failure_counter_present(status)


def _mini_solved_export_failure_reason(status: Mapping[str, Any]) -> str:
    return solved_export_failure_reason(status)


def _auto_export_solved_run(
    output_dir: Path,
    *,
    lean_project_dir: Optional[Path] = None,
) -> Dict[str, Any]:
    """Best-effort export of a solved run to runs/mini_prover/solved."""

    try:
        from .extract_solved import (
            SolvedExportVerificationError,
            export_solved_run,
        )
    except Exception as exc:
        print(f"Solved Lean export skipped: could not import exporter ({exc})")
        return _mini_solved_export_status("import_error", diagnostic=str(exc))

    project_dir = (
        Path(lean_project_dir)
        if lean_project_dir is not None
        else _PROJECT_ROOT / "external" / "PutnamBench" / "lean4"
    )
    if not project_dir.is_absolute():
        project_dir = (_PROJECT_ROOT / project_dir).resolve()
    try:
        record = export_solved_run(
            Path(output_dir),
            verify_lean=True,
            allow_pre_export_bootstrap=True,
            lean_project_dir=project_dir,
        )
    except SolvedExportVerificationError as exc:
        print("Solved Lean export rejected by Lean self-check.")
        return _mini_solved_export_status(
            str(getattr(exc, "status", "") or "lean_rejected"),
            diagnostic=getattr(exc, "output", str(exc)),
        )
    except Exception as exc:
        print(f"Solved Lean export failed: {type(exc).__name__}: {exc}")
        return _mini_solved_export_status(
            "exception",
            diagnostic=f"{type(exc).__name__}: {exc}",
        )

    if record is None:
        print(
            "Solved Lean export skipped: no kernel-verified reconstructable "
            "solved run artifact."
        )
        return _mini_solved_export_status("not_reconstructable")
    visibility_bits = [str(getattr(record, "answer_visibility", "") or "")]
    for attr in (
        "opaque_mode",
        "allow_official_answer_visibility",
        "official_answer_payload_present",
    ):
        value = getattr(record, attr, None)
        if isinstance(value, bool):
            visibility_bits.append(f"{attr}={'true' if value else 'false'}")
    print(
        "Solved Lean exported: "
        f"{record.output_path} ({', '.join(visibility_bits)})"
    )
    return _mini_solved_export_status(
        "verified",
        path=record.output_path,
        diagnostic=record.export_verification_output,
    )


_MINI_PROOF_GRAPH_SUMMARY_TO_METRIC_KEY = {
    "nodes": "mini_proof_graph_nodes",
    "edges": "mini_proof_graph_edges",
    "attempts": "mini_proof_graph_attempts",
    "helper_nodes": "mini_proof_graph_helper_nodes",
    "proved_helpers": "mini_proof_graph_proved_helpers",
    "open_helpers": "mini_proof_graph_open_helpers",
    "failed_helpers": "mini_proof_graph_failed_helpers",
    "blocked_helpers": "mini_proof_graph_blocked_helpers",
    "claim_nodes": "mini_proof_graph_claim_nodes",
    "open_claim_nodes": "mini_proof_graph_open_claim_nodes",
    "proved_claim_nodes": "mini_proof_graph_proved_claim_nodes",
    "rejected_claim_nodes": "mini_proof_graph_rejected_claim_nodes",
    "variant_nodes": "mini_proof_graph_variant_nodes",
    "open_variant_nodes": "mini_proof_graph_open_variant_nodes",
    "proved_variant_nodes": "mini_proof_graph_proved_variant_nodes",
    "rejected_variant_nodes": "mini_proof_graph_rejected_variant_nodes",
    "non_theorem_statement_nodes": "mini_proof_graph_non_theorem_statement_nodes",
    "route_nodes": "mini_proof_graph_route_nodes",
    "open_route_nodes": "mini_proof_graph_open_route_nodes",
    "obligation_nodes": "mini_proof_graph_obligation_nodes",
    "open_obligation_nodes": "mini_proof_graph_open_obligation_nodes",
    "open_attackable_obligation_nodes": "mini_proof_graph_open_attackable_obligation_nodes",
    "open_quarantined_obligation_nodes": "mini_proof_graph_open_quarantined_obligation_nodes",
    "open_promoted_obligation_nodes": "mini_proof_graph_open_promoted_obligation_nodes",
    "replan_queue_nodes": "mini_proof_graph_replan_queue_nodes",
    "open_replan_queue_nodes": "mini_proof_graph_open_replan_queue_nodes",
    "open_attackable_replan_queue_nodes": "mini_proof_graph_open_attackable_replan_queue_nodes",
    "open_quarantined_replan_queue_nodes": "mini_proof_graph_open_quarantined_replan_queue_nodes",
    "open_promoted_replan_queue_nodes": "mini_proof_graph_open_promoted_replan_queue_nodes",
    "scratch_nodes": "mini_proof_graph_scratch_nodes",
    "decl_application_nodes": "mini_proof_graph_decl_application_nodes",
    "closed_decl_applications": "mini_proof_graph_closed_decl_applications",
    "partial_decl_applications": "mini_proof_graph_partial_decl_applications",
    "rejected_decl_applications": "mini_proof_graph_rejected_decl_applications",
    "root_proved": "mini_proof_graph_root_proved",
    "proof_state_nodes": "mini_proof_graph_proof_state_nodes",
    "open_proof_state_nodes": "mini_proof_graph_open_proof_state_nodes",
    "proved_proof_state_nodes": "mini_proof_graph_proved_proof_state_nodes",
    "proof_state_artifact_nodes": "mini_proof_graph_proof_state_artifact_nodes",
    "proof_state_transition_nodes": "mini_proof_graph_proof_state_transition_nodes",
    "proof_state_retrieval_nodes": "mini_proof_graph_proof_state_retrieval_nodes",
    "proof_state_assembly_nodes": "mini_proof_graph_proof_state_assembly_nodes",
    "proof_state_attempt_nodes": "mini_proof_graph_proof_state_attempt_nodes",
    "branch_frames": "mini_proof_graph_branch_frames",
    "open_branch_frames": "mini_proof_graph_open_branch_frames",
    "proved_branch_frames": "mini_proof_graph_proved_branch_frames",
}


_MINI_PROOF_STATE_TO_METRIC_KEY = {
    "total_close_attempts": "mini_proof_state_total_close_attempts",
    "total_tactic_attempts": "mini_proof_state_total_tactic_attempts",
    "total_decl_application_attempts": "mini_proof_state_total_decl_application_attempts",
    "total_assembly_attempts": "mini_proof_state_total_assembly_attempts",
    "cache_hits": "mini_proof_state_cache_hits",
    "budget_skips": "mini_proof_state_budget_skips",
    "retrieval_hit_count": "mini_proof_state_retrieval_hit_count",
    "graph_obligation_child_promotions": (
        "mini_proof_state_graph_obligation_child_promotions"
    ),
    "graph_obligation_child_promotion_reuses": (
        "mini_proof_state_graph_obligation_child_promotion_reuses"
    ),
    "graph_obligation_child_promotion_skipped_quarantined": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_quarantined"
    ),
    "graph_obligation_child_promotion_skipped_untrusted": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_untrusted"
    ),
    "graph_obligation_child_promotion_skipped_formalization_required": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_formalization_required"
    ),
    "graph_obligation_child_promotion_skipped_non_executable": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_non_executable"
    ),
    "graph_obligation_child_promotion_skipped_root_equivalent": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_root_equivalent"
    ),
    "graph_obligation_child_promotion_skipped_rejected": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_rejected"
    ),
    "graph_obligation_child_promotion_skipped_cycle": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_cycle"
    ),
    "graph_obligation_child_promotion_skipped_terminal_parent": (
        "mini_proof_state_graph_obligation_child_promotion_skipped_terminal_parent"
    ),
    "open_child_nodes": "mini_proof_state_open_child_nodes",
    "proved_child_nodes": "mini_proof_state_proved_child_nodes",
    "failed_child_nodes": "mini_proof_state_failed_child_nodes",
    "unverified_decomposition_tasks": (
        "mini_proof_state_unverified_decomposition_tasks"
    ),
    "partial_verified_decomposition_tasks": (
        "mini_proof_state_partial_verified_decomposition_tasks"
    ),
    "proved_decomposition_tasks_with_open_children": (
        "mini_proof_state_proved_decomposition_tasks_with_open_children"
    ),
    "lemma_dag_decomposition_all_candidates_rejected": (
        "mini_proof_state_lemma_dag_decomposition_all_candidates_rejected"
    ),
    "lemma_dag_child_statement_rejections": (
        "mini_proof_state_lemma_dag_child_statement_rejections"
    ),
    "lemma_dag_child_source_rejections": (
        "mini_proof_state_lemma_dag_child_source_rejections"
    ),
    "lemma_dag_parent_stub_spawns": (
        "mini_proof_state_lemma_dag_parent_stub_spawns"
    ),
    "lemma_dag_parent_stub_rejections": (
        "mini_proof_state_lemma_dag_parent_stub_rejections"
    ),
    "failed_proof_residual_batches_quarantined": (
        "mini_proof_state_failed_proof_residual_batches_quarantined"
    ),
    "failed_proof_residual_goals_quarantined": (
        "mini_proof_state_failed_proof_residual_goals_quarantined"
    ),
    "residual_goal_context_filtered": (
        "mini_proof_state_residual_goal_context_filtered"
    ),
    "tactic_pattern_cache_lookups": (
        "mini_proof_state_tactic_pattern_cache_lookups"
    ),
    "tactic_pattern_cache_exact_success_hits": (
        "mini_proof_state_tactic_pattern_cache_exact_success_hits"
    ),
    "tactic_pattern_cache_shape_success_hits": (
        "mini_proof_state_tactic_pattern_cache_shape_success_hits"
    ),
    "tactic_pattern_cache_failed_filtered": (
        "mini_proof_state_tactic_pattern_cache_failed_filtered"
    ),
    "tactic_pattern_cache_all_candidates_pruned": (
        "mini_proof_state_tactic_pattern_cache_all_candidates_pruned"
    ),
    "tactic_pattern_cache_cap_preserved_misses": (
        "mini_proof_state_tactic_pattern_cache_cap_preserved_misses"
    ),
    "tactic_pattern_cache_failures_recorded": (
        "mini_proof_state_tactic_pattern_cache_failures_recorded"
    ),
    "tactic_pattern_cache_failures_not_cached": (
        "mini_proof_state_tactic_pattern_cache_failures_not_cached"
    ),
    "tactic_pattern_cache_successes_recorded": (
        "mini_proof_state_tactic_pattern_cache_successes_recorded"
    ),
    "tactic_pattern_cache_shape_successes_recorded": (
        "mini_proof_state_tactic_pattern_cache_shape_successes_recorded"
    ),
    "tactic_pattern_cache_successes_deferred": (
        "mini_proof_state_tactic_pattern_cache_successes_deferred"
    ),
    "tactic_pattern_cache_acceptance_vetoes": (
        "mini_proof_state_tactic_pattern_cache_acceptance_vetoes"
    ),
    "tactic_pattern_cache_suppressed_filtered": (
        "mini_proof_state_tactic_pattern_cache_suppressed_filtered"
    ),
    "root_tactic_context_attempts": (
        "mini_proof_state_root_tactic_context_attempts"
    ),
    "root_tactic_context_skips": (
        "mini_proof_state_root_tactic_context_skips"
    ),
    "root_tactic_transient_deferrals": (
        "mini_proof_state_root_tactic_transient_deferrals"
    ),
    "root_tactic_transient_retries": (
        "mini_proof_state_root_tactic_transient_retries"
    ),
    "root_tactic_deferred_skips": (
        "mini_proof_state_root_tactic_deferred_skips"
    ),
    "root_tactic_reenabled_by_new_evidence": (
        "mini_proof_state_root_tactic_reenabled_by_new_evidence"
    ),
    "root_tactic_terminal_after_continuation": (
        "mini_proof_state_root_tactic_terminal_after_continuation"
    ),
    "assembly_selected_stale": (
        "mini_proof_state_assembly_selected_stale"
    ),
    "assembly_contracts_created": (
        "mini_proof_state_assembly_contracts_created"
    ),
    "assembly_groups_ready": (
        "mini_proof_state_assembly_groups_ready"
    ),
}

def _mini_proof_graph_metric_record(
    proof_graph_summary: Optional[Dict[str, Any]],
) -> Dict[str, int]:
    summary = dict(proof_graph_summary or {})
    out: Dict[str, int] = {}
    for summary_key, metric_key in _MINI_PROOF_GRAPH_SUMMARY_TO_METRIC_KEY.items():
        try:
            out[metric_key] = int(summary.get(summary_key, 0) or 0)
        except Exception:
            out[metric_key] = 0
    return out


def _mini_proof_state_metric_record(
    proof_state_record: Optional[Dict[str, Any]],
) -> Dict[str, int]:
    metrics = dict((proof_state_record or {}).get("metrics") or {})
    out: Dict[str, int] = {}
    for metric_key, export_key in _MINI_PROOF_STATE_TO_METRIC_KEY.items():
        try:
            out[export_key] = int(metrics.get(metric_key, 0) or 0)
        except Exception:
            out[export_key] = 0
    return out


def _mini_dossier_structural_metric_record(
    dossier: Optional[ProofDossier],
) -> Dict[str, int]:
    if dossier is None:
        return {key: 0 for key in _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS}
    tool_metrics = dict(getattr(dossier, "tool_metrics", {}) or {})
    projection_metrics: Dict[str, int] = {}
    if (
        str(
            getattr(dossier, "graph_execution_projection_mode", "off") or "off"
        ).strip().lower()
        == "shadow"
        and getattr(dossier, "proof_graph", None) is not None
    ):
        from .graph_execution_projection import project_graph_execution_shadow

        projection_report = project_graph_execution_shadow(
            dossier.proof_graph.clone().to_record(),
            project_environment_hash=str(
                getattr(
                    dossier,
                    "graph_execution_project_environment_hash",
                    "",
                )
                or ""
            ),
        )
        projection_counts = projection_report.counts
        projection_metrics = {
            "mini_graph_projection_routes_total": int(
                projection_counts.get("routes_total", 0) or 0
            ),
            "mini_graph_projection_routes_active": int(
                projection_counts.get("routes_active", 0) or 0
            ),
            "mini_graph_projection_debt_before": int(
                projection_counts.get("routes_projection_debt_before", 0) or 0
            ),
            "mini_graph_projection_debt": int(
                projection_counts.get("routes_projection_debt", 0) or 0
            ),
            "mini_graph_projection_executable_obligations": int(
                projection_counts.get("obligations_executable", 0) or 0
            ),
            "mini_graph_projection_work_items": int(
                projection_counts.get("work_items_total", 0) or 0
            ),
            "mini_graph_projection_dangling_dependencies": int(
                projection_counts.get("dangling_required_node_ids", 0) or 0
            ),
        }
    helper_progress = helper_progress_metadata_for_accepted_helpers(
        dossier,
        list((getattr(dossier, "verified_helpers", {}) or {}).keys()),
    )
    theory_lemma_count = len(
        list(helper_progress.get("theory_progress_helper_names") or [])
    )
    parent_progress_obligation_count = len(
        list(helper_progress.get("parent_progress_resolved_obligation_node_ids") or [])
    )
    parent_progress_edge_count = int(
        helper_progress.get("parent_progress_edge_count", 0) or 0
    )
    out = {
        "mini_accepted_proof_stubs": len(
            list(getattr(dossier, "accepted_proof_stubs", []) or [])
        ),
        "mini_session_theory_lemmas_accepted": theory_lemma_count,
        "mini_session_parent_progress_edges": parent_progress_edge_count,
        "mini_session_parent_progress_obligations_proved": parent_progress_obligation_count,
        "mini_parallel_sample_proof_state_snapshots": max(
            len(list(getattr(dossier, "parallel_sample_proof_states", []) or [])),
            int(
                tool_metrics.get("mini_parallel_sample_proof_state_snapshots", 0)
                or 0
            ),
        ),
        "mini_parallel_sample_structural_snapshots": max(
            len(
                [
                    item
                    for item in list(
                        getattr(dossier, "parallel_sample_proof_states", []) or []
                    )
                    if isinstance(item, dict)
                    and isinstance(item.get("graph_structural_summary"), dict)
                ]
            ),
            int(tool_metrics.get("mini_parallel_sample_structural_snapshots", 0) or 0),
        ),
        "mini_parallel_sample_failures": max(
            len(list(getattr(dossier, "parallel_sample_failures", []) or [])),
            int(tool_metrics.get("mini_parallel_sample_failures", 0) or 0),
        ),
        "mini_parallel_samples_zero_completed": int(
            tool_metrics.get("mini_parallel_samples_zero_completed", 0) or 0
        ),
        "mini_apply_decl_tool_state_updates": int(
            tool_metrics.get("mini_apply_decl_tool_state_updates", 0) or 0
        ),
        "mini_apply_decl_tool_state_closures": int(
            tool_metrics.get("mini_apply_decl_tool_state_closures", 0) or 0
        ),
        "mini_lemma_cache_store_errors": int(
            tool_metrics.get("mini_lemma_cache_store_errors", 0) or 0
        ),
        "mini_lemma_cache_deadline_integrity_unrecoverable": int(
            tool_metrics.get("mini_lemma_cache_deadline_integrity_unrecoverable", 0)
            or 0
        ),
        "mini_lemma_cache_ingest_schema_migrated": int(
            tool_metrics.get("mini_lemma_cache_ingest_schema_migrated", 0) or 0
        ),
        "mini_lemma_cache_ingest_schema_rejected": int(
            tool_metrics.get("mini_lemma_cache_ingest_schema_rejected", 0) or 0
        ),
        "mini_lemma_cache_ingest_quality_rejected": int(
            tool_metrics.get("mini_lemma_cache_ingest_quality_rejected", 0) or 0
        ),
        "mini_lemma_cache_ingest_projection_rejected": int(
            tool_metrics.get("mini_lemma_cache_ingest_projection_rejected", 0) or 0
        ),
        "mini_lemma_cache_ingest_policy_rejected": int(
            tool_metrics.get("mini_lemma_cache_ingest_policy_rejected", 0) or 0
        ),
        "mini_lemma_cache_ingest_field_rejected": int(
            tool_metrics.get("mini_lemma_cache_ingest_field_rejected", 0) or 0
        ),
        "mini_lemma_cache_ingest_owner_deduped": int(
            tool_metrics.get("mini_lemma_cache_ingest_owner_deduped", 0) or 0
        ),
        "mini_search_pre_retrieved_duplicates_suppressed": int(
            tool_metrics.get(
                "mini_search_pre_retrieved_duplicates_suppressed",
                0,
            )
            or 0
        ),
        "mini_hollow_root_reducers_detected": int(
            tool_metrics.get("mini_hollow_root_reducers_detected", 0) or 0
        ),
        "mini_hollow_root_reducers_reenabled_by_premise": int(
            tool_metrics.get("mini_hollow_root_reducers_reenabled_by_premise", 0)
            or 0
        ),
        "mini_negative_evidence_helpers_withheld": int(
            tool_metrics.get("mini_negative_evidence_helpers_withheld", 0) or 0
        ),
        "mini_graph_hollow_reducer_certificates_blocked": int(
            tool_metrics.get("mini_graph_hollow_reducer_certificates_blocked", 0)
            or 0
        ),
        "mini_graph_negative_evidence_certificates_blocked": int(
            tool_metrics.get(
                "mini_graph_negative_evidence_certificates_blocked",
                0,
            )
            or 0
        ),
        "mini_graph_negative_evidence_exact_certificates_accepted": int(
            tool_metrics.get(
                "mini_graph_negative_evidence_exact_certificates_accepted",
                0,
            )
            or 0
        ),
        "mini_graph_negative_evidence_contradicted_targets": int(
            tool_metrics.get(
                "mini_graph_negative_evidence_contradicted_targets",
                0,
            )
            or 0
        ),
        "mini_graph_negative_evidence_contradicted_routes": int(
            tool_metrics.get(
                "mini_graph_negative_evidence_contradicted_routes",
                0,
            )
            or 0
        ),
        "mini_session_assemble_route_conversation_rejected": int(
            tool_metrics.get("mini_session_assemble_route_conversation_rejected", 0)
            or 0
        ),
        "mini_session_assemble_route_static_conversation_suppressed": int(
            tool_metrics.get(
                "mini_session_assemble_route_static_conversation_suppressed",
                0,
            )
            or 0
        ),
        "mini_session_unscoped_root_authoring_suppressed": int(
            tool_metrics.get("mini_session_unscoped_root_authoring_suppressed", 0)
            or 0
        ),
        "mini_session_graph_route_no_replayable_helpers": int(
            tool_metrics.get("mini_session_graph_route_no_replayable_helpers", 0) or 0
        ),
        "mini_session_graph_route_contract_blocked": int(
            tool_metrics.get("mini_session_graph_route_contract_blocked", 0) or 0
        ),
        "mini_root_assembly_contract_blocked": int(
            tool_metrics.get("mini_root_assembly_contract_blocked", 0) or 0
        ),
        "mini_session_graph_route_authoring_requested": int(
            tool_metrics.get("mini_session_graph_route_authoring_requested", 0) or 0
        ),
        "mini_session_graph_route_authoring_failed": int(
            tool_metrics.get("mini_session_graph_route_authoring_failed", 0) or 0
        ),
    }
    for key in _MINI_GRAPH_RECURSIVE_DECOMPOSE_METRIC_KEYS:
        out[key] = int(tool_metrics.get(key, 0) or 0)
    for key in _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS:
        out.setdefault(key, int(tool_metrics.get(key, 0) or 0))
    out.update(projection_metrics)
    return out


# ---------------------------------------------------------------------------
# Provider config. Three providers wired by env vars.
# ---------------------------------------------------------------------------

_DEFAULT_MODELS = {
    "openai": "gpt-5.2",
    "deepseek": "deepseek-v4-pro",
    "openrouter": "",
}

_PROVIDER_BASE_URLS = {
    "openai": "https://api.openai.com/v1",
    "deepseek": "https://api.deepseek.com/v1",
    "openrouter": "https://openrouter.ai/api/v1",
}

_PROVIDER_ENV_VARS = {
    "openai": "OPENAI_API_KEY",
    "deepseek": "DEEPSEEK_API_KEY",
    "openrouter": "OPENROUTER_API_KEY",
}
_REASONING_PROVIDER_DEFAULT = "provider-default"
_MINI_THEORY_MODE_DEFAULT = "build"


def _effective_mini_theory_mode(args: argparse.Namespace) -> str:
    """Resolve the operational theory mode."""

    requested = str(getattr(args, "mini_theory_mode", None) or "").strip()
    if requested:
        return requested
    return _MINI_THEORY_MODE_DEFAULT


_REASONING_MODE_CHOICES = (_REASONING_PROVIDER_DEFAULT, "auto", "on", "off")
_REASONING_EFFORT_CHOICES = ("none", "low", "medium", "high", "max")
_LLM_DEADLINE_POLICY_CHOICES = ("soft", "hard")
_LLM_REQUEST_TIMEOUT_DISABLED = "disabled"
_LLM_REQUEST_TIMEOUT_DISABLED_ALIASES = {
    "none",
    "off",
    "disabled",
    "disable",
    "unbounded",
    "infinite",
}


def _routed_model_name(model: Optional[str]) -> str:
    """Return a transport-namespace-independent model identifier."""

    name = str(model or "").strip().lower()
    if "/" in name:
        name = name.rsplit("/", 1)[-1].strip()
    return name


def _canonical_openrouter_model_id(model: str) -> str:
    """Expand supported OpenRouter shorthand to its transport model ID.

    OpenRouter's catalog and request API use provider-namespaced IDs. The CLI
    historically accepted aliases that could reach pricing preflight without
    a routable provider ID. Canonicalize only the exact supported aliases and
    the unambiguous, unnamespaced OpenAI GPT family.
    """

    return canonical_openrouter_model_id(model)


def _model_token_defaults(model: Optional[str]) -> Tuple[Optional[int], int]:
    """Return (context_window, max_tokens) defaults for a given model name.

    Per-model overrides handle frontier models whose context/output limits
    differ from the system-wide default of (None, 8192). Unknown models
    fall through to the safe default.

    DeepSeek-V4: 1,000,000 token context, 384,000 max output tokens.
    GPT-5.2: 400,000 token context, 128,000 max output tokens.
    GPT-5.6: 1,050,000 token context, 128,000 max output tokens.
    """
    # OpenRouter IDs are namespaced as ``provider/model``. Capability matching
    # is about the routed model, not the transport namespace.
    name = _routed_model_name(model)
    if name.startswith("deepseek-v4"):
        return 1_000_000, 384_000
    if name.startswith("gpt-5.2"):
        return 400_000, 128_000
    if name.startswith("gpt-5.6"):
        return 1_050_000, 128_000
    return None, 8192


def _model_timeout_default(
    model: Optional[str],
    *,
    provider: Optional[str] = None,
) -> float:
    name = _routed_model_name(model)
    provider_name = str(provider or "").strip().lower()
    if name.startswith("deepseek-v4"):
        return 600.0
    if provider_name == "openrouter" or "qwen" in name:
        return 1200.0
    return 300.0


def _make_role_cfg(
    provider: str,
    model: Optional[str],
    *,
    role_name: str,
    timeout_s: Optional[float] = None,
    llm_deadline_policy: str = "soft",
    request_timeout_s: Optional[float] = None,
    request_timeout_disabled: Optional[bool] = None,
) -> RoleConfig:
    provider = provider.lower()
    if provider not in _DEFAULT_MODELS:
        raise SystemExit(f"Unknown provider: {provider}")
    api_key = os.environ.get(_PROVIDER_ENV_VARS[provider], "").strip()
    if not api_key:
        raise SystemExit(
            f"{_PROVIDER_ENV_VARS[provider]} is not set in the environment."
        )
    resolved_model = str(model or _DEFAULT_MODELS[provider] or "").strip()
    if not resolved_model:
        raise SystemExit(
            f"{provider} requires an explicit model for {role_name}; "
            f"pass --{role_name}-model (for example, an OpenRouter model id)."
        )
    if provider == "openrouter":
        resolved_model = _canonical_openrouter_model_id(resolved_model)
    context_window, max_out = _model_token_defaults(resolved_model)
    if timeout_s is None:
        timeout_s = _model_timeout_default(resolved_model, provider=provider)
    try:
        timeout_f = float(timeout_s)
    except Exception as exc:
        raise SystemExit(f"{role_name} timeout must be a number: {timeout_s!r}") from exc
    if not math.isfinite(timeout_f) or timeout_f <= 0.0:
        raise SystemExit(
            f"{role_name} timeout must be a finite number > 0, got {timeout_f}"
        )
    clean_deadline_policy = str(llm_deadline_policy or "soft").strip().lower()
    if clean_deadline_policy not in _LLM_DEADLINE_POLICY_CHOICES:
        raise SystemExit(
            "LLM deadline policy must be one of "
            f"{', '.join(_LLM_DEADLINE_POLICY_CHOICES)}, "
            f"got {llm_deadline_policy!r}"
        )
    request_timeout_f: Optional[float] = None
    if request_timeout_s is not None:
        try:
            request_timeout_f = float(request_timeout_s)
        except Exception as exc:
            raise SystemExit(
                f"{role_name} request timeout must be a number: {request_timeout_s!r}"
            ) from exc
        if not math.isfinite(request_timeout_f) or request_timeout_f <= 0.0:
            raise SystemExit(
                f"{role_name} request timeout must be a finite number > 0, "
                f"got {request_timeout_f}"
            )
    if request_timeout_disabled is None:
        # Search lifetime and one provider operation are different budgets.
        # Soft policy may ignore a phase deadline, but an individual HTTP
        # request must still have a watchdog or one wedged socket can freeze an
        # otherwise resumable multi-day search.  The role/model timeout is the
        # default operation lease.  Explicit ``off`` remains available via the
        # request-timeout CLI parser and arrives here as disabled=True.
        request_timeout_disabled = False
    if not bool(request_timeout_disabled) and request_timeout_f is None:
        request_timeout_f = timeout_f
    if bool(request_timeout_disabled):
        request_timeout_f = None
    cfg = RoleConfig(
        name=role_name,
        base_url=_PROVIDER_BASE_URLS[provider],
        model=resolved_model,
        api_key=api_key,
        temperature=0.6,
        top_p=0.95,
        max_tokens=max_out,
        context_window=context_window,
        timeout_s=timeout_f,
    )
    setattr(cfg, "llm_deadline_policy", clean_deadline_policy)
    setattr(cfg, "request_timeout_s", request_timeout_f)
    setattr(cfg, "request_timeout_disabled", bool(request_timeout_disabled))
    return cfg


def _normalize_reasoning_cli_mode(mode: Optional[str]) -> str:
    clean_mode = str(mode or _REASONING_PROVIDER_DEFAULT).strip().lower()
    if clean_mode == "auto":
        clean_mode = _REASONING_PROVIDER_DEFAULT
    if clean_mode not in _REASONING_MODE_CHOICES:
        raise SystemExit(
            "reasoning mode must be one of "
            f"{', '.join(_REASONING_MODE_CHOICES)}, got {mode!r}"
        )
    return clean_mode


def _reasoning_role_cli_settings(
    args: Any,
    role_name: str,
) -> Tuple[str, Optional[str]]:
    role_mode = getattr(args, f"{role_name}_reasoning_mode", None)
    if role_mode is None:
        role_mode = getattr(args, "reasoning_mode", _REASONING_PROVIDER_DEFAULT)
    role_effort = getattr(args, f"{role_name}_reasoning_effort", None)
    if role_effort is None:
        role_effort = getattr(args, "reasoning_effort", None)
    return _normalize_reasoning_cli_mode(role_mode), role_effort


def _apply_reasoning_cli_override(
    cfg: RoleConfig,
    *,
    mode: str = _REASONING_PROVIDER_DEFAULT,
    effort: Optional[str] = None,
) -> None:
    """Apply explicit mini-prover reasoning controls to a role config."""
    clean_mode = _normalize_reasoning_cli_mode(mode)
    clean_effort = str(effort or "").strip().lower() or None
    if clean_effort is not None and clean_effort not in _REASONING_EFFORT_CHOICES:
        raise SystemExit(
            "reasoning effort must be one of "
            f"{', '.join(_REASONING_EFFORT_CHOICES)}, got {effort!r}"
        )

    if clean_mode == "off" and clean_effort not in {None, "none"}:
        raise SystemExit(
            "--reasoning-mode off cannot be combined with "
            f"--reasoning-effort {clean_effort}"
        )
    if clean_mode == "on" and clean_effort == "none":
        raise SystemExit(
            "--reasoning-mode on cannot be combined with --reasoning-effort none"
        )

    if clean_mode == _REASONING_PROVIDER_DEFAULT and clean_effort is None:
        setattr(cfg, "reasoning_requested_mode", clean_mode)
        setattr(cfg, "reasoning_requested_effort", "")
        return
    setattr(cfg, "reasoning_requested_mode", clean_mode)
    setattr(cfg, "reasoning_requested_effort", str(clean_effort or ""))
    cfg.reasoning_control_required = True
    if clean_mode == "off":
        clean_effort = "none"
    elif clean_mode == "on" and clean_effort is None:
        clean_effort = "medium"

    if clean_effort == "none":
        if base_url_matches_provider(cfg.base_url, "deepseek"):
            cfg.reasoning_effort = None
            cfg.thinking_enabled = False
        else:
            cfg.reasoning_effort = "none"
        return

    if clean_effort is not None:
        cfg.reasoning_effort = clean_effort
    if base_url_matches_provider(cfg.base_url, "deepseek"):
        cfg.thinking_enabled = True


async def _preflight_mini_reasoning_contract_or_defer(
    client: Any,
    *,
    role: str,
) -> List[Dict[str, Any]]:
    """Keep transient capability discovery inside Mini's retry contract."""

    try:
        return await preflight_mini_reasoning_contract(client, role=role)
    except MiniReasoningCapabilityUnavailable as exc:
        cfg = getattr(client, "cfg", None)
        record = {
            "role": str(role or "llm"),
            "model": str(getattr(cfg, "model", "") or ""),
            "base_url": str(getattr(cfg, "base_url", "") or ""),
            "requested_mode": str(
                getattr(cfg, "reasoning_requested_mode", "provider-default")
                or "provider-default"
            ),
            "requested_effort": str(
                getattr(cfg, "reasoning_effort", "") or ""
            ),
            "resolution": "deferred_capability_unavailable",
            "transport_mode": "not_dispatched",
            "retryable": True,
            "error_type": type(exc).__name__,
            "error": str(exc),
        }
        try:
            setattr(cfg, "reasoning_preflight_record", dict(record))
        except Exception:
            pass
        print(
            "[mini_prover] reasoning capability preflight deferred for "
            f"{role}: {exc}",
            flush=True,
        )
        return [record]


def _reasoning_cli_summary(
    cfg: Optional[RoleConfig],
    *,
    provider: Optional[str],
    requested_mode: str,
    requested_effort: Optional[str],
) -> Optional[Dict[str, Any]]:
    if cfg is None:
        return None
    return {
        "provider": str(provider or ""),
        "model": str(getattr(cfg, "model", "") or ""),
        "requested_mode": _normalize_reasoning_cli_mode(requested_mode),
        "requested_effort": str(requested_effort or ""),
        "resolved_reasoning_effort": str(getattr(cfg, "reasoning_effort", "") or ""),
        "resolved_thinking_enabled": bool(getattr(cfg, "thinking_enabled", False)),
        "reasoning_control_required": bool(
            getattr(cfg, "reasoning_control_required", False)
        ),
        "reasoning_preflight": dict(
            getattr(cfg, "reasoning_preflight_record", {}) or {}
        ),
    }


def _llm_deadline_cli_summary(cfg: Optional[RoleConfig]) -> Optional[Dict[str, Any]]:
    if cfg is None:
        return None
    request_timeout_disabled = bool(
        getattr(cfg, "request_timeout_disabled", False)
    )
    request_timeout_override = getattr(cfg, "request_timeout_s", None)
    effective_request_timeout = None
    if not request_timeout_disabled:
        effective_request_timeout = (
            float(request_timeout_override)
            if request_timeout_override is not None
            else float(getattr(cfg, "timeout_s", 0.0) or 0.0)
        )
    return {
        "policy": str(getattr(cfg, "llm_deadline_policy", "hard") or "hard"),
        "role_timeout_s": float(getattr(cfg, "timeout_s", 0.0) or 0.0),
        "request_timeout_s": effective_request_timeout,
        "request_timeout_override_s": (
            float(request_timeout_override)
            if request_timeout_override is not None
            else None
        ),
        "request_timeout_disabled": request_timeout_disabled,
        "operation_timeout_s": (
            float(getattr(cfg, "operation_timeout_s"))
            if getattr(cfg, "operation_timeout_s", None) is not None
            else None
        ),
    }


def _run_reasoning_config_record(
    *,
    args: Any,
    prover_cfg: Optional[RoleConfig],
    refiner_cfg: Optional[RoleConfig],
    prover_reasoning_mode: str,
    prover_reasoning_effort: Optional[str],
    refiner_reasoning_mode: str,
    refiner_reasoning_effort: Optional[str],
) -> Dict[str, Any]:
    return {
        "phase": "run_config",
        "verdict": "config_recorded",
        "reasoning_mode": _normalize_reasoning_cli_mode(
            getattr(args, "reasoning_mode", _REASONING_PROVIDER_DEFAULT)
        ),
        "reasoning_effort": str(getattr(args, "reasoning_effort", None) or ""),
        "prover_reasoning_mode": prover_reasoning_mode,
        "prover_reasoning_effort": str(prover_reasoning_effort or ""),
        "refiner_reasoning_mode": refiner_reasoning_mode,
        "refiner_reasoning_effort": str(refiner_reasoning_effort or ""),
        "prover_reasoning": _reasoning_cli_summary(
            prover_cfg,
            provider=getattr(args, "prover", None),
            requested_mode=prover_reasoning_mode,
            requested_effort=prover_reasoning_effort,
        ),
        "refiner_reasoning": _reasoning_cli_summary(
            refiner_cfg,
            provider=getattr(args, "refiner", None),
            requested_mode=refiner_reasoning_mode,
            requested_effort=refiner_reasoning_effort,
        ),
        "llm_deadline_policy": str(
            getattr(args, "llm_deadline_policy", "soft") or "soft"
        ),
        "prover_llm_deadline_policy": (
            str(getattr(prover_cfg, "llm_deadline_policy", ""))
            if prover_cfg
            else ""
        ),
        "refiner_llm_deadline_policy": (
            str(getattr(refiner_cfg, "llm_deadline_policy", ""))
            if refiner_cfg
            else ""
        ),
        "prover_llm_deadline": _llm_deadline_cli_summary(prover_cfg),
        "refiner_llm_deadline": _llm_deadline_cli_summary(refiner_cfg),
        "mini_worker_timeout_s": float(
            getattr(args, "mini_worker_timeout_s", 0.0) or 0.0
        ),
        "mini_run_wall_clock_budget_s": float(
            getattr(args, "mini_run_wall_clock_budget_s", 0.0) or 0.0
        ),
        "mini_no_strong_progress_budget_s": float(
            getattr(args, "mini_no_strong_progress_budget_s", 0.0) or 0.0
        ),
        "mini_worker_startup_timeout_s": float(
            getattr(args, "mini_worker_startup_timeout_s", 0.0) or 0.0
        ),
        "mini_worker_shutdown_timeout_s": float(
            getattr(args, "mini_worker_shutdown_timeout_s", 0.0) or 0.0
        ),
        "mini_hard_operation_watchdog": bool(
            getattr(args, "mini_hard_operation_watchdog", False)
        ),
    }


# ---------------------------------------------------------------------------
# CLI entry.
# ---------------------------------------------------------------------------

def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="mini_prover",
        description=(
            "End-to-end autonomous recursive Lean prover (theory test bed). "
            "Mini-session scheduling, recursive helpers, deterministic "
            "prepasses, and turn-by-turn Lean feedback."
        ),
        epilog=(
            "Reasoning controls:\n"
            "  The default --reasoning-mode provider-default (alias: auto) "
            "sends no reasoning/thinking field, so the provider/model default "
            "applies. This is not the same as off.\n"
            "  --disable-reasoning / --reasoning-mode off sends an explicit "
            "disable request. Explicit controls are required to stick; if a "
            "provider rejects the reasoning/thinking field, the run fails "
            "instead of silently retrying without the control.\n"
            "  Use --prover-reasoning-* and --refiner-reasoning-* to set "
            "different policies per role. Each run records the resolved config "
            "at startup in run_config and prints a 'Reasoning controls: ...' "
            "line before long LLM work.\n"
            "  reasoning_output_tokens=0 on successful usage records confirms "
            "the provider reported no hidden reasoning tokens.\n"
            "LLM deadline policy:\n"
            "  The default --llm-deadline-policy soft is patient for "
            "OpenRouter/long-reasoning calls: phase/retry deadlines do not "
            "kill an in-flight generation and are not a local total-operation "
            "kill switch. Each HTTP request retains the finite role/model "
            "watchdog unless --llm-request-timeout-s off (or a role-scoped "
            "equivalent) explicitly disables it.\n"
            "  Use --llm-deadline-policy hard for fail-fast experiments that "
            "reject a late LLM/tool-loop operation at the role or phase "
            "deadline; it does not cap the overall MiniSession run.\n"
            "Terminal trace controls:\n"
            "  --terminal-trace compact is the default: startup lines, session "
            "heartbeats, verdict summaries, and truncated assistant text.\n"
            "  --terminal-trace full keeps the readable trace but prints "
            "untruncated assistant responses.\n"
            "  --terminal-trace jsonl mirrors every turns.jsonl record to the "
            "terminal, including prompts, responses, tool logs, provider "
            "attempts, Lean metadata, and scheduler events.\n"
            "  --terminal-trace off disables structured live trace lines while "
            "still writing run.log, turns.jsonl, activation_telemetry.json, "
            "and summary.json."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    input_group = p.add_mutually_exclusive_group(required=True)
    input_group.add_argument(
        "--lean-file",
        default=None,
        help="Path to an arbitrary Lean source file containing the target theorem.",
    )
    input_group.add_argument(
        "--putnam-file",
        default=None,
        help=(
            "PutnamBench compatibility adapter. The source is normalized into "
            "the same theorem-project request used by --lean-file."
        ),
    )
    p.add_argument(
        "--theorem-name",
        default=None,
        help=(
            "Fully qualified target theorem name. Required with --lean-file; "
            "the PutnamBench adapter retains its legacy first-theorem default."
        ),
    )
    p.add_argument(
        "--prover",
        default="deepseek",
        choices=["openai", "deepseek", "openrouter"],
        help="Provider for the prover role.",
    )
    p.add_argument("--prover-model", default=None)
    p.add_argument(
        "--refiner",
        default=None,
        choices=["openai", "deepseek", "openrouter"],
        help=(
            "Optional refiner provider. When set, the refiner role takes over "
            "the transcript after prover stalls; it may use the same provider "
            "and model as the prover."
        ),
    )
    p.add_argument("--refiner-model", default=None)
    p.add_argument(
        "--planner-escalation",
        default="auto",
        choices=["auto", "openai", "deepseek", "openrouter", "off"],
        help=(
            "Escalation provider for the recursive planner. After a "
            "degenerate (empty/unparseable) planning response, the next "
            "planner call uses this stronger role instead of the prover "
            "model (bounded by planner_escalation_max_calls per attempt). "
            "'auto' (default) uses the OpenAI API when OPENAI_API_KEY is set "
            "and otherwise disables escalation with a warning; an explicit "
            "provider fails loudly if its key is missing; 'off' disables."
        ),
    )
    p.add_argument(
        "--planner-escalation-model",
        default="gpt-5.6-terra",
        help="Model for the planner-escalation role.",
    )
    p.add_argument(
        "--reasoning-mode",
        choices=list(_REASONING_MODE_CHOICES),
        default=_REASONING_PROVIDER_DEFAULT,
        help=(
            "Reasoning control for prover/refiner roles. 'provider-default' "
            "sends no explicit control and lets the provider/model default apply "
            "(not the same as off); 'off' explicitly disables reasoning/thinking "
            "where supported and is fail-closed if rejected; 'on' requests "
            "reasoning at --reasoning-effort or medium. "
            "'auto' is accepted as an alias for provider-default."
        ),
    )
    p.add_argument(
        "--disable-reasoning",
        dest="reasoning_mode",
        action="store_const",
        const="off",
        help="Shortcut for --reasoning-mode off.",
    )
    p.add_argument(
        "--enable-reasoning",
        dest="reasoning_mode",
        action="store_const",
        const="on",
        help="Shortcut for --reasoning-mode on.",
    )
    p.add_argument(
        "--reasoning-effort",
        choices=list(_REASONING_EFFORT_CHOICES),
        default=None,
        help=(
            "Optional provider reasoning effort override. 'none' is an explicit "
            "off request for providers with an off switch; failed calls may not "
            "return usage, so use run_config plus successful llm_usage records "
            "to audit effective behavior."
        ),
    )
    p.add_argument(
        "--prover-reasoning-mode",
        choices=list(_REASONING_MODE_CHOICES),
        default=None,
        help="Override --reasoning-mode for the prover role.",
    )
    p.add_argument(
        "--prover-reasoning-effort",
        choices=list(_REASONING_EFFORT_CHOICES),
        default=None,
        help="Override --reasoning-effort for the prover role.",
    )
    p.add_argument(
        "--refiner-reasoning-mode",
        choices=list(_REASONING_MODE_CHOICES),
        default=None,
        help="Override --reasoning-mode for the refiner role.",
    )
    p.add_argument(
        "--refiner-reasoning-effort",
        choices=list(_REASONING_EFFORT_CHOICES),
        default=None,
        help="Override --reasoning-effort for the refiner role.",
    )
    p.add_argument(
        "--llm-timeout-s",
        type=_positive_finite_float_arg,
        default=None,
        help=(
            "Default per-request HTTP watchdog for both roles. "
            "Defaults are model/provider-specific (OpenRouter or Qwen: "
            "1200s; DeepSeek-V4: 600s; others: 300s)."
        ),
    )
    p.add_argument(
        "--prover-timeout-s",
        type=_positive_finite_float_arg,
        default=None,
        help="Override per-request LLM HTTP patience for the prover role only.",
    )
    p.add_argument(
        "--refiner-timeout-s",
        type=_positive_finite_float_arg,
        default=None,
        help="Override per-request LLM HTTP patience for the refiner role only.",
    )
    p.add_argument(
        "--llm-request-timeout-s",
        type=_llm_request_timeout_arg,
        default=None,
        help=(
            "HTTP response timeout for both roles. Use a finite number of "
            "seconds to bound provider reads, or 'none'/'off'/'unbounded' to "
            "wait indefinitely after connect. Default: the finite role/model "
            "timeout in both soft and hard deadline modes."
        ),
    )
    p.add_argument(
        "--prover-request-timeout-s",
        type=_llm_request_timeout_arg,
        default=None,
        help="Override HTTP response timeout for the prover role only.",
    )
    p.add_argument(
        "--refiner-request-timeout-s",
        type=_llm_request_timeout_arg,
        default=None,
        help="Override HTTP response timeout for the refiner role only.",
    )
    p.add_argument(
        "--llm-deadline-policy",
        choices=list(_LLM_DEADLINE_POLICY_CHOICES),
        default="soft",
        help=(
            "Local deadline policy for prover/refiner LLM calls. 'soft' "
            "keeps waiting for provider responses across phase/retry "
            "deadlines; 'hard' bounds one LLM/tool-loop operation and "
            "rejects its late result without ending the MiniSession run."
        ),
    )
    p.add_argument(
        "--max-prove-turns",
        type=int,
        default=30,
        help="Maximum direct prover conversation turns (default: %(default)s).",
    )
    p.add_argument(
        "--max-refine-turns",
        type=int,
        default=25,
        help="Maximum refiner conversation turns (default: %(default)s).",
    )
    p.add_argument(
        "--cost-budget-usd",
        type=float,
        default=0.0,
        help=(
            "Optional MiniSession LLM dollar budget. 0 disables budget stops "
            "while still recording request-scoped usage/cost when available."
        ),
    )
    p.add_argument(
        "--cost-budget-reserve-output-tokens",
        type=int,
        default=1024,
        help=(
            "Output-token reserve used for pre-dispatch dollar-budget checks. "
            "Final cost uses provider-reported usage when present."
        ),
    )
    p.add_argument(
        "--project-path",
        "--lean-project-dir",
        dest="lean_project_dir",
        default=None,
        help=(
            "Lake project used for compilation. Required with --lean-file. "
            "--lean-project-dir is retained as a compatibility alias; the "
            "Putnam adapter can infer its project from the source path."
        ),
    )
    p.add_argument(
        "--import",
        dest="theorem_project_imports",
        action="append",
        default=[],
        help=(
            "Additional Lean module imported into every target check. Repeat "
            "for multiple modules."
        ),
    )
    p.add_argument(
        "--supporting-source-dir",
        "--source-dir",
        dest="theorem_project_source_dirs",
        action="append",
        default=[],
        help=(
            "Supporting Lean source root. Project-declared roots are indexed. "
            "An external root must belong to an identifiable Lake project; its "
            "owning Lake project may be built during preflight, and verification "
            "requires current .olean modules after a successful build. Repeatable."
        ),
    )
    description_group = p.add_mutually_exclusive_group()
    description_group.add_argument(
        "--description",
        dest="theorem_project_description",
        default=None,
        help="Optional natural-language theorem description.",
    )
    description_group.add_argument(
        "--description-file",
        dest="theorem_project_description_file",
        default=None,
        help="UTF-8 file containing the optional natural-language description.",
    )
    p.add_argument(
        "--lean-timeout-s",
        type=int,
        # Bumped from 60 → 300 after deterministic timeouts on a slow
        # elaboration. At 60s the LLM rationalized via solution placeholders
        # blaming "deterministic timeout (as shown by the tool feedback)".
        # 300s is the comfortable upper bound; if proofs complete below
        # budget the higher cap is harmless. Override per-run via
        # --lean-timeout-s.
        default=300,
        help="Per-Lean-check wall-clock cap (seconds).",
    )
    p.add_argument(
        "--lean-max-heartbeats",
        type=int,
        # Lean's `maxHeartbeats` default is 200000 which exhausts before
        # tsum elaboration completes on ℕ+/ℚ goals. 1.6M is 2× the
        # TacticOracleConfig budget already used by lean-native search,
        # giving comfortable headroom for measure-theoretic elaboration.
        # If proofs complete below budget the higher cap is harmless.
        default=1600000,
        help=(
            "set_option maxHeartbeats budget for proof verification. "
            "Bump higher (e.g. 3200000) for unusually heavy elaboration."
        ),
    )
    p.add_argument(
        "--output-dir",
        default=None,
        help=(
            "Directory for run.log + turns.jsonl + activation_telemetry.json "
            "+ summary.json. Default: runs/mini_prover/<theorem>_<timestamp>/."
        ),
    )
    p.add_argument(
        "--terminal-trace",
        choices=("compact", "full", "jsonl", "off"),
        default="compact",
        help=(
            "Live terminal trace detail. compact prints the current heartbeat "
            "with truncated assistant text; full prints readable trace lines "
            "with untruncated assistant responses; jsonl mirrors every "
            "turns.jsonl record to the terminal; off disables structured live "
            "trace lines while still writing artifacts."
        ),
    )
    p.add_argument(
        "--api-search",
        dest="api_search",
        action="store_true",
        default=True,
        help=(
            "Enable Mathlib API search as a tool the prover (and refiner) may "
            "invoke. Builds a local BM25 index over Mathlib (cached after first "
            "run). Enabled by default (default: on)."
        ),
    )
    p.add_argument(
        "--no-api-search",
        dest="api_search",
        action="store_false",
        help=(
            "Disable Mathlib API search. The CLI default is --api-search on."
        ),
    )
    p.add_argument(
        "--mathematical-retrieval",
        dest="mathematical_retrieval",
        action="store_true",
        default=True,
        help=(
            "Enable Mini's federated mathematical retrieval service over the "
            "static Mathlib API, the active Lean project, additional explicit "
            "project/support roots, and compatible published Mini theory "
            "(default: on)."
        ),
    )
    p.add_argument(
        "--no-mathematical-retrieval",
        dest="mathematical_retrieval",
        action="store_false",
        help="Use the legacy static Mathlib searcher without federated retrieval.",
    )
    p.add_argument(
        "--mini-retrieval-project-root",
        dest="mini_retrieval_project_roots",
        action="append",
        default=[],
        help=(
            "Explicit Lean source root to index as a project/support library. "
            "Repeat for multiple roots. The active --lean-project-dir is also "
            "indexed by default; use --no-mini-retrieval-include-lean-project "
            "to opt out."
        ),
    )
    p.add_argument(
        "--mini-retrieval-include-lean-project",
        dest="mini_retrieval_include_lean_project",
        action="store_true",
        default=True,
        help=(
            "Index --lean-project-dir as a project library (default: on). The "
            "active theorem declaration and source file remain held out."
        ),
    )
    p.add_argument(
        "--no-mini-retrieval-include-lean-project",
        dest="mini_retrieval_include_lean_project",
        action="store_false",
        help="Disable automatic indexing of --lean-project-dir.",
    )
    p.add_argument(
        "--mini-retrieval-cache-root",
        type=str,
        default=str(_PROJECT_ROOT / "runs" / "mini_retrieval"),
        help="Persistent root for versioned project retrieval indexes.",
    )
    p.add_argument(
        "--no-mini-retrieval-semantic",
        dest="mini_retrieval_semantic",
        action="store_false",
        default=True,
        help=(
            "Disable sentence-transformer semantic scoring for project/support "
            "retrieval roots; lexical and type-directed channels remain active."
        ),
    )
    p.add_argument(
        "--mini-retrieval-dense",
        dest="mini_retrieval_dense",
        action="store_true",
        default=True,
        help=(
            "Build/load a persistent dense matrix for project/support roots. "
            "Enabled by default; first construction may be expensive."
        ),
    )
    p.add_argument(
        "--no-mini-retrieval-dense",
        dest="mini_retrieval_dense",
        action="store_false",
        help="Disable project dense retrieval while retaining lexical/semantic/type channels.",
    )
    p.add_argument(
        "--no-mini-retrieval-type-directed",
        dest="mini_retrieval_type_directed",
        action="store_false",
        default=True,
        help="Disable the federated declaration type-shape channel.",
    )
    p.add_argument(
        "--no-lean-check-tool",
        dest="lean_check_tool",
        action="store_false",
        default=True,
        help=(
            "Disable the answer-safe Lean #check tool. By default the prover can "
            "call check_lean to verify declaration names instead of asking the "
            "user to run #check."
        ),
    )
    p.add_argument(
        "--no-try-lean-tool",
        dest="try_lean_tool",
        action="store_false",
        default=True,
        help=(
            "Disable the answer-safe try_lean scratch verifier. By default the "
            "prover can call try_lean to test a proof body against the current "
            "goal before committing a final answer."
        ),
    )
    p.add_argument(
        "--no-compute-examples-tool",
        dest="compute_examples_tool",
        action="store_false",
        default=True,
        help=(
            "Disable the answer-safe compute_examples observation tool. By "
            "default the prover can ask Lean to evaluate bounded pure #eval, "
            "#reduce, and #check snippets for small-case exploration. Results "
            "are observations only and never count as proof evidence."
        ),
    )
    p.add_argument(
        "--max-tool-calls-per-turn",
        type=int,
        default=60,
        help=(
            "Cap on search_mathlib/check_lean/try_lean/compute_examples "
            "tool calls within a single conversational turn (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--raw-feedback",
        action="store_true",
        help=(
            "A/B path: feed the raw Lean compiler output verbatim instead of "
            "the structured FailureAnalyzer rendering. Answer-safe gating is "
            "preserved (we still skip raw output when only the full check has "
            "diagnostics and the answer-safe recheck accepted)."
        ),
    )
    p.add_argument(
        "--proof-state-retrieval",
        dest="proof_state_retrieval",
        action="store_true",
        default=False,
        help=(
            "Enable the proof_state_retrieval scheduler action, which mines "
            "Mathlib for open proof-state nodes ahead of root repair. Disabled "
            "by default: it precedes root repair in the static prepass set. "
            "In-turn repair retrieval is governed separately by "
            "--no-repair-retrieval."
        ),
    )
    p.add_argument(
        "--no-proof-state-retrieval",
        dest="proof_state_retrieval",
        action="store_false",
        default=False,
        help=(
            "Explicitly disable the proof_state_retrieval scheduler action "
            "(the default)."
        ),
    )
    p.add_argument(
        "--no-repair-retrieval",
        dest="repair_retrieval",
        action="store_false",
        default=True,
        help=(
            "Disable repair-time Mathlib retrieval. By default, when "
            "`--api-search` is active, failed Lean diagnostics are converted "
            "into a focused Mathlib query and appended to the next repair "
            "prompt."
        ),
    )
    p.add_argument(
        "--repair-retrieval-top-k",
        type=int,
        default=6,
        help=(
            "Number of repair-time Mathlib candidates to append after each "
            "failed Lean check when repair retrieval is enabled."
        ),
    )
    p.add_argument(
        "--no-proof-state-engine",
        dest="proof_state_engine",
        action="store_false",
        default=True,
        help=(
            "Disable the diagnostic-driven proof-state scheduler added after "
            "Lean failures."
        ),
    )
    p.add_argument(
        "--no-proof-state-child-tactics",
        dest="proof_state_child_tactics",
        action="store_false",
        default=True,
        help=(
            "Disable deterministic proof-state child-goal declaration and "
            "tactic probes while keeping proof-state context/retrieval active."
        ),
    )
    p.add_argument(
        "--proof-state-child-tactic-timeout-s",
        type=float,
        default=DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
        help=(
            "Wall-clock seconds for proof-state child-goal tactic/assembly "
            "probes after each failed turn (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--proof-state-child-tactic-max-candidates",
        type=int,
        default=36,
        help=(
            "Maximum deterministic tactic candidates per proof-state child "
            "goal (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--proof-state-child-goal-limit",
        type=int,
        default=3,
        help="Maximum open proof-state child goals to probe after a failed turn.",
    )
    p.add_argument(
        "--proof-state-decl-application-limit",
        type=int,
        default=6,
        help=(
            "Maximum retrieved declarations to apply to each proof-state "
            "child goal (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--proof-state-batch-parallelism",
        type=int,
        default=1,
        help=(
            "Requested proof-state child-node batch parallelism. Multi-node "
            "child closure is currently serialized because probes mutate shared "
            "proof_state/dossier state; values above 1 are preserved for future "
            "isolated batch executors and should not be treated as a speed knob "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--formal-state-search",
        dest="formal_state_search",
        action=_TrackedBooleanOptionalAction,
        default=False,
        help=(
            "Enable bounded, persistent goal-conditioned search over Lean states "
            "after deterministic closers fail (default: disabled; use "
            "--formal-state-search to enable)."
        ),
    )
    p.set_defaults(_formal_state_search_explicit=False)
    p.add_argument(
        "--formal-state-search-timeout-s",
        type=float,
        default=DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
        help=(
            "Bounded wall-clock quantum for one resumable formal-state search "
            "dispatch; this is not an overall run-duration cap."
        ),
    )
    p.add_argument(
        "--formal-state-search-operation-timeout-s",
        type=float,
        default=DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
        help=(
            "Optional per-Lean-operation asyncio bound inside formal-state "
            "search. Zero waits for the in-flight check; the search quantum "
            "still yields between steps (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--formal-state-search-provider-timeout-s",
        type=float,
        default=DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_TIMEOUT_S,
        help=(
            "Hard wall-clock watchdog for one admitted goal-conditioned tactic "
            "generation (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--formal-state-search-provider-max-tokens",
        type=int,
        default=DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_MAX_TOKENS,
        help=(
            "Maximum output tokens reserved and sent for one compact tactic "
            "policy generation (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--formal-state-search-provider-reasoning-effort",
        default=DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
        help=(
            "Reasoning-effort override for compact formal tactic policy "
            "generation (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--formal-state-search-provider-max-attempts",
        type=int,
        default=2,
        help="Maximum paid attempts for one identical formal policy request.",
    )
    p.add_argument(
        "--formal-state-search-provider-retry-backoff-s",
        type=float,
        default=5.0,
        help="Initial durable backoff between identical incomplete policy requests.",
    )
    p.add_argument(
        "--formal-state-search-beam-width",
        type=int,
        default=4,
        help="Number of diverse Lean states retained in the active beam.",
    )
    p.add_argument(
        "--formal-state-search-max-steps",
        type=int,
        default=8,
        help="Maximum tactic-prefix depth for one formal-state search.",
    )
    p.add_argument(
        "--formal-state-search-max-candidates",
        type=int,
        default=6,
        help="Maximum generated tactics checked per expanded Lean state.",
    )
    p.add_argument(
        "--formal-state-search-backtrack-limit",
        type=int,
        default=8,
        help="Maximum checked reserve states restored after a beam dead end.",
    )
    p.add_argument(
        "--formal-state-search-max-no-improvement-quanta",
        type=int,
        default=6,
        help=(
            "Consecutive completed formal-search quanta without kernel-facing "
            "or diagnostic improvement before retiring that unchanged context; "
            "0 disables this progress governor (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-falsification",
        dest="mini_falsification",
        action=argparse.BooleanOptionalAction,
        default=True,
        help=(
            "Run certificate-gated root/helper counterexample search "
            "(default: on)."
        ),
    )
    p.add_argument(
        "--mini-falsification-max-checks",
        type=int,
        default=32,
        help="Per-engine candidate batch; live cursors cover later batches.",
    )
    p.add_argument(
        "--mini-falsification-operation-timeout-s",
        type=float,
        default=DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
        help="Watchdog for one Lean/solver falsification operation.",
    )
    p.add_argument(
        "--mini-falsification-engine-timeout-s",
        type=float,
        default=DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
        help="Watchdog for one falsification engine invocation.",
    )
    p.add_argument(
        "--proof-state-cache",
        dest="proof_state_cache",
        action="store_true",
        default=True,
        help=(
            "Enable the persistent verified helper cache for proof-state nodes. "
            "At run start, same-problem cached helpers are re-kernel-checked "
            "and seeded into the dossier. Enabled by default (default: on)."
        ),
    )
    p.add_argument(
        "--no-proof-state-cache",
        dest="proof_state_cache",
        action="store_false",
        help=(
            "Disable the persistent verified helper cache for proof-state "
            "nodes. The CLI default is --proof-state-cache on."
        ),
    )
    p.add_argument(
        "--proof-state-cache-path",
        type=str,
        default=str(MiniVerifiedLemmaCache.default_path()),
        help="JSONL path for the persistent verified helper cache.",
    )
    p.add_argument(
        "--opaque-mode",
        dest="opaque_mode",
        action="store_true",
        default=True,
        help=(
            "Hide PutnamBench `_solution` values from the LLM-facing prompt "
            "(default). The prover sees opaque axioms and must infer any answer "
            "from the problem statement."
        ),
    )
    p.add_argument(
        "--no-opaque-mode",
        dest="opaque_mode",
        action="store_false",
        help=(
            "Disable opaque prompt mode while keeping official PutnamBench "
            "answers hidden from the LLM unless "
            "--allow-official-answer-visibility is also supplied."
        ),
    )
    p.set_defaults(allow_official_answer_visibility=False)
    p.add_argument(
        "--allow-official-answer-visibility",
        dest="allow_official_answer_visibility",
        action="store_true",
        help=(
            "Permit --no-opaque-mode runs to show filled official PutnamBench "
            "`_solution` definitions to the LLM. Use only for with-answer controls."
        ),
    )
    p.add_argument(
        "--visible-answer-mode",
        nargs=0,
        action=_VisibleAnswerModeAction,
        help=(
            "Alias for --no-opaque-mode plus --allow-official-answer-visibility. "
            "Use only for with-answer controls."
        ),
    )
    p.add_argument(
        "--premise-retrieval",
        dest="premise_retrieval",
        action="store_true",
        default=False,
        help=(
            "Enable eager Mathlib premise retrieval: the top-K lemmas similar "
            "to the goal (and to the model's exploration strategy/observations, "
            "if exploration ran) are retrieved up front and prepended to the "
            "prove conversation. Disabled by default; the model calls "
            "`search_mathlib` reactively instead."
        ),
    )
    p.add_argument(
        "--no-premise-retrieval",
        dest="premise_retrieval",
        action="store_false",
        default=False,
        help=(
            "Explicitly disable eager Mathlib premise retrieval (the default). "
            "The model must call `search_mathlib` reactively."
        ),
    )
    p.add_argument(
        "--no-apply-decl-to-goal-tool",
        dest="apply_decl_to_goal_tool",
        action="store_false",
        default=True,
        help=(
            "Disable the `apply_decl_to_goal` LLM tool. The tool asks Lean "
            "whether a Mathlib declaration actually fits the current goal "
            "before the model commits it to a proof. Disabling it leaves the "
            "model to verify candidates only via `check_lean` (type only) and "
            "`try_lean` (whole-proof attempts)."
        ),
    )
    p.add_argument(
        "--premise-retrieval-top-k",
        dest="premise_retrieval_top_k",
        type=int,
        default=64,
        help=(
            "Number of Mathlib lemmas to pre-retrieve when "
            "`--premise-retrieval` is on (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--premise-zero-hit-policy",
        dest="premise_zero_hit_policy",
        choices=("off", "shadow", "enforce"),
        default="off",
        help=(
            "Policy for clean zero-hit eager premise retrieval. 'shadow' only "
            "records that the run would switch to local micro-theory mode; "
            "'enforce' uses a bounded local-helper construction turn before "
            "broad library-first repair. Default: %(default)s."
        ),
    )
    p.add_argument(
        "--premise-zero-hit-max-local-turns",
        dest="premise_zero_hit_max_local_turns",
        type=int,
        default=1,
        help=(
            "Maximum conversation turns that suppress broad Mathlib search "
            "under --premise-zero-hit-policy=enforce (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--premise-zero-hit-keep-library-first",
        dest="premise_zero_hit_suppress_library_first",
        action="store_false",
        default=True,
        help=(
            "Do not suppress search_mathlib/apply_decl_to_goal when a clean "
            "zero-hit premise signal activates local micro-theory mode."
        ),
    )
    p.add_argument(
        "--premise-zero-hit-no-api-grounding-escape",
        dest="premise_zero_hit_allow_api_grounding_after_lean_failure",
        action="store_false",
        default=True,
        help=(
            "Do not exempt unknown-identifier repair tickets from local "
            "micro-theory library-search suppression."
        ),
    )
    p.add_argument(
        "--parallel-samples",
        dest="parallel_samples",
        type=_parallel_samples_arg,
        default=1,
        help=(
            "Number of parallel proof samples per branch (default: "
            "%(default)s, single-thread). When N>1, N independent "
            "prove+refine sessions run concurrently; the first to produce "
            "a Lean-accepted proof wins, then siblings get "
            "--parallel-late-sample-grace-s to finish before cancellation. "
            "Cost scales linearly with N. Pair with `--parallel-temps` for "
            "diversification across samples. Must be >= 1. CLI runs with N>1 "
            "use cooperative in-process fan-out. Process supervision remains "
            "enabled; overall and startup deadlines default to unlimited, "
            "while post-result shutdown is bounded."
        ),
    )
    p.add_argument(
        "--parallel-late-sample-grace-s",
        dest="parallel_late_sample_grace_s",
        type=_nonnegative_finite_float_arg,
        default=_PARALLEL_SAMPLE_LATE_GRACE_DEFAULT_S,
        help=(
            "Seconds to wait after the first parallel sample proves the root "
            "so near-finished sibling samples can preserve helpers/proof-state "
            "snapshots before cancellation. Set 0 for immediate cancellation "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--parallel-temps",
        dest="parallel_temps",
        type=_parallel_temps_arg,
        default="",
        help=(
            "Comma-separated list of sampling temperatures to stripe "
            "across parallel samples (e.g. '0.3,0.7'). Each value must "
            "be a finite non-negative float in [0.0, 2.0]. Empty string "
            "means use API default for every sample. Only honored by "
            "models that accept a temperature parameter."
        ),
    )
    p.add_argument(
        "--mini-phase-temperatures",
        dest="mini_phase_temperatures",
        action="store_true",
        default=True,
        help=(
            "Enable mini-prover phase-specific temperatures: hot planning, "
            "diverse initial proof, and cool formalization/repair "
            "(default: on)."
        ),
    )
    p.add_argument(
        "--no-mini-phase-temperatures",
        dest="mini_phase_temperatures",
        action="store_false",
        help=(
            "Disable phase-specific temperatures and use only "
            "--parallel-temps/API defaults. The CLI default is "
            "--mini-phase-temperatures on."
        ),
    )
    p.add_argument("--mini-temperature-planner", type=_mini_temperature_arg, default=0.10)
    p.add_argument("--mini-temperature-initial-proof", type=_mini_temperature_arg, default=0.45)
    p.add_argument(
        "--mini-temperature-formalization-helper",
        type=_mini_temperature_arg,
        default=0.10,
    )
    p.add_argument("--mini-temperature-lean-repair", type=_mini_temperature_arg, default=0.05)
    p.add_argument("--mini-temperature-refine", type=_mini_temperature_arg, default=0.25)
    p.add_argument("--mini-temperature-route-assembly", type=_mini_temperature_arg, default=0.25)
    p.add_argument("--mini-temperature-stagnation-escape", type=_mini_temperature_arg, default=0.85)
    p.add_argument(
        "--mini-temperature-initial-use-sample",
        dest="mini_temperature_initial_use_sample",
        action="store_true",
        default=True,
        help=(
            "When phase temperatures are enabled, preserve --parallel-temps "
            "for plain initial proof exploration."
        ),
    )
    p.add_argument(
        "--mini-temperature-initial-no-sample",
        dest="mini_temperature_initial_use_sample",
        action="store_false",
        help=(
            "When phase temperatures are enabled, use the initial-proof phase "
            "temperature even for plain proof turns."
        ),
    )
    p.add_argument(
        "--root-tactic-prepass",
        dest="root_tactic_prepass",
        action="store_true",
        default=False,
        help=(
            "Enable the operational deterministic root-close portfolio before "
            "the first LLM proof attempt. Disabled by default; helper-backed "
            "root tactic assembly remains available through recursive/graph "
            "assembly paths."
        ),
    )
    p.add_argument(
        "--no-root-tactic-prepass",
        dest="root_tactic_prepass",
        action="store_false",
        help=(
            "Explicitly disable the cold deterministic root-close prepass "
            "(the default)."
        ),
    )
    p.add_argument(
        "--root-tactic-timeout-s",
        type=float,
        default=40.0,
        help=(
            "Wall-clock seconds for the deterministic root-close prepass "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--root-tactic-max-candidates",
        type=int,
        default=64,
        help=(
            "Maximum deterministic root-close candidates for the prepass "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--startup-root-fast-lane",
        dest="startup_root_fast_lane",
        action="store_true",
        default=False,
        help=(
            "Run one tightly bounded deterministic root close before "
            "decomposition (explicit opt-in; default: off)."
        ),
    )
    p.add_argument(
        "--no-startup-root-fast-lane",
        dest="startup_root_fast_lane",
        action="store_false",
        help="Disable the bounded startup root fast lane.",
    )
    p.add_argument(
        "--startup-root-fast-lane-tactic-timeout-s",
        type=float,
        default=300.0,
    )
    p.add_argument(
        "--startup-root-fast-lane-tactic-max-candidates",
        type=int,
        default=12,
    )
    p.add_argument(
        "--mini-recursive",
        dest="mini_recursive",
        action="store_true",
        default=True,
        help=(
            "Enable the focused recursive helper controller: plan subgoals, "
            "prove helpers as first-class Lean goals, and try an answer-safe "
            "root tactic close after each accepted helper (default: on)."
        ),
    )
    p.add_argument(
        "--no-mini-recursive",
        dest="mini_recursive",
        action="store_false",
        help=(
            "Disable the focused recursive helper controller. The CLI default "
            "is --mini-recursive on."
        ),
    )
    p.add_argument(
        "--no-adaptive-recursive-on-stall",
        dest="adaptive_recursive_on_stall",
        action="store_false",
        default=True,
        help=(
            "Disable the operational fallback that escalates to the recursive "
            "helper controller once direct prove/refine sampling stalls."
        ),
    )
    p.add_argument(
        "--mini-recursive-passes",
        type=int,
        default=6,
        help=(
            "Number of recursive plan/prove/integrate passes when "
            "--mini-recursive is enabled (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-recursive-claims",
        type=int,
        default=PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
        help=(
            "Maximum helper-plus-root claims across planner tranches "
            "(default: %(default)s). One tranche is 6 claims; this leaves "
            "room for a later root_assembly instead of filling the cap "
            "with helpers and proving a route-less ladder."
        ),
    )
    p.add_argument(
        "--mini-recursive-turns-per-claim",
        type=int,
        default=6,
        help=(
            "Prover/refiner turns allocated to each recursive helper goal "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-recursive-tactic-timeout-s",
        type=float,
        default=60.0,
        help=(
            "Wall-clock seconds for each deterministic helper/root tactic "
            "closer call (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-recursive-tactic-max-candidates",
        type=int,
        default=48,
        help=(
            "Maximum deterministic tactic candidates per mini recursive closer "
            "call (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-worker-timeout-s",
        type=_nonnegative_finite_float_arg,
        default=0.0,
        help=(
            "Hard parent-supervisor wall cap for the isolated Mini CLI worker. "
            "This is independent of dollar cost and also bounds an in-flight "
            "operation. Zero permits an intentionally unbounded run "
            "(default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-run-wall-clock-budget-s",
        type=_nonnegative_finite_float_arg,
        default=0.0,
        help=(
            "Cumulative MiniSession wall-clock budget for the current run. "
            "Zero explicitly disables it (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-no-strong-progress-budget-s",
        type=_nonnegative_finite_float_arg,
        default=0.0,
        help=(
            "Active seconds allowed without authoritative "
            "strong/root progress. Soft helpers and graph churn do not reset "
            "the window; zero disables it (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-worker-startup-timeout-s",
        type=_nonnegative_finite_float_arg,
        default=0.0,
        help=(
            "Optional parent-supervisor deadline for reaching the proof-search "
            "ready handshake. Disabled by default because slow initialization "
            "is not evidence that the worker is hung (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-worker-shutdown-timeout-s",
        type=_nonnegative_finite_float_arg,
        default=120.0,
        help=(
            "Optional parent-supervisor deadline for asyncio/resource shutdown "
            "after the run has returned. Zero disables it (default: %(default)s)."
        ),
    )
    p.add_argument(
        "--mini-hard-operation-watchdog",
        action="store_true",
        default=False,
        help=(
            "Opt in to escalating any expired local Lean/provider/tool lease "
            "into termination of the entire Mini worker. Disabled by default; "
            "local operation timeouts remain active and recoverable, while "
            "critical transactional liveness leases remain supervisor-enforced."
        ),
    )
    # ----- Phase 2: recursive helper prover ---------------------------
    # Spawns a child MiniSession to prove ONE open child_goal helper
    # via a bounded LLM sub-conversation, after the deterministic
    # actions (tactic swarm, retrieval) have already attacked it.
    p.add_argument(
        "--recursive-helper-prover",
        dest="recursive_helper_prover",
        action="store_true",
        default=True,
        help=(
            "Enable Phase 2 RecursiveHelperProverAction — spawn a child "
            "MiniSession to prove ONE open child_goal helper after "
            "deterministic actions have failed on it (default: on)."
        ),
    )
    p.add_argument(
        "--no-recursive-helper-prover",
        dest="recursive_helper_prover",
        action="store_false",
        help=(
            "Disable Phase 2 RecursiveHelperProverAction. The CLI default is "
            "--recursive-helper-prover on."
        ),
    )
    p.add_argument(
        "--recursive-helper-budget",
        dest="recursive_helper_budget",
        type=int,
        default=0,
        help=(
            "Maximum invocations of RecursiveHelperProverAction per "
            "session. 0 (default) auto-derives from max_prove_turns × 2."
        ),
    )
    p.add_argument(
        "--recursive-helper-max-depth",
        dest="recursive_helper_max_depth",
        type=int,
        default=3,
        help=(
            "Maximum recursion depth for child sub-sessions. At the cap, "
            "the give-up gate's nudge stops asking for further "
            "decomposition and instructs the LLM to make a direct "
            "attempt. Default 3 — beyond that, sub-sessions chain into "
            "diminishing returns."
        ),
    )
    p.add_argument(
        "--recursive-helper-max-attempts-per-node",
        dest="recursive_helper_max_attempts_per_node",
        type=int,
        default=2,
        help=(
            "Maximum recursive-helper-prover attempts on a single open "
            "child_goal node. Once exceeded, the node sits open until "
            "deterministic actions close it or budget exhausts."
        ),
    )
    p.add_argument(
        "--recursive-helper-turns",
        dest="recursive_helper_turns",
        type=int,
        default=5,
        help=(
            "Maximum LLM turns the child sub-session can spend on each "
            "helper goal. Default 5."
        ),
    )
    p.add_argument(
        "--recursive-helper-refine",
        dest="recursive_helper_refine",
        action="store_true",
        default=True,
        help=(
            "Also run a refine-role pass in the child sub-session if the "
            "prove pass didn't solve (default: on)."
        ),
    )
    p.add_argument(
        "--no-recursive-helper-refine",
        dest="recursive_helper_refine",
        action="store_false",
        help=(
            "Disable recursive-helper refine child passes. The CLI default is "
            "--recursive-helper-refine on."
        ),
    )
    p.add_argument(
        "--mini-theory-mode",
        choices=("off", "read", "build"),
        default=None,
        help=(
            "Persistent Mini-owned domain theory: off, retrieve verified bundles "
            "only, or autonomously build/verify/publish missing theory "
            "(default: build)."
        ),
    )
    p.add_argument(
        "--mini-theory-root",
        default=str(Path.home() / ".cache" / "mini_prover" / "theory"),
        help="Persistent content-addressed Mini theory store.",
    )
    p.add_argument(
        "--mini-theory-domain",
        default="general mathematics",
        help="Domain label used for this conjecture's theory needs and retrieval.",
    )
    p.add_argument(
        "--mini-theory-bundle",
        dest="mini_theory_bundles",
        action="append",
        default=[],
        help="Exact verified bundle id to import at session start; repeatable.",
    )
    p.add_argument(
        "--mini-theory-verifier-timeout-s",
        type=float,
        default=180.0,
        help="Per independent theory compilation/audit timeout.",
    )
    p.add_argument(
        "--mini-theory-operation-timeout-s",
        type=_positive_finite_float_arg,
        default=None,
        help=(
            "Optional opt-in watchdog for one logical domain-theory model "
            "build. By default the reasoning call has no local timeout."
        ),
    )
    p.add_argument(
        "--mini-theory-promote-verified-helpers",
        action="store_true",
        default=False,
        help=(
            "Durably stage generic verified helpers during a MiniSession; after "
            "the supervised proof worker exits, independently recompile and "
            "publish only helpers that do not depend on problem-local context."
        ),
    )
    p.add_argument(
        "--mini-theory-startup-overlay-nonce",
        default="",
        help=argparse.SUPPRESS,
    )
    return p


def _mini_prover_external_stop_reason(exc: BaseException) -> Tuple[str, str]:
    """Return a canonical summary reason plus diagnostic detail for external stops."""

    detail = format_exception(exc)[:1000]
    if isinstance(exc, asyncio.CancelledError):
        return "run_cancelled", detail
    if isinstance(exc, KeyboardInterrupt):
        return "user_interrupted", detail
    return f"{type(exc).__name__}: {exc}", detail



def _install_cooperative_stop_signal_handlers(
    stop_signals: List[int],
    *,
    cancel_all_tasks: bool = False,
    hard_stop_timeout_s: float = 0.0,
) -> Callable[[], None]:
    """MP-FU-009: convert a delivered stop signal into cooperative shutdown.

    The first signal routes the run through ordinary CancelledError teardown:
    cancellation barrier, terminal summary, session-cancelled cutpoint, and
    recorder close. Supervised workers leave escalation to their parent. The
    cooperative parallel CLI has no parent supervisor, so it may request
    direct child-task cancellation and a bounded hard-stop timer; a repeated
    signal then escalates immediately. Returns an uninstall callable; both
    directions are best-effort because non-main-thread loops cannot install
    handlers.
    """

    import signal

    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        return lambda: None
    main_task = asyncio.current_task()
    if main_task is None:
        return lambda: None
    installed: List[int] = []
    hard_stop_timer: Optional[threading.Timer] = None

    def _hard_stop(signum: int) -> None:
        # This path is enabled only by the top-level cooperative parallel CLI.
        # os._exit is intentional: a task that suppresses CancelledError can
        # hold asyncio.run() shutdown forever, so no coroutine-level mechanism
        # can provide the required bound once the grace interval expires.
        os._exit(128 + int(signum))

    def _request_stop(signum: int) -> None:
        nonlocal hard_stop_timer
        if stop_signals:
            if hard_stop_timeout_s > 0.0:
                _hard_stop(signum)
            return
        stop_signals.append(int(signum))
        if cancel_all_tasks:
            for task in asyncio.all_tasks(loop):
                if task is not main_task and not task.done():
                    task.cancel()
        main_task.cancel()
        if hard_stop_timeout_s > 0.0:
            hard_stop_timer = threading.Timer(
                max(0.01, float(hard_stop_timeout_s)),
                _hard_stop,
                args=(int(signum),),
            )
            hard_stop_timer.daemon = True
            hard_stop_timer.start()

    for handled in (signal.SIGTERM, signal.SIGINT):
        try:
            loop.add_signal_handler(handled, _request_stop, int(handled))
        except (NotImplementedError, RuntimeError, ValueError, OSError):
            continue
        installed.append(int(handled))

    def _uninstall() -> None:
        # Once a cooperative stop was delivered, keep the hard-stop lease
        # alive through ``asyncio.run``'s own final task-cancellation sweep.
        # A sample that suppresses CancelledError may outlive ``_main_async``;
        # cancelling the timer here would make that final sweep unbounded,
        # precisely the case the timer exists to cover. Normal, unsignalled
        # teardown still cancels the dormant lease.
        if hard_stop_timer is not None and not stop_signals:
            hard_stop_timer.cancel()
        for handled in installed:
            try:
                loop.remove_signal_handler(handled)
            except (NotImplementedError, RuntimeError, ValueError, OSError):
                pass

    return _uninstall

def _mini_prover_unsolved_failure_reason(
    *,
    ok: bool,
    failure_reason: Optional[str],
    controller_failure_reason: Optional[str],
    usage_summary: Dict[str, Any],
    recorder_metrics: Dict[str, Any],
) -> Optional[str]:
    """Derive a non-null reason for every unsolved mini-prover summary."""

    if ok:
        return None
    explicit = str(failure_reason or "").strip()
    if explicit:
        return explicit
    controller = str(controller_failure_reason or "").strip()
    # Close-time HTTP tails are accounting diagnostics, not a search outcome.
    if (
        controller
        and controller != "llm_transport_not_quiescent_before_summary"
    ):
        return controller

    cost_reason = str(
        usage_summary.get("llm_cost_budget_terminal_reason") or ""
    ).strip()
    if cost_reason:
        return cost_reason
    if bool(usage_summary.get("llm_cost_budget_exhausted")):
        return "llm_cost_budget_exhausted"

    last_status = str(recorder_metrics.get("llm_usage_last_status") or "").strip()
    last_verdict = str(recorder_metrics.get("llm_usage_last_verdict") or "").strip()
    if last_status == "cancelled":
        return "run_cancelled"
    terminal_proof_search_reason = str(
        recorder_metrics.get("terminal_proof_search_reason") or ""
    ).strip()
    if terminal_proof_search_reason:
        return terminal_proof_search_reason
    llm_last_failure_reason = str(
        recorder_metrics.get("mini_session_llm_last_failure_reason") or ""
    ).strip()
    if last_status == "exception":
        if llm_last_failure_reason:
            return llm_last_failure_reason
        return "llm_call_exception"
    mini_recursive_last_failure_reason = str(
        recorder_metrics.get("mini_recursive_last_failure_reason") or ""
    ).strip()
    if (
        mini_recursive_last_failure_reason
        and not is_resumable_mini_recursive_yield(
            mini_recursive_last_failure_reason
        )
        and llm_failure_scope(mini_recursive_last_failure_reason) != "scoped"
    ):
        return mini_recursive_last_failure_reason
    if last_verdict == "llm_usage_missing":
        return "llm_usage_missing"
    return "proof_search_exhausted"


def _mini_prover_unsolved_failure_detail(
    *,
    ok: bool,
    effective_failure_reason: Optional[str],
    existing_detail: Optional[str],
    recorder_metrics: Dict[str, Any],
) -> Optional[str]:
    """Preserve the causal scoped LLM blocker behind a generic governor exit."""

    detail = str(existing_detail or "").strip()
    if ok or detail:
        return detail or None
    terminal_reason = str(effective_failure_reason or "").strip()
    if terminal_reason not in {
        "mini_no_strong_progress_budget_exhausted",
        "mini_run_wall_clock_budget_exhausted",
        "proof_search_exhausted",
        "no_serviceable_frontier_work",
        "no_recovery_budget_granted",
    }:
        return None

    last_scope = str(
        recorder_metrics.get("mini_session_llm_last_failure_scope") or ""
    ).strip()
    last_reason = str(
        recorder_metrics.get("mini_session_llm_last_failure_reason") or ""
    ).strip()
    deadline_failures = int(
        recorder_metrics.get("mini_session_llm_retry_deadline_scoped_failures", 0)
        or 0
    )
    scoped_failures = int(
        recorder_metrics.get("mini_session_llm_scoped_failures", 0) or 0
    )
    if deadline_failures > 0 and (not last_reason or last_scope != "scoped"):
        last_reason = "llm_retry_deadline_exhausted"
        last_scope = "scoped"
    if not last_reason or last_scope != "scoped":
        return None
    recorded_failures = max(deadline_failures, scoped_failures, 1)
    return (
        f"prior_scoped_llm_failure={last_reason}; "
        f"recorded_failure_events={recorded_failures}"
    )


async def _validate_cost_budget_pricing(
    *,
    max_cost_usd: float,
    role_clients: Sequence[tuple[str, Any]],
) -> tuple[Dict[str, Any], ...]:
    """Fail before proof work if an enabled dollar budget cannot be priced."""
    if max(0.0, float(max_cost_usd or 0.0)) <= 0.0:
        return ()
    checked: List[Dict[str, Any]] = []
    unknown: List[Dict[str, Any]] = []
    seen: set[tuple[str, str, str]] = set()
    for role, client in role_clients:
        if client is None:
            continue
        for model, base_url in reservation_pricing_targets(client):
            identity = (str(role or "llm"), str(model or ""), str(base_url or ""))
            if identity in seen:
                continue
            seen.add(identity)
            pricing = await lookup_known_token_pricing_async(base_url, model)
            record = {
                "role": identity[0],
                "model": identity[1],
                "base_url": identity[2],
                "pricing_known": pricing is not None,
                "pricing_per_million": list(pricing) if pricing is not None else None,
            }
            checked.append(record)
            if pricing is None:
                unknown.append(record)
    if unknown:
        detail = ", ".join(
            f"{item['role']}={item['model']}@{item['base_url']}"
            for item in unknown
        )
        raise ValueError(
            "--cost-budget-usd requires known token pricing for every active "
            f"model; missing: {detail}. Update ensemble_prover/pricing.py with "
            "verified provider pricing, or explicitly disable dollar-budget "
            "stops with --cost-budget-usd 0."
        )
    return tuple(checked)


def _resolve_cli_theorem_problem(args: argparse.Namespace) -> TheoremProblem:
    """Resolve the CLI's one canonical theorem-project input boundary."""

    cached = getattr(args, "_resolved_theorem_problem", None)
    if isinstance(cached, TheoremProblem):
        return cached

    description = getattr(args, "theorem_project_description", None)
    description_file = str(
        getattr(args, "theorem_project_description_file", "") or ""
    ).strip()
    if description_file:
        description_path = Path(description_file).expanduser().resolve(strict=True)
        if not description_path.is_file():
            raise ValueError(f"description file is not a file: {description_path}")
        description = description_path.read_text(encoding="utf-8").strip()

    imports = tuple(getattr(args, "theorem_project_imports", ()) or ())
    source_dirs = tuple(
        Path(item)
        for item in (getattr(args, "theorem_project_source_dirs", ()) or ())
    )
    generic_file = str(getattr(args, "lean_file", "") or "").strip()
    putnam_file = str(getattr(args, "putnam_file", "") or "").strip()
    project_path = str(getattr(args, "lean_project_dir", "") or "").strip()
    theorem_name = str(getattr(args, "theorem_name", "") or "").strip()
    if generic_file:
        if not theorem_name:
            raise ValueError("--lean-file requires --theorem-name")
        if not project_path:
            raise ValueError("--lean-file requires --project-path")
        if bool(getattr(args, "allow_official_answer_visibility", False)):
            raise ValueError(
                "official-answer visibility controls require --putnam-file; "
                "generic theorem projects preserve their ordinary source semantics"
            )
        problem = resolve_theorem_project(
            TheoremProjectRequest(
                lean_file=Path(generic_file),
                theorem_name=theorem_name,
                project_path=Path(project_path),
                imports=imports,
                source_dirs=source_dirs,
                description=description,
            )
        )
    elif putnam_file:
        if project_path or imports or source_dirs or description is not None:
            problem = load_putnam_problem(
                putnam_file,
                theorem_name=theorem_name or None,
                project_path=Path(project_path) if project_path else None,
                imports=imports,
                source_dirs=source_dirs,
                description=description,
            )
        else:
            # Keep the historic two-argument loader seam for programmatic
            # embedders while routing the real implementation to the adapter.
            problem = load_putnam_problem(putnam_file, theorem_name or None)
        if not isinstance(problem, TheoremProblem):
            # Compatibility for embedders that replace the historical loader
            # with a light-weight problem object. Normal CLI execution always
            # receives the strongly typed result from ``load_putnam_project``.
            fallback_path = Path(putnam_file).expanduser().resolve()
            fallback_project = (
                Path(project_path).expanduser().resolve()
                if project_path
                else (_PROJECT_ROOT / "external" / "PutnamBench" / "lean4")
            )
            problem = TheoremProblem(
                path=Path(getattr(problem, "path", fallback_path)),
                theorem_name=str(getattr(problem, "theorem_name")),
                declaration_name=str(
                    getattr(problem, "declaration_name", "")
                    or getattr(problem, "theorem_name")
                ),
                preamble=str(getattr(problem, "preamble", "") or ""),
                lean_preamble=str(
                    getattr(problem, "lean_preamble", "")
                    or getattr(problem, "preamble", "")
                    or ""
                ),
                statement_type=str(getattr(problem, "statement_type")),
                docstring=str(getattr(problem, "docstring", "") or ""),
                solution_comment=str(
                    getattr(problem, "solution_comment", "") or ""
                ),
                project_path=fallback_project,
                adapter_id=PUTNAMBENCH_ADAPTER_ID,
                adapter_metadata={"exclude_entire_source_from_retrieval": True},
            )
    else:  # argparse enforces this; programmatic Namespace callers may not.
        raise ValueError("provide exactly one of --lean-file or --putnam-file")

    setattr(args, "lean_file", str(problem.path))
    setattr(args, "lean_project_dir", str(problem.project_path or project_path))
    configured_roots = list(
        getattr(args, "mini_retrieval_project_roots", ()) or ()
    )
    for root in _external_theorem_support_roots(problem):
        value = str(root)
        if value not in configured_roots:
            configured_roots.append(value)
    setattr(args, "mini_retrieval_project_roots", configured_roots)
    setattr(args, "_resolved_theorem_problem", problem)
    return problem


async def _supervised_resource_close(
    awaitable: Any,
    *,
    label: str,
    timeout_s: float = 10.0,
    cancel_grace_s: float = 0.25,
) -> None:
    """Bound teardown so final accounting cannot hang behind a stuck close."""

    task = asyncio.ensure_future(awaitable)
    done, _pending = await asyncio.wait(
        {task},
        timeout=max(0.0, float(timeout_s or 0.0)),
    )
    if task in done:
        await task
        return
    task.cancel()
    done, _pending = await asyncio.wait(
        {task},
        timeout=max(0.0, float(cancel_grace_s or 0.0)),
    )
    if task in done:
        try:
            await task
        except asyncio.CancelledError as exc:
            raise TimeoutError(f"{label} timed out") from exc
        return

    from .mini_session.process_watchdog import is_watchdog_worker

    if is_watchdog_worker():
        # The active shutdown lease is the only mechanism that can both bound
        # an arbitrary cancellation-resistant coroutine and guarantee it never
        # mutates accounting after this wrapper returns. Keep the worker alive
        # until the supervisor performs the process-tree sweep.
        while True:
            try:
                await asyncio.Future()
            except asyncio.CancelledError:
                continue
    while not task.done():
        try:
            await asyncio.shield(task)
        except asyncio.CancelledError:
            continue
    if not task.cancelled():
        try:
            task.result()
        except BaseException:
            pass
    raise TimeoutError(f"{label} timed out and resisted cancellation")


_SYNC_CLOSE_LOCK = threading.Lock()
_SYNC_CLOSE_IN_FLIGHT: Dict[int, Dict[str, Any]] = {}


async def _supervised_sync_resource_close(
    close: Any,
    *,
    label: str,
    timeout_s: float = 10.0,
) -> None:
    """Bound synchronous closes without occupying asyncio's default executor."""

    loop = asyncio.get_running_loop()
    future = loop.create_future()
    owner = getattr(close, "__self__", close)
    close_key = id(owner)

    def publish(outcome: tuple[bool, Any]) -> None:
        if future.done():
            return
        ok, value = outcome
        if ok:
            future.set_result(None)
        else:
            future.set_exception(value)

    def publish_to_subscriber(
        subscriber_loop: Any,
        subscriber_future: Any,
        outcome: tuple[bool, Any],
    ) -> None:
        if subscriber_loop.is_closed():
            return
        try:
            subscriber_loop.call_soon_threadsafe(
                lambda: (
                    None
                    if subscriber_future.done()
                    else subscriber_future.set_result(None)
                    if outcome[0]
                    else subscriber_future.set_exception(outcome[1])
                )
            )
        except RuntimeError:
            pass

    def worker(entry: Dict[str, Any]) -> None:
        try:
            outcome = (True, close())
        except BaseException as exc:
            outcome = (False, exc)
        entry["outcome"] = outcome
        entry["settled"].set()
        with _SYNC_CLOSE_LOCK:
            subscribers = list(entry.get("subscribers") or ())
            if _SYNC_CLOSE_IN_FLIGHT.get(close_key) is entry:
                _SYNC_CLOSE_IN_FLIGHT.pop(close_key, None)
        for subscriber_loop, subscriber_future in subscribers:
            publish_to_subscriber(subscriber_loop, subscriber_future, outcome)

    with _SYNC_CLOSE_LOCK:
        entry = _SYNC_CLOSE_IN_FLIGHT.get(close_key)
        if entry is not None and entry.get("owner") is not owner:
            entry = None
        if entry is None:
            entry = {
                "owner": owner,
                "subscribers": [],
                "settled": threading.Event(),
                "outcome": None,
            }
            _SYNC_CLOSE_IN_FLIGHT[close_key] = entry
            thread = threading.Thread(
                target=worker,
                args=(entry,),
                name=f"{label}-close",
                daemon=True,
            )
            entry["thread"] = thread
            thread.start()
        entry["subscribers"].append((loop, future))
    try:
        await asyncio.wait_for(
            asyncio.shield(future),
            timeout=max(0.001, float(timeout_s or 0.001)),
        )
    except asyncio.TimeoutError as exc:
        # A daemon thread cannot be cancelled safely. Do not let it mutate a
        # recorder/library after this wrapper has returned. In a supervised
        # CLI worker the active shutdown lease bounds this wait by killing the
        # process tree; programmatic callers instead wait for settlement.
        while not entry["settled"].is_set():
            try:
                await asyncio.sleep(0.01)
            except asyncio.CancelledError:
                continue
        if future.done() and not future.cancelled():
            try:
                future.result()
            except BaseException:
                pass
        raise TimeoutError(f"{label} timed out after close settled") from exc
    except asyncio.CancelledError:
        while not entry["settled"].is_set():
            try:
                await asyncio.sleep(0.01)
            except asyncio.CancelledError:
                continue
        if future.done() and not future.cancelled():
            try:
                future.result()
            except BaseException:
                pass
        raise


async def _run_cancellation_barrier(
    *,
    lean: Any,
    theory_library: Any = None,
    drain_timeout_s: float = 5.0,
    close_timeout_s: float = 10.0,
) -> Dict[str, Any]:
    """MP-FU-009: stop child work BEFORE the event stream closes.

    Order matters: (1) refuse new Lean admissions so no fresh scratch file or
    subprocess can start, (2) join detached deadline tasks so cancellation-
    suppressing adapters finish mutating state, (3) close the Lean runner
    (kills in-flight subprocess trees), (4) close the theory library. Every
    step is bounded and failure-isolated; the report travels in the terminal
    summary so the run record shows what the barrier actually joined.
    """

    from .deadline_guard import drain_abandoned_deadline_tasks

    report: Dict[str, Any] = {
        "barrier_ran": True,
        "lean_closed": False,
        "theory_closed": False,
        "abandoned_tasks": {"drained": 0, "still_pending": 0},
    }
    quiesce = getattr(lean, "quiesce", None) if lean is not None else None
    if callable(quiesce):
        try:
            quiesce()
            report["lean_quiesced"] = True
        except Exception as exc:
            report["lean_quiesce_error"] = f"{type(exc).__name__}: {exc}"
    try:
        report["abandoned_tasks"] = await drain_abandoned_deadline_tasks(
            timeout_s=max(0.0, float(drain_timeout_s)),
        )
    except Exception as exc:
        report["abandoned_tasks_error"] = f"{type(exc).__name__}: {exc}"
    if lean is not None:
        try:
            await _supervised_resource_close(
                lean.aclose(),
                label="mini_cancellation_barrier_lean_close",
                timeout_s=max(0.0, float(close_timeout_s)),
            )
            report["lean_closed"] = True
        except Exception as exc:
            report["lean_close_error"] = f"{type(exc).__name__}: {exc}"
    if theory_library is not None:
        try:
            await _supervised_sync_resource_close(
                theory_library.close,
                label="mini_cancellation_barrier_theory_close",
                timeout_s=max(0.0, float(close_timeout_s)),
            )
            report["theory_closed"] = True
        except Exception as exc:
            report["theory_close_error"] = f"{type(exc).__name__}: {exc}"
    return report


def _falsification_deadlines_from_args(
    args: argparse.Namespace,
) -> tuple[float, float]:
    """Validate CLI and partial programmatic namespaces identically."""

    return (
        require_falsification_watchdog(
            getattr(
                args,
                "mini_falsification_operation_timeout_s",
                DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
            ),
            field="mini_falsification_operation_timeout_s",
        ),
        require_falsification_watchdog(
            getattr(
                args,
                "mini_falsification_engine_timeout_s",
                DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
            ),
            field="mini_falsification_engine_timeout_s",
        ),
    )


def _allocate_default_mini_run_dir(artifact_slug: str) -> Path:
    """Atomically reserve a unique default artifact directory.

    The readable timestamp remains the primary name. A same-second contender
    receives a process/nonce suffix, with ``mkdir(exist_ok=False)`` providing
    the cross-process ownership boundary for logs, summaries, and accounting.
    """

    parent = _PROJECT_ROOT / "runs" / "mini_prover"
    parent.mkdir(parents=True, exist_ok=True)
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    stem = f"{str(artifact_slug or 'run').strip() or 'run'}_{timestamp}"
    primary = parent / stem
    try:
        primary.mkdir(exist_ok=False)
        return primary.resolve()
    except FileExistsError:
        pass
    while True:
        candidate = parent / f"{stem}_{os.getpid()}_{uuid.uuid4().hex[:12]}"
        try:
            candidate.mkdir(exist_ok=False)
            return candidate.resolve()
        except FileExistsError:
            continue


async def _main_async(args: argparse.Namespace) -> int:
    # CLI namespaces can also be supplied programmatically.  Validate the
    # complete falsification numeric surface before installing handlers,
    # resolving theorem inputs, or initializing any runtime service.
    falsification_max_checks = require_falsification_search_bound(
        getattr(args, "mini_falsification_max_checks", 32),
        field="mini_falsification_max_checks",
    )
    (
        falsification_operation_timeout_s,
        falsification_engine_timeout_s,
    ) = _falsification_deadlines_from_args(args)
    cooperative_stop_signals: List[int] = []
    cooperative_parallel_cli = bool(
        getattr(args, "_cooperative_parallel_cli", False)
    )
    _uninstall_cooperative_stop = _install_cooperative_stop_signal_handlers(
        cooperative_stop_signals,
        cancel_all_tasks=cooperative_parallel_cli,
        hard_stop_timeout_s=(5.0 if cooperative_parallel_cli else 0.0),
    )
    problem = _resolve_cli_theorem_problem(args)
    run_source_provenance = capture_repository_provenance(Path(__file__))
    if args.output_dir:
        output_dir = Path(args.output_dir).resolve()
    else:
        output_dir = _allocate_default_mini_run_dir(problem.artifact_slug)
    recorder = RunRecorder(output_dir)
    configure_live_trace = getattr(recorder, "configure_live_trace", None)
    if callable(configure_live_trace):
        configure_live_trace(str(getattr(args, "terminal_trace", "compact") or "compact"))

    # Pre-declare so the finally branch always has access — even when setup
    # fails before the prover/refiner clients are constructed. Without this,
    # an early SystemExit (e.g. missing API key from ``_make_role_cfg``)
    # would bypass recorder finalization, leak ``sys.stdout``/``sys.stderr``,
    # and leave a half-finished run dir with no summary on disk (the
    # "ghost run" pattern that breaks downstream sweep aggregation).
    ok = False
    proof: Optional[str] = None
    failure_reason: Optional[str] = None
    prover_cfg: Optional[RoleConfig] = None
    refiner_cfg: Optional[RoleConfig] = None
    prover_client: Optional[OpenAICompatClient] = None
    refiner_client: Optional[OpenAICompatClient] = None
    # Pre-try init: the finally-block transport cleanup references this even
    # when setup fails before the escalation client is (conditionally) built.
    planner_escalation_client: Optional[OpenAICompatClient] = None
    lean: Optional[LeanRunner] = None
    searcher: Optional[Any] = None
    proof_dossier: Optional[ProofDossier] = None
    cost_controller: Optional[CostBudgetController] = None
    mini_phase_temperature_policy: Optional[MiniPhaseTemperatures] = None
    theory_library: Optional[Any] = None
    theory_candidate_builder: Optional[Any] = None
    pending_reraise: Optional[BaseException] = None
    failure_reason_detail: Optional[str] = None
    infrastructure_aborted = False
    prover_reasoning_mode = _REASONING_PROVIDER_DEFAULT
    prover_reasoning_effort: Optional[str] = None
    refiner_reasoning_mode = _REASONING_PROVIDER_DEFAULT
    refiner_reasoning_effort: Optional[str] = None
    cost_budget_pricing_preflight: tuple[Dict[str, Any], ...] = ()
    llm_client_close_attempted_ids: set[int] = set()
    lean_close_completed = False
    theory_library_close_completed = False
    early_staged_solution_written = False
    # Programmatic callers may invoke Mini repeatedly in one task/context.
    # Give every concrete role client in this theorem one shared, fresh
    # registry without moving the run lifecycle out of ``_main_async`` (whose
    # cancellation-barrier/summary ordering is a public operational contract).
    provider_lane_health_registry = ProviderLaneHealthRegistry()

    try:
        print("=== mini_prover run ===")
        print(f"Output dir: {output_dir}")
        print(
            "Terminal trace: "
            f"{str(getattr(args, 'terminal_trace', 'compact') or 'compact')}"
        )
        print(
            f"Loaded {problem.theorem_name} from {problem.path} "
            f"(adapter={getattr(problem, 'adapter_id', 'generic')})"
        )
        print(f"Docstring:\n  {problem.docstring or '(none)'}")
        print(f"Statement type:\n  {problem.statement_type}")
        print()
        cost_controller = CostBudgetController(
            max_cost_usd=max(0.0, float(getattr(args, "cost_budget_usd", 0.0) or 0.0)),
            reserve_output_tokens=max(
                0,
                int(
                    getattr(args, "cost_budget_reserve_output_tokens", 1024)
                    or 0
                ),
            ),
            event_sink=recorder.record_turn,
        )
        mini_phase_temperature_policy = _mini_phase_temperature_policy_from_args(args)

        prover_timeout_s = (
            getattr(args, "prover_timeout_s", None)
            if getattr(args, "prover_timeout_s", None) is not None
            else getattr(args, "llm_timeout_s", None)
        )
        refiner_timeout_s = (
            getattr(args, "refiner_timeout_s", None)
            if getattr(args, "refiner_timeout_s", None) is not None
            else getattr(args, "llm_timeout_s", None)
        )
        prover_request_timeout_raw = (
            getattr(args, "prover_request_timeout_s", None)
            if getattr(args, "prover_request_timeout_s", None) is not None
            else getattr(args, "llm_request_timeout_s", None)
        )
        refiner_request_timeout_raw = (
            getattr(args, "refiner_request_timeout_s", None)
            if getattr(args, "refiner_request_timeout_s", None) is not None
            else getattr(args, "llm_request_timeout_s", None)
        )
        (
            prover_request_timeout_s,
            prover_request_timeout_disabled,
        ) = _resolve_llm_request_timeout_setting(
            prover_request_timeout_raw,
            role_name="prover",
        )
        (
            refiner_request_timeout_s,
            refiner_request_timeout_disabled,
        ) = _resolve_llm_request_timeout_setting(
            refiner_request_timeout_raw,
            role_name="refiner",
        )

        prover_cfg = _make_role_cfg(
            args.prover,
            args.prover_model,
            role_name="prover",
            timeout_s=prover_timeout_s,
            llm_deadline_policy=getattr(args, "llm_deadline_policy", "soft"),
            request_timeout_s=prover_request_timeout_s,
            request_timeout_disabled=prover_request_timeout_disabled,
        )
        prover_reasoning_mode, prover_reasoning_effort = _reasoning_role_cli_settings(
            args,
            "prover",
        )
        _apply_reasoning_cli_override(
            prover_cfg,
            mode=prover_reasoning_mode,
            effort=prover_reasoning_effort,
        )
        prover_client = OpenAICompatClient(
            prover_cfg,
            provider_lane_health_registry=provider_lane_health_registry,
        )
        if args.refiner:
            refiner_cfg = _make_role_cfg(
                args.refiner,
                args.refiner_model,
                role_name="refiner",
                timeout_s=refiner_timeout_s,
                llm_deadline_policy=getattr(args, "llm_deadline_policy", "soft"),
                request_timeout_s=refiner_request_timeout_s,
                request_timeout_disabled=refiner_request_timeout_disabled,
            )
            refiner_reasoning_mode, refiner_reasoning_effort = (
                _reasoning_role_cli_settings(
                    args,
                    "refiner",
                )
            )
            _apply_reasoning_cli_override(
                refiner_cfg,
                mode=refiner_reasoning_mode,
                effort=refiner_reasoning_effort,
            )
            refiner_client = OpenAICompatClient(
                refiner_cfg,
                provider_lane_health_registry=provider_lane_health_registry,
            )
        await _preflight_mini_reasoning_contract_or_defer(
            prover_client,
            role="prover",
        )
        if refiner_client is not None:
            await _preflight_mini_reasoning_contract_or_defer(
                refiner_client,
                role="refiner",
            )
        planner_escalation_client = None
        planner_escalation_choice = str(
            getattr(args, "planner_escalation", "auto") or "auto"
        ).strip().lower()
        if planner_escalation_choice == "auto":
            # On by default via the OpenAI API, but fail-soft: a run
            # configured without OPENAI_API_KEY must keep working (an
            # EXPLICIT provider choice below still fails loudly).
            if os.environ.get(
                _PROVIDER_ENV_VARS.get("openai", "OPENAI_API_KEY"), ""
            ).strip():
                planner_escalation_choice = "openai"
            else:
                planner_escalation_choice = ""
                print(
                    "[mini_prover] planner escalation disabled: "
                    "OPENAI_API_KEY is not set (pass --planner-escalation "
                    "openrouter/deepseek to use another provider, or "
                    "--planner-escalation off to silence this).",
                    flush=True,
                )
        elif planner_escalation_choice == "off":
            planner_escalation_choice = ""
        if planner_escalation_choice:
            # getattr: programmatic callers (tests, embedding) pass plain
            # namespaces that predate this flag.
            planner_escalation_model = (
                getattr(args, "planner_escalation_model", None)
                or "gpt-5.6-terra"
            )
            if planner_escalation_model in {"gpt-5.2", "gpt-5.6-terra"}:
                # Bare GPT model names target the OpenAI API. Map or reject
                # when the operator explicitly selects another provider
                # instead of failing at the first escalated call deep into a
                # run.
                if planner_escalation_choice == "openrouter":
                    planner_escalation_model = f"openai/{planner_escalation_model}"
                elif planner_escalation_choice == "deepseek":
                    raise SystemExit(
                        "--planner-escalation deepseek requires an explicit "
                        "DeepSeek model via --planner-escalation-model."
                    )
            planner_escalation_cfg = _make_role_cfg(
                planner_escalation_choice,
                planner_escalation_model,
                role_name="planner_escalation",
                timeout_s=prover_timeout_s,
                llm_deadline_policy=getattr(args, "llm_deadline_policy", "soft"),
                request_timeout_s=prover_request_timeout_s,
                request_timeout_disabled=prover_request_timeout_disabled,
            )
            planner_escalation_client = OpenAICompatClient(
                planner_escalation_cfg,
                provider_lane_health_registry=provider_lane_health_registry,
            )

        cost_budget_pricing_preflight = await _validate_cost_budget_pricing(
            max_cost_usd=float(getattr(args, "cost_budget_usd", 0.0) or 0.0),
            role_clients=(
                ("prover", prover_client),
                ("refiner", refiner_client),
                ("planner_escalation", planner_escalation_client),
            ),
        )

        run_config_record = _run_reasoning_config_record(
            args=args,
            prover_cfg=prover_cfg,
            refiner_cfg=refiner_cfg,
            prover_reasoning_mode=prover_reasoning_mode,
            prover_reasoning_effort=prover_reasoning_effort,
            refiner_reasoning_mode=refiner_reasoning_mode,
            refiner_reasoning_effort=refiner_reasoning_effort,
        )
        recorder.record_turn(run_config_record)
        print(
            "Reasoning controls: "
            f"prover={prover_reasoning_mode}"
            f"{':' + str(prover_reasoning_effort) if prover_reasoning_effort else ''}; "
            f"refiner={refiner_reasoning_mode}"
            f"{':' + str(refiner_reasoning_effort) if refiner_reasoning_effort else ''}"
        )
        def _armed_attempt_wall(role_cfg: Any) -> str:
            if role_cfg is None:
                # The role was never configured (e.g. no --refiner); claiming
                # an unbounded watchdog for a role that does not exist is the
                # same kind of misreport this message replaced.
                return "n/a"
            configured = getattr(role_cfg, "request_timeout_s", None)
            if configured is None:
                return "unbounded"
            return f"{float(configured):g}s"

        # Report what is actually armed rather than asserting a watchdog
        # exists. The old text ("each provider operation retains its finite
        # role watchdog") hid that soft policy removes the operation-level
        # deadline entirely, and cost real time diagnosing a silent stall.
        # What survives is a whole-attempt wall clock -- httpx applies the
        # value to connect/read/write/pool and it is wrapped in an outer
        # asyncio.wait -- not merely a read watchdog.
        _deadline_policy = str(
            getattr(args, "llm_deadline_policy", "soft") or "soft"
        )
        _policy_note = (
            "soft mode imposes no phase/operation deadline; what remains is"
            if _deadline_policy == "soft"
            else "hard mode adds an operation deadline on top of"
        )
        print(
            "LLM deadline policy: "
            f"{_deadline_policy} "
            f"({_policy_note} a per-HTTP-attempt wall clock, which a "
            "transport retry may restart from full: "
            f"prover={_armed_attempt_wall(prover_cfg)}, "
            f"refiner={_armed_attempt_wall(refiner_cfg)}; "
            "disable with --llm-request-timeout-s off)"
        )
        print(
            "Mini supervisor timeouts: "
            f"overall={float(getattr(args, 'mini_worker_timeout_s', 0.0) or 0.0):g}s; "
            f"startup={float(getattr(args, 'mini_worker_startup_timeout_s', 0.0) or 0.0):g}s; "
            f"shutdown={float(getattr(args, 'mini_worker_shutdown_timeout_s', 0.0) or 0.0):g}s; "
            "general-hard-operation-escalation="
            f"{'on' if bool(getattr(args, 'mini_hard_operation_watchdog', False)) else 'off'} "
            "(0s means disabled; local timeouts remain recoverable and critical "
            "transactional liveness leases remain supervisor-enforced)"
        )

        lean_cfg = LeanConfig(
            project_dir=args.lean_project_dir,
            scratch_dir=str(output_dir / ".lean_tmp"),
            timeout_s=int(args.lean_timeout_s),
            max_parallel=1,
            backend_mode="auto",
            module_search_paths=[
                str(path) for path in getattr(problem, "module_search_paths", ())
            ],
            project_imports=list(getattr(problem, "project_imports", ()) or ()),
            project_import_sources=dict(
                getattr(problem, "project_import_sources", {}) or {}
            ),
            support_project_builds={
                str(project): list(targets)
                for project, targets in dict(
                    getattr(problem, "support_project_builds", {}) or {}
                ).items()
            },
        )
        lean = LeanRunner(lean_cfg)
        # 2026-05-22: lift Lean's maxHeartbeats default for the run so
        # tsum-heavy elaboration (e.g. putnam_1978_b2) has enough
        # kernel-step budget. LeanRunner.check() reads this attribute
        # when callers don't supply max_heartbeats explicitly.
        # Override via --lean-max-heartbeats. ``getattr`` keeps tests
        # that construct ``args`` as SimpleNamespace without this attr
        # working with the CLI's 800k default.
        lean.default_max_heartbeats = int(
            getattr(args, "lean_max_heartbeats", 1600000) or 1600000
        )

        # Mini theory contributes a verified module root to Lean's process
        # environment.  Activate it before *any* theorem preflight: the
        # preflight performs a real Lean check and may lazily initialize the
        # env-cached REPL.  Mutating module_search_paths after that point would
        # leave the preflight and proof search in different Lean environments.
        theory_mode = _effective_mini_theory_mode(args)
        if theory_mode != "off":
            from .mini_theory import LLMTheoryCandidateBuilder, MiniTheoryLibrary

            theory_root = Path(
                str(
                    getattr(
                        args,
                        "mini_theory_root",
                        Path.home() / ".cache" / "mini_prover" / "theory",
                    )
                )
            ).expanduser()
            try:
                theory_library = MiniTheoryLibrary(
                    root=theory_root,
                    lean_project_dir=Path(args.lean_project_dir),
                    mode=theory_mode,
                    attempt_scope_id=(
                        "run_"
                        + hashlib.sha256(
                            str(output_dir).encode("utf-8", errors="replace")
                        ).hexdigest()[:16]
                    ),
                    verifier_timeout_s=max(
                        1.0,
                        float(
                            getattr(args, "mini_theory_verifier_timeout_s", 180.0)
                            or 180.0
                        ),
                    ),
                )
                _configure_pre_worker_retrieval_overlay(
                    theory_library,
                    output_dir,
                    expected_nonce=str(
                        getattr(
                            args,
                            "mini_theory_startup_overlay_nonce",
                            "",
                        )
                        or ""
                    ),
                )
                theory_library.activate_lean_runner(lean)
            except OSError as exc:
                raise RuntimeError(
                    "persistent Mini theory store could not be initialized at "
                    f"{theory_root}: {exc}. Use --mini-theory-root with a writable "
                    "persistent path or explicitly pass --mini-theory-mode off."
                ) from exc
            if theory_mode == "build":
                theory_candidate_builder = LLMTheoryCandidateBuilder(
                    client=prover_client,
                    cost_controller=cost_controller,
                    generated_by_model=str(getattr(prover_cfg, "model", "") or ""),
                    generated_by_run=output_dir.name,
                    source_theorem=problem.theorem_name,
                    operation_timeout_s=getattr(
                        args, "mini_theory_operation_timeout_s", None
                    ),
                )
            promotion_status: Dict[str, Any] = {}
            if (
                theory_mode == "build"
                and bool(
                    getattr(args, "mini_theory_promote_verified_helpers", False)
                )
            ):
                try:
                    from .mini_theory.promotion_outbox import PromotionOutbox

                    promotion_status = PromotionOutbox(theory_library).status()
                except Exception as promotion_status_exc:
                    promotion_status = {
                        "status_error": type(promotion_status_exc).__name__
                    }
            print(
                "Mini theory: "
                f"mode={theory_mode} root={theory_library.store.root} "
                f"domain={getattr(args, 'mini_theory_domain', 'general mathematics')} "
                "promote_verified_helpers_requested="
                f"{bool(getattr(args, 'mini_theory_promote_verified_helpers', False))} "
                "promote_verified_helpers_effective="
                f"{bool(theory_mode == 'build' and getattr(args, 'mini_theory_promote_verified_helpers', False))} "
                f"promotion_inbox={promotion_status}"
            )

        prepared_problem = await _preflight_theorem_project_input(
            lean,
            problem,
            timeout_s=max(
                1.0,
                float(getattr(args, "lean_timeout_s", 300) or 300),
            ),
        )
        if isinstance(prepared_problem, TheoremProblem):
            problem = prepared_problem
            setattr(args, "_resolved_theorem_problem", problem)
            source_provenance = problem.input_spec.get("source_statement_type")
            if source_provenance and source_provenance != problem.statement_type:
                print(f"Lean-elaborated statement type:\n  {problem.statement_type}\n")
            elif not source_provenance:
                # No elaborated provenance -> the preflight executed the raw
                # source statement (both Lean renders failed validation).
                print(
                    "Using source statement type (Lean type renders were not "
                    "self-contained)\n"
                )

        api_searcher = _init_api_searcher(lean_cfg) if args.api_search else None
        searcher = _init_mathematical_retrieval_service(
            lean_cfg=lean_cfg,
            args=args,
            api_searcher=api_searcher,
            theory_library=theory_library,
            active_imports=_lean_imports_from_text(
                str(getattr(problem, "preamble", "") or ""),
                str(getattr(problem, "raw_text", "") or ""),
            ),
        )

        try:
            proof_dossier = ProofDossier(
                theorem_name=problem.theorem_name,
                root_statement=problem.statement_type,
                problem_text=problem_docstring_text(problem),
            )
            # READY means the worker can begin proof search, not merely that
            # Python reached ``main``. MiniSession fires the callback only
            # after premise retrieval and session construction.
            from .mini_session.process_watchdog import signal_worker_ready
            ok, proof = await prove_problem(
                problem=problem,
                prover_client=prover_client,
                refiner_client=refiner_client,
                planner_escalation_client=planner_escalation_client,
                lean=lean,
                max_prove_turns=int(args.max_prove_turns),
                max_refine_turns=int(args.max_refine_turns),
                recorder=recorder,
                searcher=searcher,
                mathematical_retrieval_enabled=bool(
                    getattr(args, "mathematical_retrieval", True)
                ),
                lean_check_tool_enabled=bool(args.lean_check_tool),
                try_lean_tool_enabled=bool(getattr(args, "try_lean_tool", True)),
                compute_examples_tool_enabled=bool(
                    getattr(args, "compute_examples_tool", True)
                ),
                apply_decl_to_goal_tool_enabled=bool(
                    getattr(args, "apply_decl_to_goal_tool", True)
                ),
                max_tool_calls_per_turn=int(args.max_tool_calls_per_turn),
                raw_feedback=bool(args.raw_feedback),
                opaque_mode=bool(getattr(args, "opaque_mode", True)),
                allow_official_answer_visibility=bool(
                    getattr(args, "allow_official_answer_visibility", False)
                ),
                premise_retrieval_enabled=bool(
                    getattr(args, "premise_retrieval", False)
                ),
                proof_state_retrieval_enabled=bool(
                    getattr(args, "proof_state_retrieval", False)
                ),
                premise_retrieval_top_k=int(
                    getattr(args, "premise_retrieval_top_k", 64)
                ),
                premise_zero_hit_policy=str(
                    getattr(args, "premise_zero_hit_policy", "off") or "off"
                ),
                premise_zero_hit_suppress_library_first=bool(
                    getattr(args, "premise_zero_hit_suppress_library_first", True)
                ),
                premise_zero_hit_max_local_turns=max(
                    0,
                    int(getattr(args, "premise_zero_hit_max_local_turns", 1) or 0),
                ),
                premise_zero_hit_allow_api_grounding_after_lean_failure=bool(
                    getattr(
                        args,
                        "premise_zero_hit_allow_api_grounding_after_lean_failure",
                        True,
                    )
                ),
                repair_retrieval_enabled=bool(
                    getattr(args, "repair_retrieval", True)
                ),
                repair_retrieval_top_k=max(
                    0, int(getattr(args, "repair_retrieval_top_k", 6) or 0)
                ),
                parallel_samples=max(
                    1, int(getattr(args, "parallel_samples", 1) or 1)
                ),
                parallel_temperatures=tuple(
                    float(t.strip())
                    for t in str(getattr(args, "parallel_temps", "") or "").split(",")
                    if t.strip()
                ),
                parallel_late_sample_grace_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "parallel_late_sample_grace_s",
                            _PARALLEL_SAMPLE_LATE_GRACE_DEFAULT_S,
                        )
                        or 0.0
                    ),
                ),
                mini_phase_temperatures=mini_phase_temperature_policy,
                proof_state_engine_enabled=bool(
                    getattr(args, "proof_state_engine", True)
                ),
                proof_state_child_tactics_enabled=bool(
                    getattr(args, "proof_state_child_tactics", True)
                ),
                proof_state_child_tactic_timeout_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "proof_state_child_tactic_timeout_s",
                            DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                        )
                        or 0.0
                    ),
                ),
                proof_state_child_tactic_max_candidates=max(
                    0,
                    int(
                        getattr(
                            args,
                            "proof_state_child_tactic_max_candidates",
                            36,
                        )
                        or 0
                    ),
                ),
                proof_state_child_goal_limit=max(
                    0, int(getattr(args, "proof_state_child_goal_limit", 3) or 0)
                ),
                proof_state_decl_application_limit=max(
                    0,
                    int(
                        getattr(
                            args,
                            "proof_state_decl_application_limit",
                            6,
                        )
                        or 0
                    ),
                ),
                proof_state_batch_parallelism=max(
                    1,
                    int(getattr(args, "proof_state_batch_parallelism", 1) or 1),
                ),
                formal_state_search_enabled=(
                    bool(getattr(args, "formal_state_search", False))
                    if bool(
                        getattr(args, "_formal_state_search_explicit", False)
                    )
                    else None
                ),
                formal_state_search_timeout_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "formal_state_search_timeout_s",
                            DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                        )
                        or 0.0
                    ),
                ),
                formal_state_search_operation_timeout_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "formal_state_search_operation_timeout_s",
                            DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
                        )
                        or 0.0
                    ),
                ),
                formal_state_search_provider_timeout_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "formal_state_search_provider_timeout_s",
                            0.0,
                        )
                        or 0.0
                    ),
                ),
                formal_state_search_provider_max_tokens=max(
                    0,
                    int(
                        getattr(
                            args,
                            "formal_state_search_provider_max_tokens",
                            0,
                        )
                        or 0
                    ),
                ),
                formal_state_search_provider_reasoning_effort=str(
                    getattr(
                        args,
                        "formal_state_search_provider_reasoning_effort",
                        DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
                    )
                    or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
                ),
                formal_state_search_provider_max_attempts=max(
                    1,
                    int(
                        getattr(
                            args,
                            "formal_state_search_provider_max_attempts",
                            2,
                        )
                        or 1
                    ),
                ),
                formal_state_search_provider_retry_backoff_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "formal_state_search_provider_retry_backoff_s",
                            5.0,
                        )
                        or 0.0
                    ),
                ),
                formal_state_search_beam_width=max(
                    1,
                    int(getattr(args, "formal_state_search_beam_width", 4) or 1),
                ),
                formal_state_search_max_steps=max(
                    1,
                    int(getattr(args, "formal_state_search_max_steps", 8) or 1),
                ),
                formal_state_search_max_candidates=max(
                    1,
                    int(
                        getattr(args, "formal_state_search_max_candidates", 6)
                        or 1
                    ),
                ),
                formal_state_search_backtrack_limit=max(
                    0,
                    int(
                        getattr(args, "formal_state_search_backtrack_limit", 8)
                        or 0
                    ),
                ),
                formal_state_search_max_no_improvement_quanta=max(
                    0,
                    int(
                        getattr(
                            args,
                            "formal_state_search_max_no_improvement_quanta",
                            6,
                        )
                        or 0
                    ),
                ),
                falsification_enabled=bool(
                    getattr(args, "mini_falsification", True)
                ),
                falsification_max_checks=falsification_max_checks,
                falsification_operation_timeout_s=falsification_operation_timeout_s,
                falsification_engine_timeout_s=falsification_engine_timeout_s,
                proof_state_cache_enabled=bool(
                    getattr(args, "proof_state_cache", True)
                ),
                proof_state_cache_path=(
                    Path(str(getattr(args, "proof_state_cache_path", "") or ""))
                    if str(getattr(args, "proof_state_cache_path", "") or "").strip()
                    else None
                ),
                root_tactic_prepass_enabled=bool(
                    getattr(args, "root_tactic_prepass", False)
                ),
                root_tactic_timeout_s=max(
                    0.0, float(getattr(args, "root_tactic_timeout_s", 40.0) or 0.0)
                ),
                root_tactic_max_candidates=max(
                    0, int(getattr(args, "root_tactic_max_candidates", 64) or 0)
                ),
                startup_root_fast_lane_enabled=bool(
                    getattr(args, "startup_root_fast_lane", False)
                ),
                startup_root_fast_lane_tactic_timeout_s=max(
                    0.1,
                    float(
                        getattr(
                            args,
                            "startup_root_fast_lane_tactic_timeout_s",
                            300.0,
                        )
                        or 0.1
                    ),
                ),
                startup_root_fast_lane_tactic_max_candidates=max(
                    1,
                    int(
                        getattr(
                            args,
                            "startup_root_fast_lane_tactic_max_candidates",
                            12,
                        )
                        or 1
                    ),
                ),
                mini_recursive_enabled=bool(
                    getattr(args, "mini_recursive", True)
                ),
                adaptive_recursive_on_stall=bool(
                    getattr(args, "adaptive_recursive_on_stall", True)
                ),
                mini_recursive_passes=max(
                    1, int(getattr(args, "mini_recursive_passes", 6) or 6)
                ),
                mini_recursive_max_claims=max(
                    1,
                    int(
                        getattr(
                            args,
                            "mini_recursive_claims",
                            PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
                        )
                        or PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS
                    ),
                ),
                mini_recursive_turns_per_claim=max(
                    1,
                    int(getattr(args, "mini_recursive_turns_per_claim", 6) or 6),
                ),
                mini_recursive_tactic_timeout_s=max(
                    1.0,
                    float(
                        getattr(args, "mini_recursive_tactic_timeout_s", 60.0)
                        or 60.0
                    ),
                ),
                mini_recursive_tactic_max_candidates=max(
                    1,
                    int(
                        getattr(
                            args,
                            "mini_recursive_tactic_max_candidates",
                            48,
                        )
                        or 48
                    ),
                ),
                dossier=proof_dossier,
                recursive_helper_prover_enabled=bool(
                    getattr(args, "recursive_helper_prover", True)
                ),
                recursive_helper_budget=int(
                    getattr(args, "recursive_helper_budget", 0) or 0
                ),
                recursive_helper_max_depth=int(
                    getattr(args, "recursive_helper_max_depth", 3)
                    if getattr(args, "recursive_helper_max_depth", 3) is not None
                    else 3
                ),
                recursive_helper_max_attempts_per_node=int(
                    getattr(args, "recursive_helper_max_attempts_per_node", 2)
                    if getattr(args, "recursive_helper_max_attempts_per_node", 2)
                    is not None
                    else 2
                ),
                recursive_helper_turns=int(
                    getattr(args, "recursive_helper_turns", 5) or 5
                ),
                recursive_helper_refine=bool(
                    getattr(args, "recursive_helper_refine", True)
                ),
                cost_controller=cost_controller,
                run_wall_clock_budget_s=max(
                    0.0,
                    float(
                        getattr(args, "mini_run_wall_clock_budget_s", 0.0)
                        or 0.0
                    ),
                ),
                no_strong_progress_budget_s=max(
                    0.0,
                    float(
                        getattr(
                            args,
                            "mini_no_strong_progress_budget_s",
                            0.0,
                        )
                        or 0.0
                    ),
                ),
                theory_library=theory_library,
                theory_candidate_builder=theory_candidate_builder,
                theory_domain=str(
                    getattr(args, "mini_theory_domain", "general mathematics")
                    or "general mathematics"
                ),
                theory_bundle_ids=tuple(
                    str(item or "").strip()
                    for item in getattr(args, "mini_theory_bundles", [])
                    if str(item or "").strip()
                ),
                theory_promote_verified_helpers=bool(
                    getattr(args, "mini_theory_promote_verified_helpers", False)
                ),
                worker_ready_callback=signal_worker_ready,
            )
        except Exception as exc:
            failure_reason = f"{type(exc).__name__}: {exc}"
            infrastructure_aborted = True
            print(f"\nUNCAUGHT EXCEPTION: {failure_reason}", flush=True)
    except SystemExit as exc:
        # Setup-side SystemExit (most commonly missing API key from
        # ``_make_role_cfg``). Capture it so the finally block can finalize
        # the recorder and write a summary documenting the failure, then
        # re-raise after cleanup so the process exits with the original
        # code/message.
        failure_reason = (
            f"SystemExit: {exc.code}" if exc.code is not None else "SystemExit"
        )
        print(f"\nSETUP FAILED: {exc}", flush=True)
        pending_reraise = exc
    except KeyboardInterrupt as exc:
        failure_reason, failure_reason_detail = _mini_prover_external_stop_reason(exc)
        print(f"\nINTERRUPTED: {failure_reason}", flush=True)
        pending_reraise = exc
    except asyncio.CancelledError as exc:
        failure_reason, failure_reason_detail = _mini_prover_external_stop_reason(exc)
        if cooperative_stop_signals:
            failure_reason = "user_interrupted"
            failure_reason_detail = (
                f"cooperative_stop_signal:{cooperative_stop_signals[0]}"
            )
        print(f"\nCANCELLED: {failure_reason}", flush=True)
        pending_reraise = exc
    except Exception as exc:
        # Setup-side exception other than SystemExit (e.g. malformed URL in
        # OpenAICompatClient, lean project dir missing, etc.). Recorded as
        # the failure reason; we don't re-raise — the function returns 1.
        failure_reason = f"{type(exc).__name__}: {exc}"
        infrastructure_aborted = True
        print(f"\nSETUP FAILED: {failure_reason}", flush=True)
    except BaseException as exc:
        failure_reason, failure_reason_detail = _mini_prover_external_stop_reason(exc)
        print(f"\nABORTED: {failure_reason}", flush=True)
        pending_reraise = exc
    finally:
        shutdown_leases = getattr(args, "_mini_shutdown_leases", None)
        if isinstance(shutdown_leases, list) and not shutdown_leases:
            from .mini_session.process_watchdog import (
                begin_process_deadline,
                worker_shutdown_timeout_s,
            )

            shutdown_timeout_s = worker_shutdown_timeout_s()
            shutdown_leases.append(
                begin_process_deadline(
                    deadline_monotonic=(
                        time.monotonic() + shutdown_timeout_s
                        if shutdown_timeout_s > 0.0
                        else 0.0
                    ),
                    label="mini_session_asyncio_shutdown",
                    supervisor_enforced=True,
                )
            )
        # A mathematically finalized root proof must become recoverable before
        # any transport/accounting close can resist cancellation. The small
        # receipt only authorizes the supervisor to run the ordinary
        # independent Lean export verifier; it never marks the run solved.
        if (
            ok
            and isinstance(proof, str)
            and proof.strip()
            and os.environ.get("ENSEMBLE_MINI_DEFER_SOLVED_EXPORT") == "1"
            and not getattr(proof_dossier, "root_disproof_certificate", None)
        ):
            try:
                from .mini_session.process_watchdog import (
                    write_staged_solution_receipt,
                )

                official_answer_payload_present = (
                    _problem_has_official_answer_payload(problem)
                )
                answer_visible = _official_answer_visible_to_llm(
                    opaque_mode=bool(getattr(args, "opaque_mode", True)),
                    allow_official_answer_visibility=bool(
                        getattr(args, "allow_official_answer_visibility", False)
                    ),
                    official_answer_payload_present=(
                        official_answer_payload_present
                    ),
                )
                early_summary = {
                    "problem": problem.theorem_name,
                    "run_source_provenance": copy.deepcopy(
                        run_source_provenance
                    ),
                    "lean_file": str(problem.path.resolve()),
                    "theorem_project": problem.theorem_project_record(),
                    "theorem_project_input_hash": str(problem.input_spec_hash),
                    "theorem_project_adapter": str(problem.adapter_id),
                    "theorem_project_export": {
                        "schema_version": 1,
                        "adapter_id": str(problem.adapter_id),
                        "theorem_name": str(problem.theorem_name),
                        "declaration_name": str(
                            getattr(problem, "declaration_name", "")
                            or problem.theorem_name
                        ),
                        "declaration_universe_suffix": str(
                            getattr(problem, "declaration_universe_suffix", "")
                            or ""
                        ),
                        "declaration_public": bool(
                            getattr(problem, "declaration_public", False)
                        ),
                        "target_scoped_prefix": str(
                            getattr(problem, "target_scoped_prefix", "") or ""
                        ),
                        "target_omit_variables": list(
                            getattr(problem, "target_omit_variables", ()) or ()
                        ),
                        "statement_type": str(problem.statement_type),
                        "preamble": decode_theorem_target_context(
                            str(
                                problem.lean_preamble
                                if answer_visible
                                else problem.preamble
                            )
                        )[0],
                        "docstring": str(problem.docstring or ""),
                        "source_path": str(problem.path.resolve()),
                        "source_sha256": str(
                            problem.input_spec.get("source_sha256", "")
                        ),
                        "artifact_slug": str(problem.artifact_slug),
                    },
                    "putnam_file": (
                        str(problem.path.resolve())
                        if problem.adapter_id == PUTNAMBENCH_ADAPTER_ID
                        else None
                    ),
                    "solved": False,
                    "pre_export_solved": True,
                    "session_root_finalized": True,
                    "final_proof": proof,
                    "final_proof_helpers": list(
                        getattr(proof_dossier, "final_replay_helpers", ()) or ()
                    ),
                    "disproved": False,
                    "root_disproof_certificate": None,
                    "failure_reason": "solved_export_not_attempted",
                    "failure_reason_detail": None,
                    "opaque_mode": bool(getattr(args, "opaque_mode", True)),
                    "allow_official_answer_visibility": bool(
                        getattr(args, "allow_official_answer_visibility", False)
                    ),
                    "official_answer_payload_present": bool(
                        official_answer_payload_present
                    ),
                    "answer_visibility": _answer_visibility_label(
                        opaque_mode=bool(getattr(args, "opaque_mode", True)),
                        allow_official_answer_visibility=bool(
                            getattr(
                                args,
                                "allow_official_answer_visibility",
                                False,
                            )
                        ),
                        official_answer_payload_present=(
                            official_answer_payload_present
                        ),
                    ),
                    **_mini_solved_export_status("not_attempted"),
                    "mini_solved_export_downgrades_solved": 0,
                }
                write_staged_solution_receipt(
                    output_dir,
                    theorem_name=problem.theorem_name,
                    summary=early_summary,
                )
                early_staged_solution_written = True
            except Exception as early_receipt_exc:
                print(
                    "Mini-session early staged-proof receipt could not be "
                    f"written: {type(early_receipt_exc).__name__}: "
                    f"{early_receipt_exc}",
                    file=sys.stderr,
                )
        # Cleanup runs unconditionally — including for KeyboardInterrupt and
        # any other BaseException — so stdout/stderr are always restored and
        # no ghost run dir without a summary is left behind.
        try:
            try:
                controller_failure_reason = (
                    str(
                        getattr(
                            proof_dossier,
                            "session_failure_reason",
                            "",
                        )
                        or ""
                    )
                    or None
                )
                usage_summary: Dict[str, Any] = {}
                if cost_controller is not None:
                    # Freeze the transport boundary before freezing cost
                    # accounting. Detached HTTP receipts can otherwise arrive
                    # after summary.json has already declared usage missing.
                    seen_clients: set[int] = set()
                    all_clients_closed = True
                    client_close_tasks: List[tuple[Any, asyncio.Task[Any]]] = []
                    for client in (
                        prover_client,
                        refiner_client,
                        planner_escalation_client,
                    ):
                        if client is None or id(client) in seen_clients:
                            continue
                        seen_clients.add(id(client))
                        llm_client_close_attempted_ids.add(id(client))
                        client_close_tasks.append((
                            client,
                            asyncio.create_task(_supervised_resource_close(
                                client.close(),
                                label="mini_session_client_close_before_summary",
                            )),
                        ))
                    client_close_results = await asyncio.gather(
                        *(task for _client, task in client_close_tasks),
                        return_exceptions=True,
                    )
                    for (_client, _task), close_result in zip(
                        client_close_tasks,
                        client_close_results,
                    ):
                        if isinstance(close_result, BaseException):
                            all_clients_closed = False
                            recorder.record_turn(
                                {
                                    "phase": "llm_usage",
                                    "verdict": "llm_transport_close_failed_before_summary",
                                    "error": format_exception(close_result)[:500],
                                }
                            )
                    drain_late_usage = getattr(cost_controller, "drain_late_usage", None)
                    if callable(drain_late_usage):
                        await drain_late_usage(timeout_s=1.0)
                    freeze_final_accounting = getattr(
                        cost_controller,
                        "freeze_final_accounting",
                        None,
                    )
                    if callable(freeze_final_accounting):
                        await freeze_final_accounting()
                    usage_summary = dict(cost_controller.summary())
                    usage_summary["llm_clients_closed_before_summary"] = bool(
                        all_clients_closed
                    )
                    usage_summary["llm_transport_quiescent_before_summary"] = bool(
                        all_clients_closed
                    )
                    if not all_clients_closed:
                        # Diagnostic only. Unresolved HTTP tails must not become
                        # the public mathematical failure_reason.
                        usage_summary["llm_finalization_failure_reason"] = (
                            "llm_transport_not_quiescent_before_summary"
                        )
                    if int(usage_summary.get("llm_usage_events", 0) or 0) <= 0:
                        fallback_usage = usage_totals_from_clients(
                            (
                                ("prover", prover_client),
                                ("refiner", refiner_client),
                                ("planner_escalation", planner_escalation_client),
                            )
                        )
                        usage_summary = {**usage_summary, **fallback_usage}
                    cost_failure_reason = str(
                        usage_summary.get("llm_cost_budget_terminal_reason")
                        or ""
                    ).strip()
                    if (
                        cost_failure_reason
                        and not ok
                        and not controller_failure_reason
                    ):
                        controller_failure_reason = cost_failure_reason
                effective_failure_reason = _mini_prover_unsolved_failure_reason(
                    ok=bool(ok),
                    failure_reason=failure_reason,
                    controller_failure_reason=controller_failure_reason,
                    usage_summary=usage_summary,
                    recorder_metrics=dict(getattr(recorder, "metrics", {}) or {}),
                )
                failure_reason_detail = _mini_prover_unsolved_failure_detail(
                    ok=bool(ok),
                    effective_failure_reason=effective_failure_reason,
                    existing_detail=failure_reason_detail,
                    recorder_metrics=dict(getattr(recorder, "metrics", {}) or {}),
                )
                official_answer_payload_present = _problem_has_official_answer_payload(
                    problem
                )
                pre_export_solved = bool(ok)
                promotion_requested = bool(
                    getattr(
                        args,
                        "mini_theory_promote_verified_helpers",
                        False,
                    )
                )
                promotion_effective = bool(
                    _effective_mini_theory_mode(args) == "build"
                    and promotion_requested
                )
                promotion_summary = dict(
                    getattr(
                        proof_dossier,
                        "mini_theory_promotion_report",
                        {},
                    )
                    or {}
                )
                if promotion_effective and theory_library is not None:
                    try:
                        from .mini_theory.promotion_outbox import PromotionOutbox

                        promotion_summary = {
                            **promotion_summary,
                            **PromotionOutbox(theory_library).status(),
                        }
                    except Exception as promotion_status_exc:
                        promotion_summary.setdefault("status_failures", 1)
                        promotion_summary.setdefault(
                            "status_error",
                            f"{type(promotion_status_exc).__name__}: "
                            f"{promotion_status_exc}",
                        )
                promotion_summary.update(
                    {
                        "requested": promotion_requested,
                        "effective": promotion_effective,
                        "receipt_owner_id": (
                            str(theory_library.lease_owner.owner_id)
                            if promotion_effective and theory_library is not None
                            else ""
                        ),
                    }
                )
                summary_payload = {
                    "problem": problem.theorem_name,
                    "run_source_provenance": copy.deepcopy(
                        run_source_provenance
                    ),
                    "lean_file": str(problem.path.resolve()),
                    "theorem_project": problem.theorem_project_record(),
                    "theorem_project_input_hash": str(problem.input_spec_hash),
                    "theorem_project_adapter": str(problem.adapter_id),
                    "theorem_project_export": {
                        "schema_version": 1,
                        "adapter_id": str(problem.adapter_id),
                        "theorem_name": str(problem.theorem_name),
                        "declaration_name": str(
                            getattr(problem, "declaration_name", "")
                            or problem.theorem_name
                        ),
                        "declaration_universe_suffix": str(
                            getattr(problem, "declaration_universe_suffix", "")
                            or ""
                        ),
                        "declaration_public": bool(
                            getattr(problem, "declaration_public", False)
                        ),
                        "target_scoped_prefix": str(
                            getattr(problem, "target_scoped_prefix", "") or ""
                        ),
                        "target_omit_variables": list(
                            getattr(problem, "target_omit_variables", ()) or ()
                        ),
                        "statement_type": str(problem.statement_type),
                        "preamble": decode_theorem_target_context(
                            str(
                                problem.lean_preamble
                                if _official_answer_visible_to_llm(
                                opaque_mode=bool(getattr(args, "opaque_mode", True)),
                                allow_official_answer_visibility=bool(
                                    getattr(
                                        args,
                                        "allow_official_answer_visibility",
                                        False,
                                    )
                                ),
                                official_answer_payload_present=(
                                    official_answer_payload_present
                                ),
                            )
                                else problem.preamble
                            )
                        )[0],
                        "docstring": str(problem.docstring or ""),
                        "source_path": str(problem.path.resolve()),
                        "source_sha256": str(
                            problem.input_spec.get("source_sha256", "")
                        ),
                        "artifact_slug": str(problem.artifact_slug),
                    },
                    "putnam_file": (
                        str(problem.path.resolve())
                        if problem.adapter_id == PUTNAMBENCH_ADAPTER_ID
                        else None
                    ),
                    "solved": bool(ok and not pre_export_solved),
                    "pre_export_solved": pre_export_solved,
                    "session_root_finalized": pre_export_solved,
                    "final_proof": proof,
                    "final_proof_helpers": (
                        list(proof_dossier.final_replay_helpers)
                        if proof_dossier
                        else []
                    ),
                    "root_proof_certificate": (
                        copy.deepcopy(proof_dossier.root_proof_certificate)
                        if proof_dossier
                        else None
                    ),
                    "disproved": bool(
                        proof_dossier
                        and getattr(
                            proof_dossier,
                            "root_disproof_certificate",
                            None,
                        )
                    ),
                    "root_disproof_certificate": (
                        copy.deepcopy(proof_dossier.root_disproof_certificate)
                        if proof_dossier
                        else None
                    ),
                    "failure_reason": (
                        "solved_export_not_attempted"
                        if pre_export_solved
                        else effective_failure_reason
                    ),
                    "failure_reason_detail": failure_reason_detail,
                    "controller_failure_reason": controller_failure_reason,
                    "prover": (
                        {"provider": args.prover, "model": prover_cfg.model}
                        if prover_cfg
                        else None
                    ),
                    "refiner": (
                        {"provider": args.refiner, "model": refiner_cfg.model}
                        if refiner_cfg
                        else None
                    ),
                    "prover_timeout_s": (
                        float(prover_cfg.timeout_s)
                        if prover_cfg and prover_cfg.timeout_s is not None
                        else None
                    ),
                    "refiner_timeout_s": (
                        float(refiner_cfg.timeout_s)
                        if refiner_cfg and refiner_cfg.timeout_s is not None
                        else None
                    ),
                    "llm_deadline_policy": str(
                        getattr(args, "llm_deadline_policy", "soft") or "soft"
                    ),
                    "mini_worker_timeout_s": float(
                        getattr(args, "mini_worker_timeout_s", 0.0) or 0.0
                    ),
                    "mini_run_wall_clock_budget_s": float(
                        getattr(args, "mini_run_wall_clock_budget_s", 0.0)
                        or 0.0
                    ),
                    "mini_no_strong_progress_budget_s": float(
                        getattr(
                            args,
                            "mini_no_strong_progress_budget_s",
                            0.0,
                        )
                        or 0.0
                    ),
                    "mini_worker_startup_timeout_s": float(
                        getattr(args, "mini_worker_startup_timeout_s", 0.0) or 0.0
                    ),
                    "mini_worker_shutdown_timeout_s": float(
                        getattr(args, "mini_worker_shutdown_timeout_s", 0.0) or 0.0
                    ),
                    "mini_hard_operation_watchdog": bool(
                        getattr(args, "mini_hard_operation_watchdog", False)
                    ),
                    "prover_llm_deadline_policy": (
                        str(getattr(prover_cfg, "llm_deadline_policy", ""))
                        if prover_cfg
                        else ""
                    ),
                    "refiner_llm_deadline_policy": (
                        str(getattr(refiner_cfg, "llm_deadline_policy", ""))
                        if refiner_cfg
                        else ""
                    ),
                    "prover_llm_deadline": _llm_deadline_cli_summary(prover_cfg),
                    "refiner_llm_deadline": _llm_deadline_cli_summary(refiner_cfg),
                    "reasoning_mode": _normalize_reasoning_cli_mode(
                        getattr(args, "reasoning_mode", _REASONING_PROVIDER_DEFAULT)
                    ),
                    "reasoning_effort": str(
                        getattr(args, "reasoning_effort", None) or ""
                    ),
                    "prover_reasoning_mode": prover_reasoning_mode,
                    "prover_reasoning_effort": str(prover_reasoning_effort or ""),
                    "refiner_reasoning_mode": refiner_reasoning_mode,
                    "refiner_reasoning_effort": str(refiner_reasoning_effort or ""),
                    "prover_reasoning": _reasoning_cli_summary(
                        prover_cfg,
                        provider=getattr(args, "prover", None),
                        requested_mode=prover_reasoning_mode,
                        requested_effort=prover_reasoning_effort,
                    ),
                    "refiner_reasoning": _reasoning_cli_summary(
                        refiner_cfg,
                        provider=getattr(args, "refiner", None),
                        requested_mode=refiner_reasoning_mode,
                        requested_effort=refiner_reasoning_effort,
                    ),
                    "max_prove_turns": int(args.max_prove_turns),
                    "max_refine_turns": int(args.max_refine_turns),
                    # Stable telemetry fields for sweep/analysis consumers.
                    # There is only one production backend now.
                    "use_mini_session": True,
                    "prove_problem_path": "mini_session",
                    "cost_budget_usd": max(
                        0.0,
                        float(getattr(args, "cost_budget_usd", 0.0) or 0.0),
                    ),
                    "cost_budget_reserve_output_tokens": max(
                        0,
                        int(
                            getattr(
                                args,
                                "cost_budget_reserve_output_tokens",
                                1024,
                            )
                            or 0
                        ),
                    ),
                    "cost_budget_pricing_preflight": list(
                        cost_budget_pricing_preflight
                    ),
                    **usage_summary,
                    "mini_theory_mode": str(
                        _effective_mini_theory_mode(args)
                    ),
                    "mini_theory_root": (
                        str(theory_library.store.root)
                        if theory_library is not None
                        else ""
                    ),
                    "mini_theory_domain": str(
                        getattr(args, "mini_theory_domain", "general mathematics")
                        or "general mathematics"
                    ),
                    "mini_theory_snapshot": list(
                        getattr(proof_dossier, "mini_theory_snapshot", ()) or ()
                    ) if proof_dossier is not None else [],
                    "mini_theory_context_hash": str(
                        getattr(proof_dossier, "mini_theory_context_hash", "") or ""
                    ) if proof_dossier is not None else "",
                    "mini_theory_promote_verified_helpers_requested": (
                        promotion_requested
                    ),
                    "mini_theory_promote_verified_helpers_effective": (
                        promotion_effective
                    ),
                    "mini_theory_promotion": promotion_summary,
                    "mini_theory_integrity_issues": (
                        list(theory_library.integrity_issues())
                        if theory_library is not None
                        else []
                    ),
                    "api_search_enabled": bool(args.api_search),
                    "api_search_active": searcher is not None,
                    "lean_check_tool_enabled": bool(args.lean_check_tool),
                    "try_lean_tool_enabled": bool(
                        getattr(args, "try_lean_tool", True)
                    ),
                    "compute_examples_tool_enabled": bool(
                        getattr(args, "compute_examples_tool", True)
                    ),
                    "apply_decl_to_goal_tool_enabled": bool(
                        getattr(args, "apply_decl_to_goal_tool", True)
                    ),
                    "max_tool_calls_per_turn": int(args.max_tool_calls_per_turn),
                    "raw_feedback": bool(args.raw_feedback),
                    "opaque_mode": bool(getattr(args, "opaque_mode", True)),
                    "allow_official_answer_visibility": bool(
                        getattr(args, "allow_official_answer_visibility", False)
                    ),
                    "official_answer_payload_present": bool(
                        official_answer_payload_present
                    ),
                    "official_answer_visible_to_llm": _official_answer_visible_to_llm(
                        opaque_mode=bool(getattr(args, "opaque_mode", True)),
                        allow_official_answer_visibility=bool(
                            getattr(
                                args,
                                "allow_official_answer_visibility",
                                False,
                            )
                        ),
                        official_answer_payload_present=official_answer_payload_present,
                    ),
                    "answer_visibility": _answer_visibility_label(
                        opaque_mode=bool(getattr(args, "opaque_mode", True)),
                        allow_official_answer_visibility=bool(
                            getattr(
                                args,
                                "allow_official_answer_visibility",
                                False,
                            )
                        ),
                        official_answer_payload_present=official_answer_payload_present,
                    ),
                    "putnambench_answer_variant": (
                        _putnambench_answer_variant_label(
                            opaque_mode=bool(getattr(args, "opaque_mode", True)),
                            allow_official_answer_visibility=bool(
                                getattr(
                                    args,
                                    "allow_official_answer_visibility",
                                    False,
                                )
                            ),
                            official_answer_payload_present=(
                                official_answer_payload_present
                            ),
                        )
                        if problem.adapter_id == PUTNAMBENCH_ADAPTER_ID
                        else None
                    ),
                    "premise_retrieval_enabled": bool(
                        getattr(args, "premise_retrieval", False)
                    ),
                    "proof_state_retrieval_enabled": bool(
                        getattr(args, "proof_state_retrieval", False)
                    ),
                    "premise_retrieval_top_k": int(
                        getattr(args, "premise_retrieval_top_k", PREMISE_DEFAULT_TOP_K)
                    ),
                    "premise_zero_hit_policy": str(
                        getattr(args, "premise_zero_hit_policy", "off") or "off"
                    ),
                    "premise_zero_hit_suppress_library_first": bool(
                        getattr(args, "premise_zero_hit_suppress_library_first", True)
                    ),
                    "premise_zero_hit_max_local_turns": max(
                        0,
                        int(
                            getattr(args, "premise_zero_hit_max_local_turns", 1)
                            or 0
                        ),
                    ),
                    "premise_zero_hit_allow_api_grounding_after_lean_failure": bool(
                        getattr(
                            args,
                            "premise_zero_hit_allow_api_grounding_after_lean_failure",
                            True,
                        )
                    ),
                    "repair_retrieval_enabled": bool(
                        getattr(args, "repair_retrieval", True)
                    ),
                    "repair_retrieval_top_k": max(
                        0, int(getattr(args, "repair_retrieval_top_k", 6) or 0)
                    ),
                    "parallel_samples": max(
                        1, int(getattr(args, "parallel_samples", 1) or 1)
                    ),
                    "parallel_temps": str(
                        getattr(args, "parallel_temps", "") or ""
                    ),
                    "parallel_late_sample_grace_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "parallel_late_sample_grace_s",
                                _PARALLEL_SAMPLE_LATE_GRACE_DEFAULT_S,
                            )
                            or 0.0
                        ),
                    ),
                    "mini_phase_temperatures": (
                        {
                            "enabled": bool(mini_phase_temperature_policy.enabled),
                            "planner": float(mini_phase_temperature_policy.planner),
                            "initial_proof": float(
                                mini_phase_temperature_policy.initial_proof
                            ),
                            "formalization_helper": float(
                                mini_phase_temperature_policy.formalization_helper
                            ),
                            "lean_repair": float(
                                mini_phase_temperature_policy.lean_repair
                            ),
                            "refine": float(mini_phase_temperature_policy.refine),
                            "route_assembly": float(
                                mini_phase_temperature_policy.route_assembly
                            ),
                            "stagnation_escape": float(
                                mini_phase_temperature_policy.stagnation_escape
                            ),
                            "use_sample_temperature_for_initial": bool(
                                mini_phase_temperature_policy.use_sample_temperature_for_initial
                            ),
                        }
                        if mini_phase_temperature_policy is not None
                        else {"enabled": False}
                    ),
                    "proof_state_engine_enabled": bool(
                        getattr(args, "proof_state_engine", True)
                    ),
                    "proof_state_child_tactics_enabled": bool(
                        getattr(args, "proof_state_child_tactics", True)
                    ),
                    "proof_state_child_tactic_timeout_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "proof_state_child_tactic_timeout_s",
                                DEFAULT_PROOF_STATE_CHILD_TACTIC_TIMEOUT_S,
                            )
                            or 0.0
                        ),
                    ),
                    "proof_state_child_tactic_max_candidates": max(
                        0,
                        int(
                            getattr(
                                args,
                                "proof_state_child_tactic_max_candidates",
                                36,
                            )
                            or 0
                        ),
                    ),
                    "proof_state_child_goal_limit": max(
                        0,
                        int(
                            getattr(args, "proof_state_child_goal_limit", 3)
                            or 0
                        ),
                    ),
                    "proof_state_decl_application_limit": max(
                        0,
                        int(
                            getattr(
                                args,
                                "proof_state_decl_application_limit",
                                6,
                            )
                            or 0
                        ),
                    ),
                    "proof_state_batch_parallelism": max(
                        1,
                        int(
                            getattr(args, "proof_state_batch_parallelism", 1)
                            or 1
                        ),
                    ),
                    "formal_state_search_enabled": (
                        _effective_cli_formal_state_search(args)
                    ),
                    "formal_state_search_timeout_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "formal_state_search_timeout_s",
                                DEFAULT_FORMAL_STATE_SEARCH_TOTAL_TIMEOUT_S,
                            )
                            or 0.0
                        ),
                    ),
                    "formal_state_search_operation_timeout_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "formal_state_search_operation_timeout_s",
                                DEFAULT_FORMAL_STATE_SEARCH_OPERATION_TIMEOUT_S,
                            )
                            or 0.0
                        ),
                    ),
                    "formal_state_search_provider_timeout_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "formal_state_search_provider_timeout_s",
                                0.0,
                            )
                            or 0.0
                        ),
                    ),
                    "formal_state_search_provider_max_tokens": max(
                        0,
                        int(
                            getattr(
                                args,
                                "formal_state_search_provider_max_tokens",
                                0,
                            )
                            or 0
                        ),
                    ),
                    "formal_state_search_provider_reasoning_effort": str(
                        getattr(
                            args,
                            "formal_state_search_provider_reasoning_effort",
                            DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT,
                        )
                        or DEFAULT_FORMAL_STATE_SEARCH_PROVIDER_REASONING_EFFORT
                    ),
                    "formal_state_search_provider_max_attempts": max(
                        1,
                        int(
                            getattr(
                                args,
                                "formal_state_search_provider_max_attempts",
                                2,
                            )
                            or 1
                        ),
                    ),
                    "formal_state_search_provider_retry_backoff_s": max(
                        0.0,
                        float(
                            getattr(
                                args,
                                "formal_state_search_provider_retry_backoff_s",
                                5.0,
                            )
                            or 0.0
                        ),
                    ),
                    "formal_state_search_beam_width": max(
                        1,
                        int(
                            getattr(args, "formal_state_search_beam_width", 4)
                            or 1
                        ),
                    ),
                    "formal_state_search_max_steps": max(
                        1,
                        int(
                            getattr(args, "formal_state_search_max_steps", 8)
                            or 1
                        ),
                    ),
                    "formal_state_search_max_candidates": max(
                        1,
                        int(
                            getattr(args, "formal_state_search_max_candidates", 6)
                            or 1
                        ),
                    ),
                    "formal_state_search_backtrack_limit": max(
                        0,
                        int(
                            getattr(args, "formal_state_search_backtrack_limit", 8)
                            or 0
                        ),
                    ),
                    "formal_state_search_max_no_improvement_quanta": max(
                        0,
                        int(
                            getattr(
                                args,
                                "formal_state_search_max_no_improvement_quanta",
                                6,
                            )
                            or 0
                        ),
                    ),
                    "falsification_enabled": bool(
                        getattr(args, "mini_falsification", True)
                    ),
                    "falsification_max_checks": falsification_max_checks,
                    "falsification_operation_timeout_s": (
                        falsification_operation_timeout_s
                    ),
                    "falsification_engine_timeout_s": (
                        falsification_engine_timeout_s
                    ),
                    "proof_state_cache_enabled": bool(
                        getattr(args, "proof_state_cache", True)
                    ),
                    "proof_state_cache_path": str(
                        getattr(args, "proof_state_cache_path", "") or ""
                    ),
                    "root_tactic_prepass_enabled": bool(
                        getattr(args, "root_tactic_prepass", False)
                    ),
                    "root_tactic_timeout_s": max(
                        0.0,
                        float(
                            getattr(args, "root_tactic_timeout_s", 40.0)
                            or 0.0
                        ),
                    ),
                    "root_tactic_max_candidates": max(
                        0,
                        int(
                            getattr(args, "root_tactic_max_candidates", 64)
                            or 0
                        ),
                    ),
                    "startup_root_fast_lane_enabled": bool(
                        getattr(args, "startup_root_fast_lane", False)
                    ),
                    "startup_root_fast_lane_tactic_timeout_s": float(
                        getattr(
                            args,
                            "startup_root_fast_lane_tactic_timeout_s",
                            300.0,
                        )
                        or 0.0
                    ),
                    "startup_root_fast_lane_tactic_max_candidates": int(
                        getattr(
                            args,
                            "startup_root_fast_lane_tactic_max_candidates",
                            12,
                        )
                        or 0
                    ),
                    "mini_recursive_enabled": bool(
                        getattr(args, "mini_recursive", True)
                    ),
                    "adaptive_recursive_on_stall": bool(
                        getattr(args, "adaptive_recursive_on_stall", True)
                    ),
                    "mini_recursive_passes": max(
                        1, int(getattr(args, "mini_recursive_passes", 6) or 6)
                    ),
                    "mini_recursive_max_claims": max(
                        1,
                        int(
                            getattr(
                                args,
                                "mini_recursive_claims",
                                PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
                            )
                            or PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS
                        ),
                    ),
                    "mini_recursive_claims_configured": max(
                        1,
                        int(
                            getattr(
                                args,
                                "mini_recursive_claims",
                                PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
                            )
                            or PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS
                        ),
                    ),
                    "mini_recursive_claims": max(
                        1,
                        int(
                            getattr(
                                args,
                                "mini_recursive_claims",
                                PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS,
                            )
                            or PRODUCTION_MINI_RECURSIVE_MAX_CLAIMS
                        ),
                    ),
                    "mini_recursive_turns_per_claim": max(
                        1,
                        int(
                            getattr(
                                args,
                                "mini_recursive_turns_per_claim",
                                6,
                            )
                            or 6
                        ),
                    ),
                    "mini_recursive_tactic_timeout_s": max(
                        1.0,
                        float(
                            getattr(
                                args,
                                "mini_recursive_tactic_timeout_s",
                                60.0,
                            )
                            or 60.0
                        ),
                    ),
                    "mini_recursive_tactic_max_candidates": max(
                        1,
                        int(
                            getattr(
                                args,
                                "mini_recursive_tactic_max_candidates",
                                48,
                            )
                            or 48
                        ),
                    ),
                    "lean_project_dir": args.lean_project_dir,
                    "lean_timeout_s": int(args.lean_timeout_s),
                    "proof_dossier": (
                        proof_dossier.to_record() if proof_dossier else None
                    ),
                    "proof_graph_summary": (
                        proof_dossier.proof_graph.summary()
                        if proof_dossier and proof_dossier.proof_graph
                        else None
                    ),
                    "mini_proof_graph_metrics": _mini_proof_graph_metric_record(
                        proof_dossier.proof_graph.summary()
                        if proof_dossier and proof_dossier.proof_graph
                        else None
                    ),
                    **_mini_proof_graph_metric_record(
                        proof_dossier.proof_graph.summary()
                        if proof_dossier and proof_dossier.proof_graph
                        else None
                    ),
                    "proof_state_summary": (
                        getattr(proof_dossier, "proof_state_record", None)
                        if proof_dossier
                        else None
                    ),
                    "proof_state_metrics": (
                        (
                            getattr(proof_dossier, "proof_state_record", {}) or {}
                        ).get("metrics")
                        if proof_dossier
                        else None
                    ),
                    **_mini_proof_state_metric_record(
                        getattr(proof_dossier, "proof_state_record", None)
                        if proof_dossier
                        else None
                    ),
                    **_mini_dossier_structural_metric_record(proof_dossier),
                    **_mini_solved_export_status("not_attempted"),
                    "mini_solved_export_downgrades_solved": 0,
                }
                # MP-FU-009: join child work (Lean subprocess trees, detached
                # deadline tasks, theory workers) BEFORE the terminal summary
                # is written and the event stream closes. The report is part
                # of that terminal record; failure here must never block the
                # summary itself.
                try:
                    cancellation_barrier_report = await _run_cancellation_barrier(
                        lean=lean,
                        theory_library=theory_library,
                    )
                    summary_payload["cancellation_barrier"] = (
                        cancellation_barrier_report
                    )
                    lean_close_completed = bool(
                        cancellation_barrier_report.get("lean_closed")
                    )
                    theory_library_close_completed = bool(
                        cancellation_barrier_report.get("theory_closed")
                    )
                except Exception as barrier_exc:
                    summary_payload["cancellation_barrier"] = {
                        "barrier_ran": False,
                        "barrier_error": (
                            f"{type(barrier_exc).__name__}: {barrier_exc}"
                        ),
                    }
                recorder.write_summary(summary_payload)
                if (
                    ok
                    and os.environ.get("ENSEMBLE_MINI_DEFER_SOLVED_EXPORT") == "1"
                    and not early_staged_solution_written
                ):
                    try:
                        from .mini_session.process_watchdog import (
                            write_staged_solution_receipt,
                        )

                        write_staged_solution_receipt(
                            output_dir,
                            theorem_name=problem.theorem_name,
                            summary=summary_payload,
                        )
                    except Exception as receipt_exc:
                        print(
                            "Mini-session staged-proof receipt could not be "
                            f"written: {type(receipt_exc).__name__}: "
                            f"{receipt_exc}",
                            file=sys.stderr,
                        )
                if ok and os.environ.get("ENSEMBLE_MINI_DEFER_SOLVED_EXPORT") != "1":
                    export_status = _auto_export_solved_run(
                        output_dir,
                        lean_project_dir=Path(args.lean_project_dir),
                    )
                    summary_payload.update(export_status)
                    export_verified = _mini_solved_export_verified_payload(
                        export_status
                    )
                    summary_payload["pre_export_solved"] = pre_export_solved
                    summary_payload["session_root_finalized"] = pre_export_solved
                    summary_payload["solved_export_verified"] = export_verified
                    summary_payload["mini_solved_export_downgrades_solved"] = (
                        0 if export_verified else 1
                    )
                    if not export_verified:
                        ok = False
                        export_failure_state = _mini_solved_export_failure_reason(
                            export_status
                        )
                        export_failure_reason = f"solved_export_{export_failure_state}"
                        failure_reason = export_failure_reason
                        summary_payload["solved"] = False
                        summary_payload["failure_reason"] = export_failure_reason
                        if not summary_payload.get("failure_reason_detail"):
                            summary_payload["failure_reason_detail"] = str(
                                export_status.get(
                                    "mini_solved_export_diagnostic_preview",
                                    "",
                                )
                                or ""
                            )
                    else:
                        summary_payload["solved"] = True
                        summary_payload["failure_reason"] = None
                        summary_payload["failure_reason_detail"] = None
                    recorder.write_summary(summary_payload)
                print()
                print("=" * 64)
                if ok and os.environ.get("ENSEMBLE_MINI_DEFER_SOLVED_EXPORT") == "1":
                    print(f"ROOT FINALIZED, EXPORT PENDING: {problem.theorem_name}")
                    print("=" * 64)
                    print("Proof:")
                    print(proof)
                elif ok:
                    print(f"SOLVED: {problem.theorem_name}")
                    print("=" * 64)
                    print("Proof:")
                    print(proof)
                elif bool(summary_payload.get("disproved")):
                    print(f"DISPROVED: {problem.theorem_name}")
                    print("Lean verified an axiom-audited proof of the negation.")
                    print("=" * 64)
                elif infrastructure_aborted:
                    print(f"INFRASTRUCTURE ABORTED: {problem.theorem_name}")
                    print(
                        "The proof search did not reach a mathematical "
                        "solved/unsolved verdict."
                    )
                    if failure_reason:
                        print(f"Failure: {failure_reason}")
                    print("=" * 64)
                else:
                    print(f"NOT SOLVED: {problem.theorem_name}")
                    if (
                        pre_export_solved
                        and summary_payload.get("solved_export_verified") is not True
                    ):
                        print(
                            "Session root finalized, but solved export "
                            "verification did not pass: "
                            f"{summary_payload.get('mini_solved_export_status')}"
                        )
                    print("=" * 64)
                print(f"\nArtifacts: {output_dir}")
            finally:
                # ``recorder.close()`` MUST run even if write_summary fails,
                # otherwise stdout/stderr stay redirected and file handles leak.
                try:
                    await _supervised_sync_resource_close(
                        recorder.close,
                        label="mini_session_recorder_close",
                    )
                except Exception:
                    pass
        finally:
            # Release LLM HTTP connection pools even if summary writing fails.
            # ``OpenAICompatClient`` wraps an ``httpx.AsyncClient`` whose
            # connection pool is held open until ``close()``/``aclose()`` is
            # awaited. For one-shot CLI use the process exit reaps everything,
            # but programmatic callers that invoke ``_main_async`` repeatedly
            # would accumulate pools (and eventually file descriptors)
            # without these awaits. Per-client try/except so a stuck close on
            # one client doesn't prevent the other from closing.
            if (
                prover_client is not None
                and id(prover_client) not in llm_client_close_attempted_ids
            ):
                try:
                    await _supervised_resource_close(
                        prover_client.close(),
                        label="mini_session_prover_client_close",
                    )
                except Exception:
                    pass
            if (
                refiner_client is not None
                and refiner_client is not prover_client
                and id(refiner_client) not in llm_client_close_attempted_ids
            ):
                try:
                    await _supervised_resource_close(
                        refiner_client.close(),
                        label="mini_session_refiner_client_close",
                    )
                except Exception:
                    pass
            if (
                planner_escalation_client is not None
                and planner_escalation_client is not prover_client
                and planner_escalation_client is not refiner_client
                and id(planner_escalation_client)
                not in llm_client_close_attempted_ids
            ):
                try:
                    await _supervised_resource_close(
                        planner_escalation_client.close(),
                        label="mini_session_planner_escalation_client_close",
                    )
                except Exception:
                    pass
            # Release the LeanRunner's persistent verifier pool /
            # LeanREPL subprocess for the same programmatic-repeat-caller
            # reason that motivates the client cleanup above. CLI single-
            # run use is unaffected (process exit reaps everything), but
            # callers that invoke ``_main_async`` in a loop (sweep
            # drivers, in-process test harnesses) would otherwise
            # accumulate ``lake env lean`` child processes and file
            # descriptors. ``orchestrator.py`` already mirrors this
            # pattern.
            if lean is not None and not lean_close_completed:
                try:
                    await _supervised_resource_close(
                        lean.aclose(),
                        label="mini_session_lean_close",
                    )
                except Exception:
                    pass
            if theory_library is not None and not theory_library_close_completed:
                try:
                    await _supervised_sync_resource_close(
                        theory_library.close,
                        label="mini_session_theory_library_close",
                    )
                except Exception:
                    pass

    _uninstall_cooperative_stop()
    if pending_reraise is not None and not (
        cooperative_stop_signals
        and isinstance(pending_reraise, asyncio.CancelledError)
    ):
        from .mini_session.process_watchdog import is_watchdog_worker

        if not is_watchdog_worker():
            raise pending_reraise
    if cooperative_stop_signals and not ok:
        # Manual stop: conventional interrupt exit code so drivers can
        # distinguish a user stop from an ordinary unsolved run. This MUST
        return 130
    if pending_reraise is not None:
        raise pending_reraise
    return 0 if ok else 1


def _configure_pre_worker_retrieval_overlay(
    library: Any,
    output_dir: Path,
    *,
    expected_nonce: str,
) -> bool:
    """Load an exact fresh-store partition, or retain normal full retrieval."""

    sidecar = Path(output_dir) / "theory_promotion_maintenance.json"
    try:
        payload = json.loads(sidecar.read_text(encoding="utf-8"))
        promotion = dict(
            dict(payload).get("mini_theory_promotion", {}) or {}
        )
        if (
            re.fullmatch(r"[0-9a-f]{32}", str(expected_nonce or "")) is None
            or promotion.get("startup_overlay_nonce") != expected_nonce
            or promotion.get("maintenance_owner") != "pre_worker_supervisor"
            or promotion.get("environment_key")
            != str(library.environment_key)
        ):
            return False
        baseline_ids = frozenset(
            str(item or "").strip()
            for item in promotion.get("retrieval_baseline_bundle_ids", ())
            if str(item or "").strip()
        )
        recovered_ids = frozenset(
            str(item or "").strip()
            for item in promotion.get("recovered_bundle_ids", ())
            if str(item or "").strip()
        )
        current_ids = frozenset(
            str(getattr(bundle, "bundle_id", "") or "")
            for bundle in library.store.iter_bundles()
            if str(getattr(bundle, "bundle_id", "") or "")
        )
        # Sidecar persistence is advisory and can fail while leaving an older
        # file behind.  The nonce binds this snapshot to the exact worker
        # launch, while subset validation allows legitimate publications by a
        # concurrent run after the snapshot.  Those additions get their own
        # independently scored lane below instead of disabling the protected
        # baseline/recovery partition or being hidden from this invocation.
        if (
            baseline_ids.intersection(recovered_ids)
            or not baseline_ids.union(recovered_ids).issubset(current_ids)
        ):
            return False
        library.pre_worker_retrieval_baseline_bundle_ids = baseline_ids
        library.pre_worker_recovered_bundle_ids = recovered_ids
        library.pre_worker_concurrent_bundle_ids = current_ids.difference(
            baseline_ids,
            recovered_ids,
        )
        return True
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        return False


def _write_theory_promotion_maintenance_sidecar(
    output_dir: Path,
    promotion: Mapping[str, Any],
) -> bool:
    """Durably replace the advisory maintenance handoff."""

    output_dir = Path(output_dir)
    summary_path = output_dir / "summary.json"
    sidecar_path = output_dir / "theory_promotion_maintenance.json"
    temporary: Optional[Path] = None
    try:
        summary_sha256 = (
            hashlib.sha256(summary_path.read_bytes()).hexdigest()
            if summary_path.is_file()
            else ""
        )
        sidecar = {
            "schema_version": 1,
            "summary_sha256": summary_sha256,
            "mini_theory_promotion": dict(promotion),
        }
        temporary = sidecar_path.with_name(
            f".{sidecar_path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
        )
        with temporary.open("x", encoding="utf-8") as handle:
            handle.write(
                json.dumps(sidecar, indent=2, sort_keys=True, allow_nan=False)
                + "\n"
            )
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, sidecar_path)
        descriptor = os.open(
            sidecar_path.parent,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        return True
    except (OSError, TypeError, ValueError, OverflowError):
        if temporary is not None:
            try:
                temporary.unlink()
            except OSError:
                pass
        return False


def _run_supervised_theory_promotion_maintenance(
    output_dir: Path,
    *,
    args: argparse.Namespace,
    max_entries: int = 8,
    wall_budget_s: Optional[float] = None,
    maintenance_owner: str = "post_worker_supervisor",
    source_theorems: Sequence[str] = (),
    newest_first: bool = False,
    startup_overlay_nonce: str = "",
) -> None:
    """Drain durable receipts outside theorem search under an explicit budget.

    This maintenance cannot affect theorem search, winner selection, or the
    already-written proof outcome. Failure leaves receipts pending and never
    changes the worker/export return code.
    """

    requested = bool(
        getattr(args, "mini_theory_promote_verified_helpers", False)
    )
    if not requested or _effective_mini_theory_mode(args) != "build":
        return
    effective_wall_budget_s = (
        min(
            60.0,
            max(
                1.0,
                float(
                    getattr(
                        args,
                        "mini_theory_verifier_timeout_s",
                        60.0,
                    )
                    or 60.0
                ),
            ),
        )
        if wall_budget_s is None
        else max(0.1, float(wall_budget_s))
    )
    startup_cancellation_event: Optional[threading.Event] = None
    startup_timer: Optional[threading.Timer] = None
    if maintenance_owner == "pre_worker_supervisor":
        startup_cancellation_event = threading.Event()
        startup_timer = threading.Timer(
            effective_wall_budget_s,
            startup_cancellation_event.set,
        )
        startup_timer.daemon = True
        startup_timer.start()
    summary_path = Path(output_dir) / "summary.json"
    payload: Dict[str, Any] = {}
    safe_startup_overlay: Dict[str, Any] = {}
    try:
        loaded = json.loads(summary_path.read_text(encoding="utf-8"))
        if isinstance(loaded, dict):
            payload = loaded
    except (OSError, ValueError, json.JSONDecodeError):
        payload = {}
    library = None
    try:
        from .mini_theory import (
            MiniTheoryLibrary,
            run_verified_helper_promotion_maintenance,
        )
        from .mini_theory.promotion_outbox import PromotionOutbox

        theory_root = Path(
            str(
                getattr(
                    args,
                    "mini_theory_root",
                    Path.home() / ".cache" / "mini_prover" / "theory",
                )
            )
        ).expanduser()
        library = MiniTheoryLibrary(
            root=theory_root,
            lean_project_dir=Path(args.lean_project_dir),
            mode="build",
            attempt_scope_id=(
                "run_"
                + hashlib.sha256(
                    str(Path(output_dir).resolve()).encode(
                        "utf-8",
                        errors="replace",
                    )
                ).hexdigest()[:16]
            ),
            verifier_timeout_s=max(
                1.0,
                float(
                    getattr(args, "mini_theory_verifier_timeout_s", 180.0)
                    or 180.0
                ),
            ),
        )
        outbox = PromotionOutbox(library)
        baseline_ids: list[str] = []
        for bundle in library.store.iter_bundles():
            if (
                startup_cancellation_event is not None
                and startup_cancellation_event.is_set()
            ):
                return
            bundle_id = str(getattr(bundle, "bundle_id", "") or "")
            if bundle_id:
                baseline_ids.append(bundle_id)
        baseline_bundle_ids = tuple(sorted(baseline_ids))
        if maintenance_owner == "pre_worker_supervisor":
            # Persist the immutable baseline before promotion can mutate the
            # shared store.  If this write fails, skip recovery so the worker's
            # ordinary fallback observes the unchanged baseline.  If the
            # post-drain update later fails, this provisional receipt remains
            # valid and all additions are scored in the concurrent lane.
            safe_startup_overlay = {
                **dict(payload.get("mini_theory_promotion") or {}),
                "requested": True,
                "effective": True,
                "maintenance_owner": maintenance_owner,
                "environment_key": str(library.environment_key),
                "retrieval_baseline_bundle_ids": list(baseline_bundle_ids),
                "recovered_bundle_ids": [],
                "startup_overlay_nonce": str(startup_overlay_nonce or ""),
                "startup_overlay_phase": "baseline_persisted",
            }
            if not _write_theory_promotion_maintenance_sidecar(
                output_dir,
                safe_startup_overlay,
            ):
                return
        worker_owner_id = str(
            dict(payload.get("mini_theory_promotion") or {}).get(
                "receipt_owner_id", ""
            )
            or ""
        )
        preferred_owner_ids = tuple(
            dict.fromkeys(
                (
                    worker_owner_id,
                    *outbox.owner_ids_for_generated_run(
                        Path(output_dir).name,
                        cancellation_event=startup_cancellation_event,
                    ),
                )
            )
        )
        if (
            startup_cancellation_event is not None
            and startup_cancellation_event.is_set()
        ):
            return
        report = run_verified_helper_promotion_maintenance(
            library,
            max_entries=max(0, int(max_entries or 0)),
            wall_budget_s=effective_wall_budget_s,
            preferred_owner_ids=preferred_owner_ids,
            source_theorems=source_theorems,
            newest_first=newest_first,
            cancellation_event=startup_cancellation_event,
        )
        post_maintenance_bundle_ids: set[str] = set()
        for bundle in library.store.iter_bundles():
            if (
                startup_cancellation_event is not None
                and startup_cancellation_event.is_set()
            ):
                return
            bundle_id = str(getattr(bundle, "bundle_id", "") or "")
            if bundle_id:
                post_maintenance_bundle_ids.add(bundle_id)
        recovered_bundle_ids = tuple(
            sorted(post_maintenance_bundle_ids - set(baseline_bundle_ids))
        )
        promotion = {
            **dict(payload.get("mini_theory_promotion") or {}),
            **report.to_dict(),
            "requested": True,
            "effective": True,
            "maintenance_owner": maintenance_owner,
            "environment_key": str(library.environment_key),
        }
        if maintenance_owner == "pre_worker_supervisor":
            # Search this frozen baseline separately from the recovered
            # overlay so startup publication cannot displace a previously
            # reachable top result.
            promotion["retrieval_baseline_bundle_ids"] = list(
                baseline_bundle_ids
            )
            promotion["recovered_bundle_ids"] = list(recovered_bundle_ids)
            promotion["startup_overlay_nonce"] = str(
                startup_overlay_nonce or ""
            )
            promotion["startup_overlay_phase"] = "recovery_complete"
    except Exception as exc:
        promotion = {
            **dict(payload.get("mini_theory_promotion") or {}),
            **safe_startup_overlay,
            "requested": True,
            "effective": True,
            "maintenance_owner": maintenance_owner,
            "failures": int(
                dict(payload.get("mini_theory_promotion") or {}).get(
                    "failures", 0
                )
                or 0
            )
            + 1,
            "maintenance_error": f"{type(exc).__name__}: {exc}",
        }
    finally:
        if startup_timer is not None:
            startup_timer.cancel()
        if library is not None:
            try:
                library.close()
            except Exception:
                pass
    _write_theory_promotion_maintenance_sidecar(output_dir, promotion)


def _run_advisory_theory_promotion_maintenance(
    output_dir: Path,
    *,
    args: argparse.Namespace,
) -> None:
    """Keep post-outcome maintenance from changing an authoritative exit code."""

    try:
        _run_supervised_theory_promotion_maintenance(output_dir, args=args)
    except BaseException:
        # The worker/export outcome is already authoritative. Even an
        # interrupt here must leave that exit code intact; receipts remain
        # durable for bounded startup recovery by the next invocation.
        pass


def _complete_supervised_solved_export(
    output_dir: Path,
    *,
    lean_project_dir: Path,
) -> int:
    """Publish a solved export only after the worker exited cleanly."""

    from .activation_telemetry import (
        _strict_json_loads,
        build_activation_telemetry_for_run,
        compact_activation_summary,
        write_activation_telemetry_for_run,
    )

    summary_path = Path(output_dir) / "summary.json"
    temporary = summary_path.with_name(
        f".summary.supervisor.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )

    def encoded_summary(record: Mapping[str, Any]) -> str:
        return json.dumps(
            dict(record),
            indent=2,
            sort_keys=True,
            allow_nan=False,
        ) + "\n"

    def replace_summary(record: Mapping[str, Any]) -> None:
        temporary.write_text(encoded_summary(record), encoding="utf-8")
        os.replace(temporary, summary_path)

    try:
        payload = _strict_json_loads(summary_path.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("summary root must be an object")
    except Exception as exc:
        print(f"Mini-session worker produced no readable summary: {exc}", file=sys.stderr)
        return 1
    if not bool(payload.get("pre_export_solved")):
        if bool(payload.get("solved")):
            payload["solved"] = False
            payload["solved_export_verified"] = False
            payload["failure_reason"] = "solved_export_missing_pre_export_receipt"
            payload["failure_reason_detail"] = (
                "solved=true requires pre_export_solved=true before supervisor export"
            )
            try:
                replace_summary(payload)
            except (OSError, TypeError, ValueError, OverflowError):
                pass
        return 1

    # Establish a durable fail-closed state before any export or activation
    # publication can fail. The solved bit is committed only after a telemetry
    # artifact bound to the exact staged summary has been published.
    payload["solved"] = False
    # The export boundary is one mirrored receipt, not an independent string.
    # Updating only ``mini_solved_export_status`` leaves
    # ``solved_export_status`` and any previous failure counters contradictory;
    # the exporter then (correctly) refuses bootstrap before reconstruction.
    # Reinitialize the complete receipt atomically so both a first attempt and
    # a supervisor retry enter the same coherent fail-closed pending state.
    payload.update(
        _mini_solved_export_status("pending_supervisor_verification")
    )
    try:
        replace_summary(payload)
    except (OSError, TypeError, ValueError, OverflowError) as exc:
        print(
            f"Mini-session supervisor could not publish fail-closed summary: {exc}",
            file=sys.stderr,
        )
        return 1

    export_status = _auto_export_solved_run(
        output_dir,
        lean_project_dir=lean_project_dir,
    )
    payload.update(export_status)
    export_verified = _mini_solved_export_verified_payload(export_status)
    payload["solved_export_verified"] = export_verified
    payload["mini_solved_export_downgrades_solved"] = 0 if export_verified else 1
    if export_verified:
        payload["solved"] = True
        payload["failure_reason"] = None
        payload["failure_reason_detail"] = None
    else:
        payload["solved"] = False
        failure_state = _mini_solved_export_failure_reason(export_status)
        payload["failure_reason"] = f"solved_export_{failure_state}"
        if not payload.get("failure_reason_detail"):
            payload["failure_reason_detail"] = str(
                export_status.get("mini_solved_export_diagnostic_preview", "") or ""
            )

    try:
        activation = build_activation_telemetry_for_run(
            output_dir,
            summary=payload,
        )
        payload["activation_telemetry"] = compact_activation_summary(activation)
    except Exception as exc:
        payload["activation_telemetry"] = {
            "activation_schema_version": 1,
            "error": f"{type(exc).__name__}: {exc}",
        }
    staged_summary = summary_path.with_name(
        f".summary.solved.{os.getpid()}.{uuid.uuid4().hex}.staged"
    )
    try:
        staged_summary.write_text(encoded_summary(payload), encoding="utf-8")
        activation = write_activation_telemetry_for_run(
            output_dir,
            summary=payload,
            summary_source_path=staged_summary,
        )
        compact = compact_activation_summary(activation)
        if compact != payload["activation_telemetry"]:
            payload["activation_telemetry"] = compact
            staged_summary.write_text(encoded_summary(payload), encoding="utf-8")
            write_activation_telemetry_for_run(
                output_dir,
                summary=payload,
                summary_source_path=staged_summary,
            )
        os.replace(staged_summary, summary_path)
    except Exception as exc:
        payload["solved"] = False
        payload["failure_reason"] = "activation_telemetry_publication_failed"
        payload["failure_reason_detail"] = f"{type(exc).__name__}: {exc}"
        payload["activation_telemetry"] = {
            "activation_schema_version": 1,
            "error": payload["failure_reason_detail"],
        }
        try:
            replace_summary(payload)
        except (OSError, TypeError, ValueError, OverflowError):
            pass
        try:
            staged_summary.unlink()
        except OSError:
            pass
        return 1
    return 0 if export_verified else 1


def _write_asyncio_shutdown_diagnostics(output_dir: Path) -> None:
    """Record pending task locations before ``asyncio.run`` cancels them."""
    try:
        current = asyncio.current_task()
        pending = [
            task
            for task in asyncio.all_tasks()
            if task is not current and not task.done()
        ]
        records: List[Dict[str, Any]] = []
        for task in pending:
            frames = task.get_stack(limit=8)
            records.append(
                {
                    "name": task.get_name(),
                    "coroutine": getattr(
                        task.get_coro(),
                        "__qualname__",
                        type(task.get_coro()).__name__,
                    ),
                    "stack": [
                        {
                            "file": frame.f_code.co_filename,
                            "function": frame.f_code.co_name,
                            "line": frame.f_lineno,
                        }
                        for frame in frames
                    ],
                }
            )
        loop = asyncio.get_running_loop()
        executor = getattr(loop, "_default_executor", None)
        executor_threads: List[Dict[str, Any]] = []
        if executor is not None:
            current_frames = sys._current_frames()
            for thread in list(getattr(executor, "_threads", ()) or ()):
                frame = current_frames.get(thread.ident) if thread.ident else None
                stack: List[Dict[str, Any]] = []
                while frame is not None and len(stack) < 12:
                    stack.append(
                        {
                            "file": frame.f_code.co_filename,
                            "function": frame.f_code.co_name,
                            "line": frame.f_lineno,
                        }
                    )
                    frame = frame.f_back
                executor_threads.append(
                    {
                        "name": thread.name,
                        "ident": thread.ident,
                        "alive": thread.is_alive(),
                        "stack": stack,
                    }
                )
        work_queue = getattr(executor, "_work_queue", None)
        try:
            queued_executor_work = int(work_queue.qsize()) if work_queue else 0
        except Exception:
            queued_executor_work = -1
        payload = {
            "schema_version": 1,
            "captured_at": time.time(),
            "pending_task_count": len(records),
            "pending_tasks": records,
            "default_executor_present": executor is not None,
            "default_executor_thread_count": len(executor_threads),
            "default_executor_queued_work": queued_executor_work,
            "default_executor_threads": executor_threads,
        }
        destination = Path(output_dir) / "asyncio_shutdown_diagnostics.json"
        temporary = destination.with_name(
            f".{destination.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
        )
        temporary.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary, destination)
    except Exception:
        pass


def _shutdown_artifact_identity(
    path: Path,
) -> Optional[tuple[int, int, int, str]]:
    from .mini_session.process_watchdog import _artifact_identity

    return _artifact_identity(Path(path))


def main() -> int:
    parser = _build_argparser()
    args = parser.parse_args()
    from .mini_session.process_watchdog import (
        VERIFY_STAGED_SOLUTION_EXIT_CODE,
        begin_process_deadline,
        is_watchdog_worker,
        run_cli_worker_under_watchdog,
        worker_overall_deadline,
    )

    parallel_sample_count = max(
        1,
        int(getattr(args, "parallel_samples", 1) or 1),
    )
    if not is_watchdog_worker():
        worker_argv = list(sys.argv[1:])
        if parallel_sample_count > 1:
            # Parallel search remains cooperative inside one isolated worker,
            # while the ordinary parent watchdog now enforces overall,
            # startup, and post-result asyncio shutdown bounds. This does not
            # shorten any search budget: the shutdown lease begins only after
            # the proof run has already returned.
            print(
                "Parallel sampling: running "
                f"{parallel_sample_count} cooperative worker samples under "
                "the process watchdog.",
                flush=True,
            )
        supervised_problem = _resolve_cli_theorem_problem(args)
        supervised_theorem_name = supervised_problem.theorem_name
        if args.output_dir:
            supervised_output_dir = Path(args.output_dir).resolve()
        else:
            supervised_output_dir = _allocate_default_mini_run_dir(
                supervised_problem.artifact_slug
            )
            worker_argv.extend(["--output-dir", str(supervised_output_dir)])
        watchdog_options = {
            "overall_timeout_s": float(
                getattr(args, "mini_worker_timeout_s", 0.0) or 0.0
            ),
            "startup_timeout_s": float(
                getattr(args, "mini_worker_startup_timeout_s", 0.0) or 0.0
            ),
            "hard_operation_deadlines": bool(
                getattr(args, "mini_hard_operation_watchdog", False)
            ),
            "shutdown_timeout_s": float(
                getattr(args, "mini_worker_shutdown_timeout_s", 0.0) or 0.0
            ),
        }
        # Recover a small amount of provably abandoned backlog before search.
        # This is what makes receipts from an interrupted predecessor useful
        # even when every predecessor obeyed the immediate Ctrl-C contract.
        startup_overlay_nonce = uuid.uuid4().hex
        worker_argv.extend(
            [
                "--mini-theory-startup-overlay-nonce",
                startup_overlay_nonce,
            ]
        )
        try:
            _run_supervised_theory_promotion_maintenance(
                supervised_output_dir,
                args=args,
                max_entries=2,
                wall_budget_s=30.0,
                maintenance_owner="pre_worker_supervisor",
                source_theorems=(supervised_theorem_name,),
                newest_first=True,
                startup_overlay_nonce=startup_overlay_nonce,
            )
        except KeyboardInterrupt:
            return 130
        worker_rc = run_cli_worker_under_watchdog(
            worker_argv,
            output_dir=supervised_output_dir,
            theorem_name=supervised_theorem_name,
            **watchdog_options,
        )
        if worker_rc not in (0, VERIFY_STAGED_SOLUTION_EXIT_CODE):
            # 130 is the explicit user-stop contract. Receipts are already
            # durable; never answer Ctrl-C with minutes of Lean maintenance.
            if worker_rc == 1:
                _run_advisory_theory_promotion_maintenance(
                    supervised_output_dir,
                    args=args,
                )
            return worker_rc
        export_rc = _complete_supervised_solved_export(
            supervised_output_dir,
            lean_project_dir=Path(args.lean_project_dir),
        )
        _run_advisory_theory_promotion_maintenance(
            supervised_output_dir,
            args=args,
        )
        return export_rc

    lifecycle = begin_process_deadline(
        deadline_monotonic=worker_overall_deadline(),
        label="mini_session_worker_lifecycle",
    )
    shutdown_leases: List[Any] = []
    setattr(args, "_mini_shutdown_leases", shutdown_leases)
    shutdown_output_dir = (
        Path(args.output_dir) if getattr(args, "output_dir", None) else None
    )

    async def run_worker() -> int:
        worker_result: Optional[int] = None
        try:
            worker_result = await _main_async(args)
            return worker_result
        finally:
            if shutdown_output_dir is not None:
                _write_asyncio_shutdown_diagnostics(shutdown_output_dir)

    try:
        return asyncio.run(run_worker())
    finally:
        lifecycle.close()


if __name__ == "__main__":
    sys.exit(main())
