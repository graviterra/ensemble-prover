"""Run recording and live trace support for mini-prover runs."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional, Set

from .activation_telemetry import (
    build_activation_telemetry_for_run,
    compact_activation_summary,
    write_activation_telemetry_for_run,
)
from .llm_error_policy import (
    classify_llm_error_text,
    is_terminal_llm_failure_reason,
    llm_failure_scope,
)
from .llm_deadline import (
    llm_retry_deadline_fields,
    llm_retry_deadline_record_from_text,
)
from .mini_recursive_outcome import is_resumable_mini_recursive_yield
from .graph_execution_projection import GRAPH_PROJECTION_METRICS
from .tactic_attempt_telemetry import MONOTONIC_LEAN_ATTEMPT_METRICS


_MINI_GRAPH_RECURSIVE_DECOMPOSE_METRIC_KEYS = (
    "mini_session_graph_recursive_decompose_invocations",
    "mini_session_graph_recursive_decompose_obligations_proved",
    "mini_session_graph_recursive_decompose_recursion_cap_hit",
    "mini_session_graph_recursive_decompose_cycle_suppressed",
    "mini_session_graph_recursive_decompose_budget_exhausted",
    "mini_session_graph_recursive_decompose_too_small_skipped",
    "mini_session_graph_recursive_decompose_non_executable_skipped",
    "mini_session_graph_recursive_decompose_answer_unsafe_skipped",
    "mini_session_graph_recursive_decompose_untrusted_obligation_skipped",
    "mini_session_graph_recursive_decompose_invalidated_obligation_skipped",
    "mini_session_graph_recursive_decompose_root_equivalent_skipped",
    "mini_session_graph_recursive_decompose_advisory_helpers_suppressed",
    "mini_session_graph_recursive_decompose_helpers_propagated",
    "mini_session_graph_recursive_decompose_failures",
    "mini_session_graph_recursive_decompose_prior_failure_skipped",
    "mini_session_graph_recursive_decompose_helper_progress_skipped",
    "mini_session_graph_recursive_decompose_poisoned_route_work_skipped",
)

_MINI_TARGET_INTEGRITY_METRIC_KEYS = (
    "mini_session_target_integrity_signals",
    "mini_session_target_integrity_fake_contradiction_detected",
    "mini_session_target_integrity_unverified_refutation_detected",
    "mini_session_target_integrity_semantic_bridge_direction_detected",
    "mini_session_target_integrity_proof_state_repair_bypassed",
    "mini_session_target_integrity_local_repair_bypassed",
    "mini_session_target_integrity_adjudication_materialized",
    "mini_session_target_integrity_adjudication_progress_suppressed",
    "mini_session_target_integrity_no_proof_signals",
    "mini_session_target_integrity_no_proof_adjudication_materialized",
    "mini_session_target_integrity_repair_tickets_contaminated",
    "mini_session_target_integrity_repair_tickets_suppressed",
)

_MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS = (
    "mini_formal_state_search_invocations",
    "mini_formal_state_search_nodes_created",
    "mini_formal_state_search_nodes_expanded",
    "mini_formal_state_search_lean_checks",
    "mini_formal_state_search_backtracks",
    "mini_formal_state_search_value_estimates",
    "mini_formal_state_search_diversity_pruned",
    "mini_formal_state_search_bottlenecks",
    "mini_formal_state_search_root_unlocking_bottlenecks",
    "mini_formal_state_search_operation_timeouts",
    "mini_formal_state_search_infrastructure_failures",
    "mini_formal_state_search_completion_rejections",
    "mini_formal_state_search_solved",
    "mini_formal_state_search_candidates_found",
    "mini_formal_state_search_zero_yield_stalls",
    "mini_formal_state_search_acceptance_vetoes",
    "mini_formal_state_search_local_intent_checkpoints_coalesced",
    "mini_formal_state_search_local_receipt_checkpoints_coalesced",
    "mini_formal_state_search_local_receipt_batch_flushes",
    "mini_formal_state_search_provider_reservation_checkpoints_coalesced",
    "mini_accepted_proof_stubs",
    "mini_parallel_sample_proof_state_snapshots",
    "mini_parallel_sample_structural_snapshots",
    "mini_parallel_sample_structural_nodes_imported",
    "mini_parallel_sample_structural_nodes_coalesced",
    "mini_parallel_sample_structural_edges_imported",
    "mini_parallel_sample_structural_branch_frames_imported",
    "mini_parallel_sample_structural_conflicts",
    "mini_parallel_sample_failures",
    "mini_parallel_samples_zero_completed",
    "mini_parallel_late_sample_candidates_preserved",
    "mini_parallel_late_sample_successes_preserved",
    "mini_parallel_late_sample_abandoned",
    "mini_parallel_late_sample_grace_timeouts",
    "mini_adaptive_recursive_fallback_suppressed_terminal_failure",
    "mini_recursive_followup_suppressed_terminal_failure",
    "mini_prove_followup_suppressed_terminal_failure",
    "mini_refine_handoff_compactions",
    "mini_refine_handoff_compacted_messages",
    "mini_refine_handoff_compacted_chars",
    "mini_refine_handoff_compacted_tool_rounds",
    "mini_in_turn_tool_history_compactions",
    "mini_in_turn_tool_history_compacted_messages",
    "mini_in_turn_tool_history_compacted_chars",
    "mini_in_turn_tool_history_compacted_tool_rounds",
    "mini_provider_call_quantum_yields",
    "mini_apply_decl_tool_state_updates",
    "mini_apply_decl_tool_state_closures",
    "mini_compute_examples_calls",
    "mini_compute_examples_queries",
    "mini_compute_examples_successes",
    "mini_compute_examples_rejected",
    "mini_compute_examples_errors",
    "mini_try_skeleton_calls",
    "mini_try_skeleton_accepted",
    "mini_try_skeleton_rejected",
    "mini_try_skeleton_residual_goals",
    "mini_try_lean_partial_state_promotions",
    "mini_tool_semantic_diagnostic_progress",
    "mini_tool_semantic_no_progress_detected",
    "mini_tool_search_cadence_skips",
    "mini_final_no_tools_accepted_proof_fallbacks",
    "mini_final_no_tools_empty_outputs",
    "mini_final_no_tools_no_proof_artifacts",
    "mini_final_no_tools_provider_tool_calls_observed",
    "mini_final_no_tools_token_exhaustions",
    "mini_extra_main_salvaged_last_main_checked",
    "mini_format_policy_redirect_granted",
    "mini_policy_rejection_final_turn_no_retry",
    "mini_repair_self_check_durable_evidence_accepted",
    "mini_preamble_redeclarations_dropped",
    "mini_preamble_redeclaration_conflicts",
    "mini_lemma_cache_store_errors",
    "mini_lemma_cache_deadline_integrity_unrecoverable",
    "mini_lemma_cache_ingest_schema_migrated",
    "mini_lemma_cache_ingest_schema_rejected",
    "mini_lemma_cache_ingest_quality_rejected",
    "mini_lemma_cache_ingest_projection_rejected",
    "mini_lemma_cache_ingest_policy_rejected",
    "mini_lemma_cache_ingest_field_rejected",
    "mini_lemma_cache_ingest_owner_deduped",
    "mini_premise_retrieval_runs",
    "mini_mathematical_retrieval_runs",
    "mini_mathematical_retrieval_mathlib_hits",
    "mini_mathematical_retrieval_project_hits",
    "mini_mathematical_retrieval_theory_hits",
    "mini_mathematical_retrieval_helper_hits",
    "mini_mathematical_retrieval_inactive_hits",
    "mini_mathematical_retrieval_source_failures",
    "mini_mathematical_retrieval_bundle_activations",
    "mini_mathematical_retrieval_helper_rechecks",
    "mini_mathematical_retrieval_project_imports",
    "mini_mathematical_retrieval_module_imports",
    "mini_mathematical_retrieval_requests_total",
    "mini_mathematical_retrieval_latency_ms_total",
    "mini_mathematical_retrieval_deadline_truncations",
    "mini_mathematical_retrieval_stale_results",
    "mini_mathematical_retrieval_direct_requests",
    "mini_mathematical_retrieval_eager_requests",
    "mini_mathematical_retrieval_reactive_requests",
    "mini_mathematical_retrieval_proof_state_requests",
    "mini_mathematical_retrieval_repair_requests",
    "mini_mathematical_retrieval_capacity_exhaustions",
    "mini_mathematical_retrieval_all_mathlib_hits",
    "mini_mathematical_retrieval_all_project_hits",
    "mini_mathematical_retrieval_all_theory_hits",
    "mini_mathematical_retrieval_all_helper_hits",
    "mini_mathematical_retrieval_all_inactive_hits",
    "mini_mathematical_retrieval_all_source_failures",
    "mini_mathematical_retrieval_channel_mathlib_lexical_contributions",
    "mini_mathematical_retrieval_channel_project_hybrid_contributions",
    "mini_mathematical_retrieval_channel_published_theory_lexical_contributions",
    "mini_mathematical_retrieval_channel_verified_helper_local_contributions",
    "mini_mathematical_retrieval_channel_verified_helper_semantic_contributions",
    "mini_mathematical_retrieval_channel_type_shape_contributions",
    "mini_mathematical_retrieval_latency_le_10ms",
    "mini_mathematical_retrieval_latency_le_50ms",
    "mini_mathematical_retrieval_latency_le_100ms",
    "mini_mathematical_retrieval_latency_le_500ms",
    "mini_mathematical_retrieval_latency_le_1000ms",
    "mini_mathematical_retrieval_latency_gt_1000ms",
    "mini_premise_retrieval_zero_raw_hits",
    "mini_premise_retrieval_zero_filtered_hits",
    "mini_premise_retrieval_filtered_out_nonpremise_hits",
    "mini_premise_retrieval_precompute_failures",
    "mini_premise_zero_hit_shadow_local_micro_theory",
    "mini_premise_zero_hit_local_micro_theory_activated",
    "mini_premise_zero_hit_library_search_suppressed",
    "mini_premise_zero_hit_repair_retrieval_suppressed",
    "mini_premise_zero_hit_proof_state_retrieval_suppressed",
    "mini_premise_zero_hit_local_micro_theory_unlocked",
    "mini_search_pre_retrieved_duplicates_suppressed",
    "mini_search_local_decl_queries_suppressed",
    "mini_hollow_root_reducers_detected",
    "mini_hollow_root_reducers_reenabled_by_premise",
    "mini_negative_evidence_helpers_withheld",
    "mini_graph_hollow_reducer_certificates_blocked",
    "mini_graph_negative_evidence_certificates_blocked",
    "mini_graph_negative_evidence_exact_certificates_accepted",
    "mini_graph_negative_evidence_contradicted_targets",
    "mini_graph_negative_evidence_contradicted_routes",
    "mini_graph_root_equivalent_claims_suppressed",
    "mini_verified_helper_statement_aliases_recorded",
    "mini_verified_root_equivalent_helpers_withheld",
    "mini_session_theory_lemmas_accepted",
    "mini_session_parent_progress_edges",
    "mini_session_parent_progress_obligations_proved",
    "mini_session_strong_progress_outcomes",
    "mini_session_soft_progress_outcomes",
    "mini_session_helper_progress_soft_alias",
    "mini_session_helper_progress_soft_weak_theory",
    "mini_session_progress_invariant_false_strong_weak_helper",
    "mini_session_progress_invariant_parent_progress_undercredited",
    "mini_proposed_helpers_rejected_malformed_statement",
    "mini_proposed_helpers_rejected_non_theorem_statement",
    "mini_verified_helpers_rejected_malformed_statement",
    "mini_verified_helpers_rejected_non_theorem_statement",
    "mini_session_assemble_route_conversation_rejected",
    "mini_session_assemble_route_static_conversation_suppressed",
    "mini_session_unscoped_root_authoring_suppressed",
    "mini_session_ready_root_route_drain_selected",
    "mini_session_ready_root_route_drain_budget_blocked",
    "mini_session_ready_root_route_drain_not_applicable",
    "mini_session_ready_root_route_drain_headroom_granted",
    "mini_session_graph_route_no_replayable_helpers",
    "mini_session_graph_route_contract_blocked",
    "mini_session_graph_route_missing_assembly_bridge",
    "mini_session_graph_route_authoring_missing_bridge_suppressed",
    "mini_session_graph_route_cases_synthesized",
    "mini_session_graph_route_cases_solved",
    "mini_session_graph_route_cases_failed",
    "mini_session_graph_route_root_tactic_continued",
    "mini_session_graph_obligations_promoted_to_child_goals",
    "mini_session_graph_obligations_reused_proof_state_child_goals",
    "mini_root_assembly_contract_blocked",
    "mini_session_repair_tickets_created",
    "mini_session_repair_tickets_queued",
    "mini_session_repair_tickets_promoted",
    "mini_session_repair_tickets_selected",
    "mini_session_repair_tickets_resolved",
    "mini_session_repair_tickets_exhausted",
    "mini_session_repair_tickets_retry_remaining",
    "mini_session_repair_tickets_unresolved_attempts_consumed",
    "mini_session_repair_tickets_unresolved_exhausted",
    "mini_session_repair_tickets_policy_retries_remaining",
    "mini_session_repair_ticket_policy_continuations",
    "mini_session_repair_tickets_scheduler_blocked",
    "mini_session_repair_tickets_policy_rejections_consumed",
    "mini_session_repair_tickets_policy_narrowing_required",
    "mini_session_repair_tickets_unserviceable_route_replan",
    "mini_session_repair_failure_observations",
    "mini_session_repair_targets_retired_repeated_failure",
    "mini_session_repair_tickets_suppressed_repeated_failure",
    "mini_session_repair_retirement_decomposition_materialized",
    "mini_session_graph_policy_failures_observed",
    "mini_session_graph_policy_targets_retired",
    "mini_session_repair_ticket_blocked_no_action",
    "mini_session_repair_policy_narrowing_blocked",
    "mini_session_repair_policy_scope_materializations",
    "mini_session_repair_policy_narrowing_no_recovery",
    "mini_session_repair_policy_child_adaptive_fallback_yields",
    "mini_session_repair_policy_frontier_selected",
    "mini_session_repair_policy_narrowing_retained_after_no_progress",
    "mini_session_root_authoring_yielded_to_scoped_frontier",
    "mini_session_retired_graph_target_restore_suppressed",
    "mini_session_retired_graph_target_repair_ticket_suppressed",
    "mini_session_retired_graph_target_repair_policy_suppressed",
    "mini_session_retired_graph_target_local_repair_suppressed",
    "mini_session_retired_graph_target_policy_redirect_suppressed",
    "mini_session_retired_graph_target_formalization_suppressed",
    "mini_session_retired_graph_target_frontier_suppressed",
    "mini_session_promoted_graph_target_restore_suppressed",
    "mini_session_terminal_graph_target_repair_bypassed",
    "mini_session_terminal_graph_target_retained_for_bounded_repair",
    "mini_session_terminal_graph_target_repair_ticket_bypassed",
    "mini_session_terminal_graph_target_local_repair_bypassed",
    "mini_session_terminal_graph_target_suppressed_by_reason",
    "mini_session_terminal_graph_target_repair_bypass_deduped",
    "mini_session_graph_formalization_bridge_rejected",
    "mini_session_graph_formalization_negative_bridge_support_rejected",
    "mini_session_graph_formalization_bridge_support_recorded",
    "mini_session_graph_formalization_route_support_helpers_hidden",
    "mini_session_graph_formalization_bridge_parent_assembly_required",
    "mini_session_graph_formalization_bridge_parent_work_materialized",
    "mini_session_graph_formalization_bridge_parent_work_missing",
    "mini_session_graph_formalization_bridge_parent_assembly_scheduled",
    "mini_session_graph_formalization_bridge_support_reselected_without_parent_work",
    "mini_session_graph_formalization_repeated_bridge_suppressed",
    "mini_session_graph_formalization_duplicate_obligations_suppressed",
    "mini_session_graph_formalization_rejected_helpers_banked_proposed",
    "mini_session_formalization_helper_declaration_rejected",
    "mini_session_formalization_requires_declaration",
    "lean_error_type_formalization_requires_declaration",
    "lean_error_type_formalization_helper_declaration_rejected",
    "mini_session_proof_only_helper_support_materialized",
    "mini_session_proof_only_helper_support_rejected",
    "mini_session_materialization_pending_reselected_same_action",
    "mini_session_materialization_pending_escalated",
    "mini_session_materialization_pending_recoveries",
    "mini_session_materialization_pending_suppressors_released",
    "mini_session_repair_policy_narrowing_reselected_same_work",
    "mini_session_repair_policy_narrowing_materialization_escalated",
    "mini_session_same_target_decl_proofs_graph_formalization_routed",
    "mini_session_same_target_decl_proofs_graph_formalization_accepted",
    "mini_session_same_target_decl_proofs_graph_formalization_bridge_support_recorded",
    "mini_session_same_target_decl_proofs_graph_formalization_rejected",
    "mini_session_same_target_decl_proofs_graph_formalization_dependencies_banked",
    "mini_session_same_target_decl_proofs_graph_formalization_dependency_rejected",
    "mini_session_proof_turn_decl_graph_formalization_routed",
    "mini_session_proof_turn_decl_graph_formalization_accepted",
    "mini_session_proof_turn_decl_graph_formalization_bridge_support_recorded",
    "mini_session_proof_turn_decl_graph_formalization_rejected",
    "mini_session_proof_turn_decl_graph_formalization_dependencies_banked",
    "mini_session_proof_turn_decl_graph_formalization_dependency_rejected",
    "mini_session_graph_native_statement_type_rejected",
    "mini_session_unknown_identifier_api_search_required",
    "mini_session_unknown_identifier_api_search_policy_rejections",
    "mini_session_parse_errors_code_generation_failures",
    "mini_session_cost_governed_continuations",
    "mini_session_cost_governed_budget_granted",
    "mini_session_cost_governed_repair_policy_released",
    "mini_session_cost_governed_forced_static_conversation",
    "mini_session_cost_governed_static_no_serviceable_work_suppressed",
    "mini_session_cost_governed_no_dispatch_lane",
    "mini_session_cost_governed_no_cost_capacity",
    "mini_session_cost_governed_lean_infra_deferred",
    "mini_session_model_call_deferred_frontier_actions",
    "mini_session_model_call_deferred_frontier_retry_releases",
    "mini_session_model_call_deferred_static_retry_releases",
    "mini_session_cast_normalization_applicable",
    "mini_session_cast_normalization_attempts",
    "mini_session_cast_normalization_nat_sub_guards_attempted",
    "mini_session_cast_normalization_choose_rewrites_attempted",
    "mini_session_cast_normalization_side_conditions_exposed",
    "mini_session_cast_normalization_side_conditions_materialized",
    "mini_session_cast_normalization_solved",
    "mini_session_cast_normalization_failed",
    "mini_session_finset_reindexing_applicable",
    "mini_session_finset_reindexing_attempts",
    "mini_session_finset_reindexing_sum_goals_attempted",
    "mini_session_finset_reindexing_product_goals_attempted",
    "mini_session_finset_reindexing_filter_rewrites_attempted",
    "mini_session_finset_reindexing_antidiagonal_rewrites_attempted",
    "mini_session_finset_reindexing_side_conditions_exposed",
    "mini_session_finset_reindexing_side_conditions_materialized",
    "mini_session_finset_reindexing_solved",
    "mini_session_finset_reindexing_failed",
    "mini_session_soft_progress_streak_saturated",
    *_MINI_TARGET_INTEGRITY_METRIC_KEYS,
    "mini_session_llm_call_failures",
    "mini_session_llm_retry_deadline_exhausted",
    "mini_session_llm_retry_deadline_guard_failures",
    "mini_session_llm_retry_deadline_http_status_failures",
    "mini_session_llm_retry_deadline_timeout_failures",
    "mini_session_llm_retry_deadline_transport_failures",
    "mini_session_llm_scoped_failures",
    "mini_session_llm_retry_deadline_scoped_failures",
    "mini_session_terminal_llm_failures",
    "mini_session_terminal_llm_insufficient_quota",
    "mini_session_no_proof_giveup_extractable_helpers_recovered",
    "mini_recursive_bottleneck_obligations_materialized",
    "mini_recursive_bottleneck_obligations_pending_adjudication",
    "mini_recursive_failed_claim_obligations_pending_adjudication",
    "mini_recursive_planner_scoped_failures",
    "mini_recursive_child_scoped_failures",
    "mini_recursive_false_parent_routes_poisoned",
    "mini_recursive_false_parent_dependency_work_suppressed",
    "mini_recursive_invalidated_parent_events_suppressed",
    "mini_recursive_root_equivalent_claim_variants_suppressed",
    "mini_recursive_durable_root_short_circuits",
    "mini_recursive_root_equivalent_helper_candidates",
    "mini_recursive_root_equivalent_helper_promotions",
    "mini_recursive_root_equivalent_helper_promotion_failures",
    "mini_recursive_llm_root_close_attempts",
    "mini_recursive_llm_root_close_solved",
    "mini_recursive_plans_unmet_assembly_bridge_rejected",
    "mini_recursive_plans_unmet_assembly_bridge_all_filtered",
    "mini_recursive_plans_unmet_assembly_bridge_recovery_passes_granted",
    "mini_recursive_plans_root_route_disconnected_after_filters",
    "mini_recursive_plans_missing_root_terminal",
    "mini_recursive_route_contracts_missing_root_terminal_rejected",
    "mini_recursive_dependency_contract_claims_suspended",
    "mini_recursive_dependency_contract_claims_rehydrated",
    "mini_recursive_max_claims",
    "mini_recursive_claims_configured",
    "mini_session_unscoped_root_repair_replans",
    "mini_session_unscoped_root_repair_structured_obligations",
    "mini_session_unscoped_root_repair_tickets_scope_redirected",
    "mini_session_unscoped_root_repair_new_tickets_suppressed",
    "mini_session_unscoped_root_repair_tickets_preempted_by_fallback",
    "mini_session_unscoped_root_repair_tickets_yielded_to_static_prepass",
    "mini_session_scoped_repair_tickets_retained_after_fallback",
    "mini_session_unselected_root_policy_misses_scope_redirected",
    "mini_session_local_root_repair_quota_suppressed",
    "mini_session_local_root_repair_quota_preempted_by_fallback",
    "mini_session_local_repair_quota_scoped_action_selected",
    "mini_session_route_replan_unserviceable_skipped",
    "mini_session_route_scoped_advisory_helpers_suppressed",
    "mini_session_failure_residual_obligations_quarantined_unscheduled",
    "mini_session_schedulable_decompositions_created",
    "mini_session_quarantined_residual_diagnostics_created",
    "mini_root_finalization_candidates",
    "mini_root_finalization_accepted",
    "mini_root_finalization_blocked",
    "mini_problem_root_finalization_accepted",
    "mini_problem_root_finalization_blocked",
    "mini_subgoal_root_finalization_accepted",
    "mini_subgoal_root_finalization_blocked",
    "mini_root_finalization_support_mismatch",
    "mini_root_finalization_route_contract_not_ready",
    "mini_root_finalization_missing_certificate",
    "mini_root_finalization_target_mismatch",
    "mini_root_finalization_certificate_rejected",
    "mini_root_finalization_certificate_accepted",
    "mini_root_finalization_bypass_blocked",
    "mini_root_certificate_created",
    "mini_root_certificate_helper_closure_expanded",
    "mini_solved_export_attempts",
    "mini_solved_export_successes",
    "mini_solved_export_skipped",
    "mini_solved_export_kernel_rejected",
    "mini_solved_export_exceptions",
    "mini_solved_export_verified",
    "mini_solved_export_downgrades_solved",
    "mini_session_graph_route_authoring_requested",
    "mini_session_graph_route_authoring_failed",
    "mini_branching_advisory_helpers_suppressed",
    "deepseek_final_raw_no_tools",
    "deepseek_dsml_content_tool_call",
    "deepseek_dsml_try_lean_salvaged",
    "deepseek_dsml_tool_after_budget",
    "deepseek_text_content_tool_call",
    "deepseek_text_try_lean_salvaged",
    "deepseek_text_tool_after_budget",
    *_MINI_GRAPH_RECURSIVE_DECOMPOSE_METRIC_KEYS,
    *sorted(MONOTONIC_LEAN_ATTEMPT_METRICS),
    *GRAPH_PROJECTION_METRICS,
)

_LLM_USAGE_BASE_KEYS = {
    "input_tokens",
    "output_tokens",
    "cached_input_tokens",
    "cache_write_tokens",
    "prompt_cache_miss_tokens",
    "reasoning_output_tokens",
    "usage_missing_responses",
    "cost_accounting_incomplete",
    "cost_usd",
    "estimated_unknown_cost_usd",
    "llm_budget_accounted_cost_usd",
    "llm_budget_committed_cost_usd",
    "llm_budget_reserved_cost_usd",
    "max_cost_usd",
    "llm_budget_remaining_usd",
    "llm_budget_unspent_usd",
    "llm_cost_budget_enabled",
    "llm_cost_budget_exhausted",
    "llm_cost_budget_terminal_reason",
    "llm_usage_events",
    "llm_calls",
    "llm_usage_missing_events",
    "llm_pricing_unknown_events",
    "llm_cancelled_provider_inflight_events",
    "llm_cancelled_provider_inflight_estimated_cost_usd",
    "llm_retryable_exception_no_charge_events",
    "llm_openrouter_affordability_retries",
    "llm_budget_reservations",
    "llm_budget_rejections",
    "llm_cost_budget_reserve_output_tokens",
    "llm_temperature_requests",
    "llm_temperature_effective_calls",
    "llm_temperature_provider_dropped",
    "llm_temperature_by_phase",
}
_LLM_USAGE_ROLE_SUFFIXES = {
    "input_tokens",
    "output_tokens",
    "cached_input_tokens",
    "cache_write_tokens",
    "prompt_cache_miss_tokens",
    "reasoning_output_tokens",
    "usage_missing_responses",
    "cost_usd",
    "estimated_unknown_cost_usd",
    "model",
}


def _is_llm_usage_summary_key(key: str) -> bool:
    if key in _LLM_USAGE_BASE_KEYS:
        return True
    return any(
        key.endswith(f"_{suffix}") for suffix in _LLM_USAGE_ROLE_SUFFIXES
    )


def _canonical_llm_usage_role(role: str) -> str:
    text = str(role or "").strip()
    return {
        "prove": "prover",
        "refine": "refiner",
    }.get(text, text)


class _TeeStream:
    """File-like wrapper that writes to two streams (e.g. stdout + a log file)."""

    def __init__(self, *streams: Any) -> None:
        self._streams = streams
        self._write_warning_emitted = False

    def write(self, data: str) -> int:
        first_error: Optional[Exception] = None
        successful_streams: List[Any] = []
        for s in self._streams:
            try:
                s.write(data)
                successful_streams.append(s)
            except Exception as exc:
                if first_error is None:
                    first_error = exc
        if first_error is not None and not self._write_warning_emitted:
            self._write_warning_emitted = True
            warning = (
                "[tee stream warning] failed to write to one run-log stream: "
                f"{type(first_error).__name__}: {first_error}\n"
            )
            for s in successful_streams:
                try:
                    s.write(warning)
                except Exception:
                    pass
        if not successful_streams and first_error is not None:
            raise first_error
        return len(data)

    def flush(self) -> None:
        first_error: Optional[Exception] = None
        flushed = False
        for s in self._streams:
            try:
                s.flush()
                flushed = True
            except Exception as exc:
                if first_error is None:
                    first_error = exc
        if not flushed and first_error is not None:
            raise first_error


_LIVE_TRACE_MODES = {"compact", "full", "jsonl", "off"}


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    except BaseException:
        # Descriptor cleanup must not replace an fsync failure or an external
        # stop with a secondary close error.
        try:
            os.close(descriptor)
        except BaseException:
            pass
        raise
    else:
        os.close(descriptor)


def _write_json_atomic(path: Path, payload: Dict[str, Any]) -> None:
    """Durably replace one JSON object without exposing a partial summary."""

    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    try:
        with temporary.open("x", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, ensure_ascii=False)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    except BaseException:
        # Preserve the primary write/replace/fsync failure. A stale temporary
        # is recoverable; losing the actual stop reason is not.
        try:
            temporary.unlink()
        except BaseException:
            pass
        raise


class RunRecorder:
    """Owns ``run.log`` (tee'd console) and ``turns.jsonl`` (structured trace).

    The recorder is process-global because the conversational loop calls
    ``print()`` everywhere; we redirect ``sys.stdout``/``sys.stderr`` at
    construction so existing prints automatically tee to the log file
    without any further plumbing.
    """

    _POLICY_METRIC_ERROR_TYPES: Set[str] = {
        "repair_self_check_missing",
        "repair_self_check_no_try_lean_call",
        "repair_self_check_tool_budget_exhausted",
        "repair_self_check_mismatch",
        "repair_self_check_terminal_continuation",
        "repair_gate_error",
        "proof_patch_failed",
        "reused_rejected_lean_fragment",
        # Round-3 fix: narrow-gate hits had no metric counter, so
        # telemetry-driven failure-mode dashboards silently
        # under-counted this rejection class.
        "transient_goal_target_sorry_helper",
        "repair_requires_api_search",
        "formalization_requires_declaration",
        "formalization_helper_declaration_rejected",
    }
    _MINI_SESSION_VERDICT_METRICS: Dict[str, str] = {
        "solved": "mini_session_verdict_solved",
        "lean_rejected": "mini_session_verdict_lean_rejected",
        "lean_infra_error": "mini_session_verdict_lean_infra_error",
        "no_proof_extracted": "mini_session_verdict_no_proof_extracted",
        "known_answer_no_construction_collapse": (
            "mini_session_verdict_known_answer_no_construction_collapse"
        ),
        "proof_policy_rejected": "mini_session_verdict_proof_policy_rejected",
        "proof_policy_repair_redirect": (
            "mini_session_verdict_proof_policy_repair_redirect"
        ),
        "helpers_accepted": "mini_session_verdict_helpers_accepted",
        "helpers_rejected": "mini_session_verdict_helpers_rejected",
        "lemma_dag_skipped_task_closed": (
            "mini_session_verdict_lemma_dag_skipped_task_closed"
        ),
        "lemma_dag_no_decomposition_task_opened": (
            "mini_session_verdict_lemma_dag_no_decomposition_task_opened"
        ),
        "solved_after_lemma_dag_helper": (
            "mini_session_verdict_solved_after_lemma_dag_helper"
        ),
        "solved_after_helper_only_salvage": (
            "mini_session_verdict_solved_after_helper_only_salvage"
        ),
        "solved_after_helper_salvage": (
            "mini_session_verdict_solved_after_helper_salvage"
        ),
        "tactic_solved": "mini_session_verdict_tactic_solved",
        "tactic_rejected": "mini_session_verdict_tactic_rejected",
        "solved_after_proof_state_child": (
            "mini_session_verdict_solved_after_proof_state_child"
        ),
        "llm_call_failed": "mini_session_verdict_llm_call_failed",
        "llm_call_retry": "mini_session_verdict_llm_call_retry",
    }

    def __init__(self, output_dir: Path) -> None:
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)
        log_path = self.output_dir / "run.log"
        turns_path = self.output_dir / "turns.jsonl"
        self._log_fp = log_path.open("w", encoding="utf-8")
        self._turns_fp = turns_path.open("w", encoding="utf-8")
        self._turns_hasher = hashlib.sha256()
        self._orig_stdout = sys.stdout
        self._orig_stderr = sys.stderr
        sys.stdout = _TeeStream(self._orig_stdout, self._log_fp)
        sys.stderr = _TeeStream(self._orig_stderr, self._log_fp)
        self.live_trace_mode = "compact"
        self.live_trace_response_chars: Optional[int] = 1600
        self.start_ts = time.time()
        self._last_elapsed_s = 0.0
        self.turn_count = 0
        # Provider recovery receipts can be redelivered within one live run.
        # Track their stable identities at the sink so metrics and trace rows
        # remain exactly-once without relying on persisted controller state.
        self._recovery_event_ids_seen: Set[str] = set()
        self.metrics: Dict[str, Any] = {
            "lean_error_type_repair_self_check_missing": 0,
            "lean_error_type_repair_self_check_no_try_lean_call": 0,
            "lean_error_type_repair_self_check_tool_budget_exhausted": 0,
            "lean_error_type_repair_self_check_mismatch": 0,
            "lean_error_type_repair_self_check_terminal_continuation": 0,
            "lean_error_type_repair_gate_error": 0,
            "lean_error_type_proof_patch_failed": 0,
            "lean_error_type_reused_rejected_lean_fragment": 0,
            "lean_error_type_transient_goal_target_sorry_helper": 0,
            "lean_error_type_repair_requires_api_search": 0,
            "lean_error_type_formalization_requires_declaration": 0,
            "lean_error_type_formalization_helper_declaration_rejected": 0,
            "mini_recursive_claim_type_checks": 0,
            "mini_recursive_claim_type_rejected": 0,
            "mini_recursive_claim_type_inconclusive": 0,
            "mini_recursive_max_claims": 0,
            "mini_recursive_claims_configured": 0,
            "mini_recursive_claims_planned": 0,
            "mini_recursive_claims_compiled": 0,
            "mini_recursive_claims_attempted": 0,
            "mini_recursive_claim_sample_checks": 0,
            "mini_recursive_claim_sample_falsified": 0,
            "mini_recursive_claim_structural_falsified": 0,
            "mini_recursive_claim_sample_inconclusive": 0,
            "mini_recursive_claim_sample_skipped_dangerous_nat_pow": 0,
            "mini_recursive_claims_dependency_skipped": 0,
            "mini_recursive_claims_deferred_by_cap": 0,
            "mini_recursive_claims_invalidated": 0,
            "mini_recursive_claims_invalidated_repeated_skipped": 0,
            "mini_recursive_claims_unverified_invalidity_ignored": 0,
            "mini_recursive_false_parent_routes_poisoned": 0,
            "mini_recursive_false_parent_dependency_work_suppressed": 0,
            "mini_recursive_invalidated_parent_events_suppressed": 0,
            "mini_recursive_planner_call_failures": 0,
            "mini_recursive_planner_terminal_failures": 0,
            "mini_recursive_planner_scoped_failures": 0,
            "mini_recursive_planner_parse_failures": 0,
            "mini_recursive_planner_parse_retries": 0,
            "mini_recursive_planner_parse_retries_succeeded": 0,
            "mini_recursive_planner_truncated_responses_rejected": 0,
            "mini_recursive_planner_escalations": 0,
            "mini_recursive_child_terminal_failures": 0,
            "mini_recursive_child_scoped_failures": 0,
            "mini_recursive_plans_self_refuting_sanity_rejected": 0,
            "mini_recursive_plans_sanity_contract_diagnostics": 0,
            "mini_recursive_plans_sanity_missing_check_diagnostics": 0,
            "mini_recursive_plans_sanity_missing_status_diagnostics": 0,
            "mini_recursive_plans_sanity_declared_failure_diagnostics": 0,
            "mini_recursive_plans_sanity_status_conflict_diagnostics": 0,
            "mini_recursive_plans_self_refuting_sanity_diagnostics": 0,
            "mini_recursive_plans_planner_withdrawn_claims_withheld": 0,
            "mini_recursive_plans_planner_withdrawn_claims_diagnostics": 0,
            "mini_recursive_plans_unchecked_counterexample_rejected": 0,
            "mini_recursive_plans_oversized_analytic_rejected": 0,
            "mini_recursive_plans_analytic_worksheet_rejected": 0,
            "mini_recursive_plans_malformed_surface_rejected": 0,
            "mini_recursive_plans_no_claims_after_filters": 0,
            "mini_recursive_plans_dependency_contract_rejected": 0,
            "mini_recursive_plans_unmet_assembly_bridge_rejected": 0,
            "mini_recursive_plans_unmet_assembly_bridge_all_filtered": 0,
            "mini_recursive_plans_unmet_assembly_bridge_recovery_passes_granted": 0,
            "mini_recursive_plans_root_route_disconnected_after_filters": 0,
            "mini_recursive_plans_missing_root_terminal": 0,
            "mini_recursive_route_contracts_missing_root_terminal_rejected": 0,
            "mini_recursive_dependency_contract_claims_suspended": 0,
            "mini_recursive_dependency_contract_claims_rehydrated": 0,
            "mini_recursive_plans_semantic_role_contract_rejected": 0,
            "mini_recursive_progress_continuation_passes_granted": 0,
            "mini_recursive_root_equivalent_claim_variants_suppressed": 0,
            "mini_recursive_root_equivalent_claims_exhausted": 0,
            "mini_recursive_durable_root_short_circuits": 0,
            "mini_recursive_root_equivalent_helper_candidates": 0,
            "mini_recursive_root_equivalent_helper_promotions": 0,
            "mini_recursive_root_equivalent_helper_promotion_failures": 0,
            "mini_recursive_llm_root_close_attempts": 0,
            "mini_recursive_llm_root_close_solved": 0,
            "mini_recursive_last_failure_reason": "",
            "mini_recursive_exit_reason": "",
            "terminal_proof_search_reason": "",
            "terminal_proof_search_phase": "",
            "mini_apply_decl_tool_state_updates": 0,
            "mini_apply_decl_tool_state_closures": 0,
            "mini_compute_examples_calls": 0,
            "mini_compute_examples_queries": 0,
            "mini_compute_examples_successes": 0,
            "mini_compute_examples_rejected": 0,
            "mini_compute_examples_errors": 0,
            "mini_answer_visibility_visible_to_llm": 0,
            "mini_answer_visibility_hidden_opaque_mode": 0,
            "mini_answer_visibility_hidden_capability_missing": 0,
            "mini_answer_visibility_not_applicable": 0,
            "mini_lemma_cache_store_errors": 0,
            "mini_lemma_cache_deadline_integrity_unrecoverable": 0,
            "mini_lemma_cache_ingest_schema_migrated": 0,
            "mini_lemma_cache_ingest_schema_rejected": 0,
            "mini_lemma_cache_ingest_quality_rejected": 0,
            "mini_lemma_cache_ingest_projection_rejected": 0,
            "mini_lemma_cache_ingest_policy_rejected": 0,
            "mini_lemma_cache_ingest_field_rejected": 0,
            "mini_lemma_cache_ingest_owner_deduped": 0,
            "mini_accepted_proof_stubs": 0,
            "mini_parallel_sample_proof_state_snapshots": 0,
            "mini_parallel_sample_structural_snapshots": 0,
            "mini_parallel_sample_structural_nodes_imported": 0,
            "mini_parallel_sample_structural_nodes_coalesced": 0,
            "mini_parallel_sample_structural_edges_imported": 0,
            "mini_parallel_sample_structural_branch_frames_imported": 0,
            "mini_parallel_sample_structural_conflicts": 0,
            "mini_parallel_sample_failures": 0,
            "mini_parallel_samples_zero_completed": 0,
            "mini_parallel_late_sample_candidates_preserved": 0,
            "mini_parallel_late_sample_successes_preserved": 0,
            "mini_parallel_late_sample_abandoned": 0,
            "mini_parallel_late_sample_grace_timeouts": 0,
            "mini_search_pre_retrieved_duplicates_suppressed": 0,
            "mini_search_local_decl_queries_suppressed": 0,
            "mini_hollow_root_reducers_detected": 0,
            "mini_hollow_root_reducers_reenabled_by_premise": 0,
            "mini_negative_evidence_helpers_withheld": 0,
            "mini_graph_hollow_reducer_certificates_blocked": 0,
            "mini_graph_negative_evidence_certificates_blocked": 0,
            "mini_graph_negative_evidence_exact_certificates_accepted": 0,
            "mini_graph_negative_evidence_contradicted_targets": 0,
            "mini_graph_negative_evidence_contradicted_routes": 0,
            "mini_graph_root_equivalent_claims_suppressed": 0,
            "mini_session_theory_lemmas_accepted": 0,
            "mini_session_parent_progress_edges": 0,
            "mini_session_parent_progress_obligations_proved": 0,
            "mini_session_strong_progress_outcomes": 0,
            "mini_session_soft_progress_outcomes": 0,
            "mini_session_helper_progress_soft_alias": 0,
            "mini_session_helper_progress_soft_weak_theory": 0,
            "mini_session_progress_invariant_false_strong_weak_helper": 0,
            "mini_session_progress_invariant_parent_progress_undercredited": 0,
            "mini_recursive_plan_premise_dependencies_inferred": 0,
            "mini_session_assemble_route_conversation_rejected": 0,
            "mini_session_assemble_route_static_conversation_suppressed": 0,
            "mini_session_unscoped_root_authoring_suppressed": 0,
            "mini_session_ready_root_route_drain_selected": 0,
            "mini_session_ready_root_route_drain_budget_blocked": 0,
            "mini_session_ready_root_route_drain_not_applicable": 0,
            "mini_session_ready_root_route_drain_headroom_granted": 0,
            "mini_session_graph_route_no_replayable_helpers": 0,
            "mini_session_graph_route_contract_blocked": 0,
            "mini_session_graph_route_missing_assembly_bridge": 0,
            "mini_session_graph_route_authoring_missing_bridge_suppressed": 0,
            "mini_session_graph_route_cases_synthesized": 0,
            "mini_session_graph_route_cases_solved": 0,
            "mini_session_graph_route_cases_failed": 0,
            "mini_session_graph_route_root_tactic_continued": 0,
            "mini_session_graph_obligations_promoted_to_child_goals": 0,
            "mini_session_graph_obligations_reused_proof_state_child_goals": 0,
            "mini_root_assembly_contract_blocked": 0,
            "mini_session_graph_route_authoring_requested": 0,
            "mini_session_graph_route_authoring_failed": 0,
            "mini_session_materialization_tickets_retained": 0,
            "mini_session_llm_response_record_missing": 0,
            "mini_session_llm_retry_deadline_exhausted": 0,
            "mini_session_llm_retry_deadline_guard_failures": 0,
            "mini_session_llm_retry_deadline_http_status_failures": 0,
            "mini_session_llm_retry_deadline_timeout_failures": 0,
            "mini_session_llm_retry_deadline_transport_failures": 0,
            "mini_session_llm_scoped_failures": 0,
            "mini_session_llm_retry_deadline_scoped_failures": 0,
            "mini_session_llm_last_failure_reason": "",
            "mini_session_llm_last_failure_scope": "",
            "mini_session_llm_last_failure_kind": "",
            "mini_session_llm_last_failure_phase": "",
            "mini_session_verdict_proof_policy_repair_redirect": 0,
            "mini_session_repair_self_check_no_try_lean_call": 0,
            "mini_session_repair_self_check_no_accepted_try_lean": 0,
            "mini_session_repair_self_check_tool_budget_exhausted": 0,
            "mini_session_repair_self_check_terminal_continuation": 0,
            "mini_session_helper_decomposition_disabled_rejections": 0,
            "mini_session_no_proof_giveup_extractable_helpers_recovered": 0,
            "mini_session_proof_only_helper_decomposition_skipped": 0,
            "mini_session_proof_only_helper_support_materialized": 0,
            "mini_session_proof_only_helper_support_rejected": 0,
            "mini_session_same_target_decl_proofs_normalized": 0,
            "mini_session_same_target_decl_proofs_accepted": 0,
            "mini_session_same_target_decl_proofs_rejected": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_routed": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_accepted": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_bridge_support_recorded": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_rejected": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_dependencies_banked": 0,
            "mini_session_same_target_decl_proofs_graph_formalization_dependency_rejected": 0,
            "mini_session_proof_turn_decl_graph_formalization_routed": 0,
            "mini_session_proof_turn_decl_graph_formalization_accepted": 0,
            "mini_session_proof_turn_decl_graph_formalization_bridge_support_recorded": 0,
            "mini_session_proof_turn_decl_graph_formalization_rejected": 0,
            "mini_session_proof_turn_decl_graph_formalization_dependencies_banked": 0,
            "mini_session_proof_turn_decl_graph_formalization_dependency_rejected": 0,
            "mini_session_no_applicable_recoveries": 0,
            "mini_session_no_applicable_repair_restore_reanchors": 0,
            "mini_session_no_applicable_budget_granted": 0,
            "mini_session_no_applicable_terminal": 0,
            "mini_session_no_applicable_deferred_only_serviceable_work": 0,
            "mini_session_no_applicable_suppression_recoveries": 0,
            "mini_session_no_applicable_stale_suppressors_released": 0,
            "mini_session_cost_governed_continuations": 0,
            "mini_session_cost_governed_budget_granted": 0,
            "mini_session_cost_governed_repair_policy_released": 0,
            "mini_session_cost_governed_forced_static_conversation": 0,
            "mini_session_cost_governed_static_no_serviceable_work_suppressed": 0,
            "mini_session_cost_governed_no_dispatch_lane": 0,
            "mini_session_cost_governed_no_cost_capacity": 0,
            "mini_session_cost_governed_lean_infra_deferred": 0,
            "mini_session_model_call_deferred_frontier_actions": 0,
            "mini_session_model_call_deferred_frontier_retry_releases": 0,
            "mini_session_model_call_deferred_static_retry_releases": 0,
            "mini_session_cast_normalization_applicable": 0,
            "mini_session_cast_normalization_attempts": 0,
            "mini_session_cast_normalization_nat_sub_guards_attempted": 0,
            "mini_session_cast_normalization_choose_rewrites_attempted": 0,
            "mini_session_cast_normalization_side_conditions_exposed": 0,
            "mini_session_cast_normalization_side_conditions_materialized": 0,
            "mini_session_cast_normalization_solved": 0,
            "mini_session_cast_normalization_failed": 0,
            "mini_session_finset_reindexing_applicable": 0,
            "mini_session_finset_reindexing_attempts": 0,
            "mini_session_finset_reindexing_sum_goals_attempted": 0,
            "mini_session_finset_reindexing_product_goals_attempted": 0,
            "mini_session_finset_reindexing_filter_rewrites_attempted": 0,
            "mini_session_finset_reindexing_antidiagonal_rewrites_attempted": 0,
            "mini_session_finset_reindexing_side_conditions_exposed": 0,
            "mini_session_finset_reindexing_side_conditions_materialized": 0,
            "mini_session_finset_reindexing_solved": 0,
            "mini_session_finset_reindexing_failed": 0,
            "mini_session_proof_patches_applied": 0,
            "mini_session_proof_patch_failures": 0,
            "mini_session_post_failure_repair_first_deferrals": 0,
            "mini_session_local_repair_quota_armed": 0,
            "mini_session_local_repair_turns_forced": 0,
            "mini_session_local_repair_quota_scoped_action_selected": 0,
            "mini_session_local_repair_giveup_suppressed": 0,
            "mini_session_local_repair_quota_exhausted": 0,
            "mini_session_repair_tickets_created": 0,
            "mini_session_repair_tickets_queued": 0,
            "mini_session_repair_tickets_promoted": 0,
            "mini_session_repair_tickets_selected": 0,
            "mini_session_repair_tickets_resolved": 0,
            "mini_session_repair_tickets_exhausted": 0,
            "mini_session_repair_tickets_retry_remaining": 0,
            "mini_session_repair_tickets_unresolved_attempts_consumed": 0,
            "mini_session_repair_tickets_unresolved_exhausted": 0,
            "mini_session_repair_tickets_policy_retries_remaining": 0,
            "mini_session_repair_ticket_policy_continuations": 0,
            "mini_session_repair_tickets_scheduler_blocked": 0,
            "mini_session_repair_tickets_policy_rejections_consumed": 0,
            "mini_session_repair_tickets_policy_narrowing_required": 0,
            "mini_session_repair_tickets_unserviceable_route_replan": 0,
            "mini_session_repair_tickets_preempted_by_fallback": 0,
            "mini_session_repair_ticket_blocked_no_action": 0,
            "mini_session_repair_policy_narrowing_blocked": 0,
            "mini_session_repair_policy_scope_materializations": 0,
            "mini_session_repair_policy_narrowing_no_recovery": 0,
            "mini_session_repair_policy_child_adaptive_fallback_yields": 0,
            "mini_session_repair_policy_frontier_selected": 0,
            "mini_session_repair_policy_narrowing_retained_after_no_progress": 0,
            "mini_session_root_authoring_yielded_to_scoped_frontier": 0,
            "mini_session_retired_graph_target_restore_suppressed": 0,
            "mini_session_retired_graph_target_repair_ticket_suppressed": 0,
            "mini_session_retired_graph_target_repair_policy_suppressed": 0,
            "mini_session_retired_graph_target_local_repair_suppressed": 0,
            "mini_session_retired_graph_target_policy_redirect_suppressed": 0,
            "mini_session_retired_graph_target_formalization_suppressed": 0,
            "mini_session_retired_graph_target_frontier_suppressed": 0,
            "mini_session_promoted_graph_target_restore_suppressed": 0,
            "mini_session_terminal_graph_target_repair_bypassed": 0,
            "mini_session_terminal_graph_target_retained_for_bounded_repair": 0,
            "mini_session_terminal_graph_target_repair_ticket_bypassed": 0,
            "mini_session_terminal_graph_target_local_repair_bypassed": 0,
            "mini_session_terminal_graph_target_suppressed_by_reason": 0,
            "mini_session_terminal_graph_target_repair_bypass_deduped": 0,
            "mini_session_graph_formalization_negative_bridge_support_rejected": 0,
            "mini_session_graph_formalization_bridge_support_recorded": 0,
            "mini_session_graph_formalization_route_support_helpers_hidden": 0,
            "mini_session_graph_formalization_bridge_parent_work_materialized": 0,
            "mini_session_graph_formalization_bridge_parent_work_missing": 0,
            "mini_session_graph_formalization_bridge_parent_assembly_scheduled": 0,
            "mini_session_graph_formalization_bridge_support_reselected_without_parent_work": 0,
            "mini_session_graph_formalization_rejected_helpers_banked_proposed": 0,
            "mini_session_formalization_helper_declaration_rejected": 0,
            "mini_session_formalization_requires_declaration": 0,
            "mini_session_graph_formalization_repeated_bridge_suppressed": 0,
            "mini_session_graph_formalization_duplicate_obligations_suppressed": 0,
            "mini_session_materialization_pending_reselected_same_action": 0,
            "mini_session_materialization_pending_escalated": 0,
            "mini_session_materialization_pending_recoveries": 0,
            "mini_session_materialization_pending_suppressors_released": 0,
            "mini_session_repair_policy_narrowing_reselected_same_work": 0,
            "mini_session_repair_policy_narrowing_materialization_escalated": 0,
            "mini_session_unknown_identifier_api_search_required": 0,
            "mini_session_unknown_identifier_api_search_policy_rejections": 0,
            "mini_session_parse_errors_code_generation_failures": 0,
            "mini_session_target_integrity_signals": 0,
            "mini_session_target_integrity_fake_contradiction_detected": 0,
            "mini_session_target_integrity_unverified_refutation_detected": 0,
            "mini_session_target_integrity_semantic_bridge_direction_detected": 0,
            "mini_session_target_integrity_proof_state_repair_bypassed": 0,
            "mini_session_target_integrity_local_repair_bypassed": 0,
            "mini_session_target_integrity_adjudication_materialized": 0,
            "mini_session_target_integrity_adjudication_progress_suppressed": 0,
            "mini_session_target_integrity_no_proof_signals": 0,
            "mini_session_target_integrity_no_proof_adjudication_materialized": 0,
            "mini_session_target_integrity_repair_tickets_contaminated": 0,
            "mini_session_target_integrity_repair_tickets_suppressed": 0,
            "mini_session_unscoped_root_repair_replans": 0,
            "mini_session_unscoped_root_repair_tickets_scope_redirected": 0,
            "mini_session_unscoped_root_repair_new_tickets_suppressed": 0,
            "mini_session_unscoped_root_repair_tickets_preempted_by_fallback": 0,
            "mini_session_unscoped_root_repair_tickets_yielded_to_static_prepass": 0,
            "mini_session_scoped_repair_tickets_retained_after_fallback": 0,
            "mini_session_unselected_root_policy_misses_scope_redirected": 0,
            "mini_session_local_root_repair_quota_suppressed": 0,
            "mini_session_local_root_repair_quota_preempted_by_fallback": 0,
            "mini_session_route_replan_unserviceable_skipped": 0,
            "mini_session_route_scoped_advisory_helpers_suppressed": 0,
            "mini_verified_helper_statement_aliases_recorded": 0,
            "mini_verified_root_equivalent_helpers_withheld": 0,
            "mini_session_failure_residual_obligations_quarantined_unscheduled": 0,
            "mini_session_schedulable_decompositions_created": 0,
            "mini_session_quarantined_residual_diagnostics_created": 0,
            "mini_session_soft_progress_streak_saturated": 0,
            "mini_root_finalization_candidates": 0,
            "mini_root_finalization_accepted": 0,
            "mini_root_finalization_blocked": 0,
            "mini_root_finalization_support_mismatch": 0,
            "mini_root_finalization_route_contract_not_ready": 0,
            "mini_root_finalization_missing_certificate": 0,
            "mini_root_finalization_target_mismatch": 0,
            "mini_root_finalization_certificate_rejected": 0,
            "mini_root_finalization_certificate_accepted": 0,
            "mini_root_finalization_bypass_blocked": 0,
            "mini_branching_advisory_helpers_suppressed": 0,
            "mini_proposed_helpers_banked": 0,
            "mini_recursive_proposed_helpers_seeded": 0,
            "mini_recursive_proposed_helpers_invalidated_suppressed": 0,
            "llm_temperature_requests": 0,
            "llm_temperature_effective_calls": 0,
            "llm_temperature_provider_dropped": 0,
            "llm_temperature_by_phase": {},
        }
        self.metrics.update(
            {key: 0 for key in self._MINI_SESSION_VERDICT_METRICS.values()}
        )
        self.metrics.update(
            {key: 0 for key in _MINI_GRAPH_RECURSIVE_DECOMPOSE_METRIC_KEYS}
        )
        self.metrics.update({key: 0 for key in _MINI_TARGET_INTEGRITY_METRIC_KEYS})
        self.metrics.update(
            {
                key: 0
                for key in _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS
                if key not in self.metrics
            }
        )
        self._mini_recursive_incremental_since_complete: Dict[str, int] = {}
        self._last_mini_recursive_complete_totals: Dict[str, int] = {}
        self._formalization_banked_helper_metric_seen: Set[str] = set()
        self._compute_receipt_metric_seen: Set[str] = set()

    def configure_live_trace(self, mode: str) -> None:
        clean = str(mode or "compact").strip().lower()
        if clean not in _LIVE_TRACE_MODES:
            clean = "compact"
        self.live_trace_mode = clean
        self.live_trace_response_chars = None if clean == "full" else 1600

    @staticmethod
    def _policy_error_metric_key(error_type: str) -> str:
        if not error_type:
            return ""
        return f"lean_error_type_{error_type}"

    def _count_new_formalization_banked_helpers(
        self,
        value: Any,
        record: Dict[str, Any],
    ) -> int:
        if isinstance(value, list):
            amount = 0
            turn_key = (
                str(record.get("conv_turn_index_absolute") or "").strip()
                or str(record.get("conv_turn_index_phase") or "").strip()
            )
            for item in value:
                helper_name = str(item or "").strip()
                if not helper_name:
                    continue
                dedupe_key = f"{turn_key}:{helper_name}" if turn_key else helper_name
                if dedupe_key in self._formalization_banked_helper_metric_seen:
                    continue
                self._formalization_banked_helper_metric_seen.add(dedupe_key)
                amount += 1
            return amount
        try:
            return max(0, int(value or 0))
        except (TypeError, ValueError):
            return 0

    def _record_policy_metrics(self, record: Dict[str, Any]) -> None:
        if str(record.get("verdict") or "") not in {
            "proof_policy_rejected",
            "proof_policy_repair_redirect",
        }:
            return
        error_type = (
            str(record.get("lean_error_type") or "").strip()
            or str(record.get("rejection_reason") or "").strip()
        )
        if error_type not in self._POLICY_METRIC_ERROR_TYPES:
            return
        key = self._policy_error_metric_key(error_type)
        if not key:
            return
        self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1

    def _record_structural_metrics(self, record: Dict[str, Any]) -> None:
        self._record_compute_receipt_metrics(record)
        verdict = str(record.get("verdict") or "")
        verdict_metric_key = self._MINI_SESSION_VERDICT_METRICS.get(verdict)
        if verdict_metric_key:
            self.metrics[verdict_metric_key] = (
                int(self.metrics.get(verdict_metric_key, 0) or 0) + 1
            )
        rejection_reason = str(record.get("rejection_reason") or "").strip()
        lean_error_type = str(record.get("lean_error_type") or "").strip()
        formalization_error = lean_error_type or rejection_reason
        policy_error_already_counted = (
            verdict in {"proof_policy_rejected", "proof_policy_repair_redirect"}
            and formalization_error in self._POLICY_METRIC_ERROR_TYPES
        )
        if formalization_error == "formalization_helper_declaration_rejected":
            key = "mini_session_formalization_helper_declaration_rejected"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            error_key = "lean_error_type_formalization_helper_declaration_rejected"
            if not policy_error_already_counted:
                self.metrics[error_key] = int(self.metrics.get(error_key, 0) or 0) + 1
        elif formalization_error == "formalization_requires_declaration":
            key = "mini_session_formalization_requires_declaration"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            error_key = "lean_error_type_formalization_requires_declaration"
            if not policy_error_already_counted:
                self.metrics[error_key] = int(self.metrics.get(error_key, 0) or 0) + 1
        elif formalization_error == "repair_self_check_terminal_continuation":
            key = "mini_session_repair_self_check_terminal_continuation"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            error_key = "lean_error_type_repair_self_check_terminal_continuation"
            if not policy_error_already_counted:
                self.metrics[error_key] = int(self.metrics.get(error_key, 0) or 0) + 1
        phase = str(record.get("phase") or "")
        if phase == "answer_visibility":
            if verdict == "official_answer_visible_to_llm":
                key = "mini_answer_visibility_visible_to_llm"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "official_answer_not_applicable":
                key = "mini_answer_visibility_not_applicable"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "official_answer_hidden_from_llm":
                reason = str(record.get("reason") or "")
                key = (
                    "mini_answer_visibility_hidden_opaque_mode"
                    if reason == "opaque_mode"
                    else "mini_answer_visibility_hidden_capability_missing"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "graph_work_consumed":
            if verdict in {
                "route_authoring_requested_missing_assembly_bridge",
                "route_missing_assembly_bridge",
            }:
                key = "mini_session_graph_route_missing_assembly_bridge"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if bool(record.get("route_root_tactic_authoring_suppressed")):
                key = "mini_session_graph_route_authoring_missing_bridge_suppressed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict in {
                "route_authoring_requested_missing_assembly_bridge",
                "route_root_tactic_failed_authoring_requested",
            }:
                key = "mini_session_graph_route_authoring_requested"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if bool(record.get("route_authoring_failed")):
                key = "mini_session_graph_route_authoring_failed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "formalization_materialization_pending":
                key = "mini_session_materialization_tickets_retained"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("materialization_pending_action_skipped")):
                    key = "mini_session_materialization_pending_escalated"
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("materialization_pending_reselected_same_action")):
                    key = (
                        "mini_session_materialization_pending_reselected_same_action"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("repair_policy_narrowing_required")):
                    key = (
                        "mini_session_repair_policy_narrowing_materialization_escalated"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                    if bool(record.get("materialization_pending_reselected_same_action")):
                        key = (
                            "mini_session_repair_policy_narrowing_reselected_same_work"
                        )
                        self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            verdict == "no_proof_extracted"
            and rejection_reason == "helper_decomposition_disabled"
        ):
            key = "mini_session_helper_decomposition_disabled_rejections"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1

        if (
            phase == "proof_only_post_failure_guard"
            and verdict == "helper_decomposition_skipped"
        ):
            key = "mini_session_proof_only_helper_decomposition_skipped"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            verdict == "graph_native_formalization_bridge_support_recorded"
            and bool(record.get("proof_only_helper_support_materialized"))
        ):
            key = "mini_session_proof_only_helper_support_materialized"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            verdict == "graph_native_formalization_bridge_rejected"
            and bool(record.get("proof_only_helper_support_attempted"))
        ):
            key = "mini_session_proof_only_helper_support_rejected"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if bool(record.get("same_target_decl_proof_normalized")):
            if verdict == "llm_response":
                key = "mini_session_same_target_decl_proofs_normalized"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict in {
                "solved",
                "solved_after_lemma_dag_helper",
                "solved_after_helper_only_salvage",
                "solved_after_helper_salvage",
                "solved_after_proof_state_child",
                "tactic_solved",
            }:
                key = "mini_session_same_target_decl_proofs_accepted"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict in {
                "lean_rejected",
                "proof_policy_rejected",
                "lean_infra_error",
            }:
                key = "mini_session_same_target_decl_proofs_rejected"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if bool(record.get("same_target_decl_proof_graph_formalization_routed")):
            if verdict == "same_target_decl_proof_graph_formalization_routed":
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_routed"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_proved":
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_accepted"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_bridge_support_recorded":
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_bridge_support_recorded"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_dependency_rejected":
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_dependency_rejected"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict in {
                "lean_rejected",
                "proof_policy_rejected",
                "lean_infra_error",
                "graph_native_formalization_bridge_rejected",
                "graph_native_formalization_dependency_rejected",
            }:
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_rejected"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            dependency_names = record.get("same_turn_dependency_helper_names")
            if isinstance(dependency_names, list) and dependency_names:
                key = (
                    "mini_session_same_target_decl_proofs_graph_formalization_dependencies_banked"
                )
                self.metrics[key] = (
                    int(self.metrics.get(key, 0) or 0) + len(dependency_names)
                )
        if bool(record.get("proof_turn_decl_graph_formalization_routed")):
            if verdict == "proof_turn_decl_graph_formalization_routed":
                key = "mini_session_proof_turn_decl_graph_formalization_routed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_proved":
                key = "mini_session_proof_turn_decl_graph_formalization_accepted"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_bridge_support_recorded":
                key = (
                    "mini_session_proof_turn_decl_graph_formalization_bridge_support_recorded"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "graph_native_formalization_dependency_rejected":
                key = (
                    "mini_session_proof_turn_decl_graph_formalization_dependency_rejected"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict in {
                "lean_rejected",
                "proof_policy_rejected",
                "lean_infra_error",
                "graph_native_formalization_bridge_rejected",
                "graph_native_formalization_dependency_rejected",
            }:
                key = "mini_session_proof_turn_decl_graph_formalization_rejected"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            dependency_names = record.get("same_turn_dependency_helper_names")
            if isinstance(dependency_names, list) and dependency_names:
                key = (
                    "mini_session_proof_turn_decl_graph_formalization_dependencies_banked"
                )
                self.metrics[key] = (
                    int(self.metrics.get(key, 0) or 0) + len(dependency_names)
                )
        if verdict == "llm_call_failed":
            self.metrics["mini_session_llm_call_failures"] = (
                int(self.metrics.get("mini_session_llm_call_failures", 0) or 0) + 1
            )
            llm_failure_kind = str(record.get("llm_failure_kind") or "").strip()
            llm_error_classification = None
            if not llm_failure_kind or llm_failure_kind in {"unknown", "text"}:
                llm_error_classification = classify_llm_error_text(
                    str(record.get("llm_error") or "")
                )
                llm_failure_kind = llm_error_classification.kind
            if llm_failure_kind == "llm_retry_deadline_exhausted":
                self.metrics["mini_session_llm_retry_deadline_exhausted"] = (
                    int(
                        self.metrics.get(
                            "mini_session_llm_retry_deadline_exhausted",
                            0,
                        )
                        or 0
                    )
                    + 1
                )
                deadline_record = llm_retry_deadline_fields(record)
                if not deadline_record:
                    deadline_record = llm_retry_deadline_record_from_text(
                        str(record.get("llm_error") or "")
                    )
                deadline_family = str(
                    deadline_record.get(
                        "llm_retry_deadline_original_exception_family"
                    )
                    or ""
                ).strip()
                family_metric = {
                    "deadline_guard": "mini_session_llm_retry_deadline_guard_failures",
                    "http_status": "mini_session_llm_retry_deadline_http_status_failures",
                    "timeout": "mini_session_llm_retry_deadline_timeout_failures",
                    "transport": "mini_session_llm_retry_deadline_transport_failures",
                }.get(deadline_family)
                if family_metric:
                    self.metrics[family_metric] = (
                        int(self.metrics.get(family_metric, 0) or 0) + 1
                    )
                scoped_metric_counted = True
                self.metrics["mini_session_llm_scoped_failures"] = (
                    int(self.metrics.get("mini_session_llm_scoped_failures", 0) or 0)
                    + 1
                )
                self.metrics["mini_session_llm_retry_deadline_scoped_failures"] = (
                    int(
                        self.metrics.get(
                            "mini_session_llm_retry_deadline_scoped_failures",
                            0,
                        )
                        or 0
                    )
                    + 1
                )
            else:
                scoped_metric_counted = False
            terminal_failure_reason = str(
                record.get("terminal_failure_reason") or ""
            ).strip()
            scoped_failure_reason = str(
                record.get("scoped_failure_reason") or ""
            ).strip()
            if (
                not terminal_failure_reason
                and llm_error_classification is not None
                and bool(llm_error_classification.terminal)
            ):
                terminal_failure_reason = str(
                    llm_error_classification.failure_reason or ""
                ).strip()
            failure_scope = str(record.get("llm_failure_scope") or "").strip()
            if not failure_scope:
                failure_scope = llm_failure_scope(
                    terminal_failure_reason or scoped_failure_reason
                )
            if failure_scope == "scoped":
                scoped_failure_reason = scoped_failure_reason or terminal_failure_reason
                terminal_failure_reason = ""
            last_failure_reason = (
                terminal_failure_reason
                or scoped_failure_reason
                or str(llm_failure_kind or "").strip()
            )
            if last_failure_reason:
                self.metrics["mini_session_llm_last_failure_reason"] = (
                    last_failure_reason
                )
                self.metrics["mini_session_llm_last_failure_scope"] = failure_scope
                self.metrics["mini_session_llm_last_failure_kind"] = (
                    str(llm_failure_kind or "").strip()
                )
                self.metrics["mini_session_llm_last_failure_phase"] = phase
            if scoped_failure_reason and not scoped_metric_counted:
                self.metrics["mini_session_llm_scoped_failures"] = (
                    int(self.metrics.get("mini_session_llm_scoped_failures", 0) or 0)
                    + 1
                )
                if scoped_failure_reason == "llm_retry_deadline_exhausted":
                    self.metrics["mini_session_llm_retry_deadline_scoped_failures"] = (
                        int(
                            self.metrics.get(
                                "mini_session_llm_retry_deadline_scoped_failures",
                                0,
                            )
                            or 0
                        )
                        + 1
                    )
            if terminal_failure_reason:
                self.metrics["mini_session_terminal_llm_failures"] = (
                    int(
                        self.metrics.get("mini_session_terminal_llm_failures", 0)
                        or 0
                    )
                    + 1
                )
                if terminal_failure_reason == "llm_insufficient_quota":
                    self.metrics["mini_session_terminal_llm_insufficient_quota"] = (
                        int(
                            self.metrics.get(
                                "mini_session_terminal_llm_insufficient_quota",
                                0,
                            )
                            or 0
                        )
                        + 1
                    )
        if verdict == "llm_response_record_missing":
            key = "mini_session_llm_response_record_missing"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if str(record.get("phase") or "") == "llm_usage":
            self._record_llm_usage_metrics(record)
        repair_status = str(
            record.get("repair_self_check_status")
            or record.get("repair_self_check_missing_kind")
            or ""
        ).strip()
        repair_metric_mapping = {
            "no_try_lean_call": "mini_session_repair_self_check_no_try_lean_call",
            "no_accepted_try_lean": "mini_session_repair_self_check_no_accepted_try_lean",
            "tool_budget_exhausted": "mini_session_repair_self_check_tool_budget_exhausted",
        }
        repair_metric_key = repair_metric_mapping.get(repair_status)
        if repair_metric_key:
            rejection_reason = str(record.get("rejection_reason") or "").strip()
            session_scoped = bool(record.get("session_scope"))
            phase = str(record.get("phase") or "").strip()
            outcome_only_repair_status = (
                session_scoped
                and phase in {"session_action_outcome", "session_subaction_outcome"}
                and verdict == "outcome_applied"
                and not bool(record.get("llm_response_recorded"))
                and not bool(record.get("repair_self_check_metric_counted"))
            )
            should_count_repair_status = (
                (session_scoped and verdict == "llm_response")
                or outcome_only_repair_status
                or (
                    verdict == "proof_policy_rejected"
                    and (
                        (repair_status == "no_accepted_try_lean" and not session_scoped)
                        or rejection_reason
                        in {
                            "repair_self_check_no_try_lean_call",
                            "repair_self_check_tool_budget_exhausted",
                            "repair_self_check_missing",
                        }
                    )
                )
                or (
                    not session_scoped
                    and verdict
                    in {
                        "known_answer_no_construction_collapse",
                        "llm_call_failed",
                        "solved",
                        "solved_after_helper_only_salvage",
                        "solved_after_helper_salvage",
                        "solved_after_lemma_dag_helper",
                        "solved_after_proof_state_child",
                        "tactic_solved",
                        "tactic_rejected",
                        "lean_rejected",
                        "no_proof_extracted",
                        "lean_infra_error",
                    }
                )
            )
            if should_count_repair_status:
                self.metrics[repair_metric_key] = (
                    int(self.metrics.get(repair_metric_key, 0) or 0) + 1
                )
        banked = record.get("banked_proposed_helpers") or []
        if isinstance(banked, list) and banked:
            key = "mini_proposed_helpers_banked"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + len(banked)
        rejected_formalization_banked = record.get(
            "formalization_rejected_helpers_banked_proposed"
        )
        rejected_candidate_formalization_banked = record.get(
            "formalization_rejected_candidate_banked_proposed_helpers"
        )
        amount = self._count_new_formalization_banked_helpers(
            rejected_formalization_banked,
            record,
        ) + self._count_new_formalization_banked_helpers(
            rejected_candidate_formalization_banked,
            record,
        )
        if amount > 0:
            key = "mini_session_graph_formalization_rejected_helpers_banked_proposed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + amount
        seeded = record.get("proposed_helpers_seeded") or []
        if (
            str(record.get("phase") or "") == "mini_recursive_plan"
            and isinstance(seeded, list)
            and seeded
        ):
            key = "mini_recursive_proposed_helpers_seeded"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + len(seeded)
        if (
            str(record.get("phase") or "") == "mini_recursive_proposed_helper"
            and verdict == "proposed_helper_skipped_child_invalidated"
        ):
            key = "mini_recursive_proposed_helpers_invalidated_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "mini_recursive_plan"
            and verdict == "plan_started"
            and int(record.get("pass_index") or 1) <= 1
        ):
            self._mini_recursive_incremental_since_complete = {}
            self._last_mini_recursive_complete_totals = {}
        if (
            phase == "mini_recursive_route_contract"
            and verdict == "claims_deferred_by_cap"
        ):
            deferred_names = record.get("deferred_claim_names") or []
            amount = len(deferred_names) if isinstance(deferred_names, list) else 1
            self.metrics["mini_recursive_claims_deferred_by_cap"] = (
                int(self.metrics.get("mini_recursive_claims_deferred_by_cap", 0) or 0)
                + max(1, amount)
            )
        mini_recursive_stat_mapping = {
            "claims_planned": "mini_recursive_claims_planned",
            "claims_compiled": "mini_recursive_claims_compiled",
            "claims_attempted": "mini_recursive_claims_attempted",
            "claim_type_checks": "mini_recursive_claim_type_checks",
            "claim_type_rejected": "mini_recursive_claim_type_rejected",
            "claim_type_inconclusive": "mini_recursive_claim_type_inconclusive",
            "claim_sample_checks": "mini_recursive_claim_sample_checks",
            "claim_sample_falsified": "mini_recursive_claim_sample_falsified",
            "claim_structural_falsified": "mini_recursive_claim_structural_falsified",
            "claim_sample_inconclusive": "mini_recursive_claim_sample_inconclusive",
            "claim_sample_skipped_dangerous_nat_pow": "mini_recursive_claim_sample_skipped_dangerous_nat_pow",
            "claims_dependency_skipped": "mini_recursive_claims_dependency_skipped",
            "claims_invalidated": "mini_recursive_claims_invalidated",
            "claims_invalidated_repeated_skipped": "mini_recursive_claims_invalidated_repeated_skipped",
            "claims_unverified_invalidity_ignored": "mini_recursive_claims_unverified_invalidity_ignored",
            "root_equivalent_claim_variants_suppressed": "mini_recursive_root_equivalent_claim_variants_suppressed",
            "planner_call_failures": "mini_recursive_planner_call_failures",
            "planner_terminal_failures": "mini_recursive_planner_terminal_failures",
            "planner_scoped_failures": "mini_recursive_planner_scoped_failures",
            "planner_parse_failures": "mini_recursive_planner_parse_failures",
            "planner_parse_retries": "mini_recursive_planner_parse_retries",
            "planner_parse_retries_succeeded": (
                "mini_recursive_planner_parse_retries_succeeded"
            ),
            "planner_truncated_responses_rejected": (
                "mini_recursive_planner_truncated_responses_rejected"
            ),
            "planner_escalations": "mini_recursive_planner_escalations",
            "child_terminal_failures": "mini_recursive_child_terminal_failures",
            "child_scoped_failures": "mini_recursive_child_scoped_failures",
            "plans_self_refuting_sanity_rejected": "mini_recursive_plans_self_refuting_sanity_rejected",
            "plans_sanity_contract_diagnostics": "mini_recursive_plans_sanity_contract_diagnostics",
            "plans_sanity_missing_check_diagnostics": "mini_recursive_plans_sanity_missing_check_diagnostics",
            "plans_sanity_missing_status_diagnostics": "mini_recursive_plans_sanity_missing_status_diagnostics",
            "plans_sanity_declared_failure_diagnostics": "mini_recursive_plans_sanity_declared_failure_diagnostics",
            "plans_sanity_status_conflict_diagnostics": "mini_recursive_plans_sanity_status_conflict_diagnostics",
            "plans_self_refuting_sanity_diagnostics": "mini_recursive_plans_self_refuting_sanity_diagnostics",
            "plans_planner_withdrawn_claims_withheld": (
                "mini_recursive_plans_planner_withdrawn_claims_withheld"
            ),
            "plans_planner_withdrawn_claims_diagnostics": (
                "mini_recursive_plans_planner_withdrawn_claims_diagnostics"
            ),
            "plans_unchecked_counterexample_rejected": "mini_recursive_plans_unchecked_counterexample_rejected",
            "plans_oversized_analytic_rejected": "mini_recursive_plans_oversized_analytic_rejected",
            "plans_analytic_worksheet_rejected": "mini_recursive_plans_analytic_worksheet_rejected",
            "plans_malformed_surface_rejected": "mini_recursive_plans_malformed_surface_rejected",
            "plans_no_claims_after_filters": "mini_recursive_plans_no_claims_after_filters",
            "plans_dependency_contract_rejected": "mini_recursive_plans_dependency_contract_rejected",
            "plans_unmet_assembly_bridge_rejected": "mini_recursive_plans_unmet_assembly_bridge_rejected",
            "plans_unmet_assembly_bridge_all_filtered": "mini_recursive_plans_unmet_assembly_bridge_all_filtered",
            "plans_unmet_assembly_bridge_recovery_passes_granted": "mini_recursive_plans_unmet_assembly_bridge_recovery_passes_granted",
            "plans_root_route_disconnected_after_filters": "mini_recursive_plans_root_route_disconnected_after_filters",
            "plans_missing_root_terminal": "mini_recursive_plans_missing_root_terminal",
            "dependency_contract_claims_suspended": "mini_recursive_dependency_contract_claims_suspended",
            "dependency_contract_claims_rehydrated": "mini_recursive_dependency_contract_claims_rehydrated",
            "plan_premise_dependencies_inferred": "mini_recursive_plan_premise_dependencies_inferred",
            "progress_continuation_passes_granted": "mini_recursive_progress_continuation_passes_granted",
            "root_equivalent_helper_candidates": "mini_recursive_root_equivalent_helper_candidates",
            "durable_root_short_circuits": "mini_recursive_durable_root_short_circuits",
            "root_equivalent_helper_promotions": "mini_recursive_root_equivalent_helper_promotions",
            "root_equivalent_helper_promotion_failures": "mini_recursive_root_equivalent_helper_promotion_failures",
            "llm_root_close_attempts": "mini_recursive_llm_root_close_attempts",
            "llm_root_close_solved": "mini_recursive_llm_root_close_solved",
            "bottleneck_obligations_materialized": "mini_recursive_bottleneck_obligations_materialized",
            "bottleneck_obligations_pending_adjudication": "mini_recursive_bottleneck_obligations_pending_adjudication",
        }

        def add_mini_recursive_stat(stat_key: str, amount: int) -> None:
            metric_key = mini_recursive_stat_mapping.get(stat_key)
            if not metric_key:
                return
            value = max(0, int(amount or 0))
            if value <= 0:
                return
            self.metrics[metric_key] = int(self.metrics.get(metric_key, 0) or 0) + value
            self._mini_recursive_incremental_since_complete[stat_key] = (
                int(
                    self._mini_recursive_incremental_since_complete.get(stat_key, 0)
                    or 0
                )
                + value
            )

        if phase == "mini_recursive_claim_llm" and verdict == "claim_llm_scoped_failure":
            add_mini_recursive_stat("child_scoped_failures", 1)

        if (
            phase == "mini_recursive_plan"
            and verdict
            in {
                "planner_escalation_call_authorized",
                "planner_escalation_repair_charged",
            }
        ):
            add_mini_recursive_stat("planner_escalations", 1)
        elif phase == "mini_recursive_plan" and (
            verdict
            in {
                "plan_truncated_transport_rejected",
                "plan_visibility_recovery_missing_root_rejected",
                "plan_reasoning_recovery_missing_root_rejected",
            }
            or (
                verdict == "planner_escalation_call_cap_rejected"
                and str(record.get("premium_call_kind") or "")
                == "visibility_recovery"
                and bool(record.get("finish_reason"))
            )
        ):
            add_mini_recursive_stat("planner_truncated_responses_rejected", 1)
        elif phase == "mini_recursive_plan_intent_contract" and verdict in {
            "claim_withheld_planner_self_abandonment",
            "claim_withheld_planner_self_abandonment_dependency",
        }:
            add_mini_recursive_stat("plans_planner_withdrawn_claims_withheld", 1)
        elif phase == "mini_recursive_plan_intent_contract" and verdict in {
            "claim_diagnosed_planner_self_abandonment",
            "claim_diagnosed_planner_self_abandonment_dependency",
        }:
            if str(record.get("policy_disposition") or "") == "diagnostic_only":
                add_mini_recursive_stat(
                    "plans_planner_withdrawn_claims_diagnostics", 1
                )
        elif phase == "mini_recursive_claim_typecheck":
            add_mini_recursive_stat("claims_attempted", 1)
            add_mini_recursive_stat("claim_type_checks", 1)
            if verdict == "variant_type_rejected":
                add_mini_recursive_stat("claim_type_rejected", 1)
            elif verdict == "variant_type_inconclusive":
                add_mini_recursive_stat("claim_type_inconclusive", 1)
        elif (
            phase == "mini_recursive_claim_variant"
            and verdict == "variant_suppressed_root_equivalent"
        ):
            add_mini_recursive_stat("root_equivalent_claim_variants_suppressed", 1)
        elif (
            phase == "mini_recursive_claim"
            and verdict == "claim_suppressed_root_equivalent_exhausted"
        ):
            self.metrics["mini_recursive_root_equivalent_claims_exhausted"] = (
                int(
                    self.metrics.get(
                        "mini_recursive_root_equivalent_claims_exhausted",
                        0,
                    )
                    or 0
                )
                + 1
            )
        elif phase == "mini_recursive_durable_root_short_circuit":
            add_mini_recursive_stat("durable_root_short_circuits", 1)
        elif phase == "mini_recursive_claim_sample":
            attempts = record.get("attempts") or []
            if isinstance(attempts, list):
                add_mini_recursive_stat("claim_sample_checks", len(attempts))
            if verdict == "variant_falsified_by_sample":
                add_mini_recursive_stat("claim_sample_falsified", 1)
            elif verdict == "variant_falsified_by_structural_obstruction":
                add_mini_recursive_stat("claim_sample_falsified", 1)
                add_mini_recursive_stat("claim_structural_falsified", 1)
            elif verdict == "variant_sample_skipped_dangerous_nat_pow":
                add_mini_recursive_stat("claim_sample_skipped_dangerous_nat_pow", 1)
            elif verdict == "variant_sample_inconclusive":
                add_mini_recursive_stat("claim_sample_inconclusive", 1)
        elif phase == "mini_recursive_claim_dependency":
            if verdict == "claim_dependency_blocked":
                add_mini_recursive_stat("claims_dependency_skipped", 1)
        elif phase == "mini_recursive_claim_invalidated":
            if verdict == "claim_invalidated_by_child":
                add_mini_recursive_stat("claims_invalidated", 1)
            elif verdict == "claim_skipped_previous_child_invalidation":
                add_mini_recursive_stat("claims_invalidated_repeated_skipped", 1)
        elif phase == "mini_recursive_plan_dependency_contract":
            if verdict in {
                "plan_rejected_dependency_contract",
                "claim_rejected_dependency_contract_tainted_dependency",
            }:
                add_mini_recursive_stat("plans_dependency_contract_rejected", 1)
                if bool(record.get("unmet_assembly_bridge")):
                    add_mini_recursive_stat(
                        "plans_unmet_assembly_bridge_rejected",
                        1,
                    )
                if bool(record.get("dependency_contract_suspended")):
                    add_mini_recursive_stat(
                        "dependency_contract_claims_suspended",
                        1,
                    )
                reasons = record.get("reasons") or []
                if any(
                    str(reason or "").startswith("semantic_role_mismatch:")
                    for reason in reasons
                ):
                    key = "mini_recursive_plans_semantic_role_contract_rejected"
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "plan_rejected_unmet_assembly_bridge_all_filtered":
                add_mini_recursive_stat("plans_unmet_assembly_bridge_all_filtered", 1)
            elif verdict == "claim_premise_dependencies_inferred":
                inferred_count = len(record.get("inferred_dependencies") or []) or 1
                add_mini_recursive_stat(
                    "plan_premise_dependencies_inferred",
                    inferred_count,
                )
        elif phase == "mini_recursive_dependency_contract_rehydrate":
            if verdict == "dependency_contract_claims_rehydrated":
                add_mini_recursive_stat(
                    "dependency_contract_claims_rehydrated",
                    int(record.get("claim_count") or 1),
                )
        elif phase == "mini_recursive_unmet_assembly_bridge_recovery":
            if verdict == "bridge_recovery_pass_granted":
                add_mini_recursive_stat(
                    "plans_unmet_assembly_bridge_recovery_passes_granted",
                    1,
                )
        elif phase == "mini_recursive_plan_sanity_contract":
            if (
                verdict == "claim_sanity_contract_diagnostic"
                and str(record.get("policy_disposition") or "")
                == "diagnostic_only"
            ):
                add_mini_recursive_stat("plans_sanity_contract_diagnostics", 1)
                reason = str(record.get("reason") or "")
                reason_stat = {
                    "sanity_check_required": (
                        "plans_sanity_missing_check_diagnostics"
                    ),
                    "missing_sanity_status": (
                        "plans_sanity_missing_status_diagnostics"
                    ),
                    "declared_failed": (
                        "plans_sanity_declared_failure_diagnostics"
                    ),
                    "missing_or_invalid_status": (
                        "plans_sanity_status_conflict_diagnostics"
                    ),
                    "status_without_check": (
                        "plans_sanity_status_conflict_diagnostics"
                    ),
                    "passes_conflicts_with_check": (
                        "plans_sanity_status_conflict_diagnostics"
                    ),
                }.get(reason)
                if reason_stat:
                    add_mini_recursive_stat(reason_stat, 1)
        elif phase == "mini_recursive_plan_sanity":
            if verdict in {
                "claim_rejected_self_refuting_sanity",
                "claim_rejected_self_refuting_sanity_dependency",
                "claim_rejected_self_refuting_dependency",
            }:
                add_mini_recursive_stat("plans_self_refuting_sanity_rejected", 1)
            elif (
                verdict
                in {
                    "claim_diagnosed_self_refuting_sanity",
                    "claim_diagnosed_self_refuting_sanity_dependency",
                }
                and str(record.get("policy_disposition") or "")
                == "diagnostic_only"
            ):
                add_mini_recursive_stat(
                    "plans_self_refuting_sanity_diagnostics", 1
                )
        elif phase == "mini_recursive_plan_counterexample_route":
            if verdict == "plan_rejected_unchecked_counterexample_route":
                rejected_count = int(record.get("claims_rejected") or 1)
                add_mini_recursive_stat(
                    "plans_unchecked_counterexample_rejected",
                    rejected_count,
                )
        elif phase == "mini_recursive_plan_analytic_scope":
            if verdict in {
                "claim_rejected_oversized_analytic_final",
                "claim_rejected_oversized_analytic_dependency",
            }:
                add_mini_recursive_stat("plans_oversized_analytic_rejected", 1)
            if verdict in {
                "claim_rejected_analytic_worksheet_missing",
                "claim_rejected_analytic_worksheet_dependency",
            }:
                add_mini_recursive_stat("plans_analytic_worksheet_rejected", 1)
        elif phase == "mini_recursive_plan":
            if verdict == "plan_compiled":
                add_mini_recursive_stat(
                    "claims_compiled",
                    int(record.get("claims_compiled") or 0),
                )
            elif verdict in {
                "plan_accepted_after_filters",
                "plan_rejected_after_filters",
            }:
                add_mini_recursive_stat(
                    "claims_planned",
                    int(record.get("claims_accepted") or 0),
                )
            if verdict == "no_claims_after_filters":
                add_mini_recursive_stat("plans_no_claims_after_filters", 1)
        elif (
            phase == "mini_recursive_claim"
            and verdict == "claim_exhausted"
            and bool(record.get("bottleneck_obligation_materialized"))
        ):
            add_mini_recursive_stat("bottleneck_obligations_materialized", 1)
        elif (
            phase == "mini_recursive_claim"
            and verdict == "claim_exhausted"
            and bool(record.get("bottleneck_obligation_pending_adjudication"))
        ):
            add_mini_recursive_stat("bottleneck_obligations_pending_adjudication", 1)
        if str(record.get("phase") or "") == "mini_recursive_complete":
            complete_failure_reason = str(
                record.get("failure_reason") or ""
            ).strip()
            # A recursive quantum yield is a bounded scheduler handoff, not a
            # terminal proof-search result. Recording it as the last recursive
            # failure lets a later scheduler terminal inherit a false reason.
            resumable_quantum_yield = is_resumable_mini_recursive_yield(
                complete_failure_reason
            )
            if (
                complete_failure_reason
                and not bool(record.get("ok", False))
                and not resumable_quantum_yield
            ):
                self._metric_snapshot(
                    "mini_recursive_last_failure_reason",
                    complete_failure_reason,
                )
                self._metric_snapshot(
                    "mini_recursive_exit_reason",
                    complete_failure_reason,
                )
                complete_failure_scope = str(
                    record.get("llm_failure_scope") or ""
                ).strip()
                if not complete_failure_scope:
                    complete_failure_scope = llm_failure_scope(complete_failure_reason)
                if (
                    complete_failure_scope == "global"
                    or is_terminal_llm_failure_reason(complete_failure_reason)
                ):
                    self._metric_snapshot(
                        "terminal_proof_search_reason",
                        complete_failure_reason,
                    )
                    self._metric_snapshot(
                        "terminal_proof_search_phase",
                        "mini_recursive_complete",
                    )
            stats = record.get("stats") or {}
            if isinstance(stats, dict):
                complete_totals = {
                    stat_key: max(0, int(stats.get(stat_key, 0) or 0))
                    for stat_key in mini_recursive_stat_mapping
                }
                for stat_key, metric_key in mini_recursive_stat_mapping.items():
                    prior_total = max(
                        0,
                        int(
                            self._last_mini_recursive_complete_totals.get(
                                stat_key,
                                0,
                            )
                            or 0
                        ),
                    )
                    cumulative_delta = max(
                        0,
                        complete_totals[stat_key] - prior_total,
                    )
                    already_counted = max(
                        0,
                        int(
                            self._mini_recursive_incremental_since_complete.get(
                                stat_key,
                                0,
                            )
                            or 0
                        ),
                    )
                    self.metrics[metric_key] = int(
                        self.metrics.get(metric_key, 0) or 0
                    ) + max(0, cumulative_delta - already_counted)
                self._mini_recursive_incremental_since_complete = {}
                self._last_mini_recursive_complete_totals = complete_totals
        if (
            str(record.get("phase") or "") == "session_terminal_failure"
            and str(record.get("session_scope") or "problem") == "problem"
        ):
            terminal_session_reason = str(record.get("reason") or "").strip()
            if terminal_session_reason:
                self._metric_snapshot(
                    "terminal_proof_search_reason",
                    terminal_session_reason,
                )
                self._metric_snapshot(
                    "terminal_proof_search_phase",
                    "session_terminal_failure",
                )
        if phase == "session_no_applicable_recovery":
            if verdict == "repair_restore_failure_selector_reanchored":
                key = "mini_session_no_applicable_repair_restore_reanchors"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict in {
                "continuation_budget_granted",
                "model_call_deferred_action_released",
            }:
                key = "mini_session_no_applicable_recoveries"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "continuation_budget_granted":
                grant_key = "mini_session_no_applicable_budget_granted"
                self.metrics[grant_key] = (
                    int(self.metrics.get(grant_key, 0) or 0)
                    + int(record.get("budget_granted_total") or 0)
                )
            elif verdict in {
                "terminal_no_applicable_action",
                "terminal_repair_policy_narrowing",
            }:
                key = "mini_session_no_applicable_terminal"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "stale_frontier_suppression_released":
                key = "mini_session_no_applicable_suppression_recoveries"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                released_key = (
                    "mini_session_no_applicable_stale_suppressors_released"
                )
                self.metrics[released_key] = (
                    int(self.metrics.get(released_key, 0) or 0)
                    + int(record.get("released_skipped_frontier_work_keys") or 0)
                    + int(record.get("released_skipped_frontier_action_keys") or 0)
                )
            elif verdict == "materialization_pending_suppression_released":
                key = "mini_session_materialization_pending_recoveries"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                released_key = (
                    "mini_session_materialization_pending_suppressors_released"
                )
                self.metrics[released_key] = (
                    int(self.metrics.get(released_key, 0) or 0)
                    + int(
                        record.get(
                            "released_materialization_pending_action_keys"
                        )
                        or 0
                    )
                )
            elif verdict == "repair_policy_yielded_to_child_adaptive_fallback":
                key = "mini_session_repair_policy_child_adaptive_fallback_yields"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict in {
                "terminal_no_applicable_action",
                "terminal_repair_policy_narrowing",
            } and str(record.get("session_scope") or "problem") == "problem":
                terminal_reason = str(
                    record.get("reason")
                    or (
                        "repair_policy_narrowing_no_applicable"
                        if verdict == "terminal_repair_policy_narrowing"
                        else "no_applicable_action"
                    )
                ).strip()
                self._metric_snapshot(
                    "terminal_proof_search_reason",
                    terminal_reason,
                )
                self._metric_snapshot(
                    "terminal_proof_search_phase",
                    "session_no_applicable_recovery",
                )
            if (
                verdict == "terminal_no_applicable_action"
                and record.get("deferred_only_serviceable_action_ids")
            ):
                key = "mini_session_no_applicable_deferred_only_serviceable_work"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_action_outcome"
            and str(record.get("action_id") or "") == "formal_state_search"
        ):
            formal_metric_fields = {
                "formal_invocations": "mini_formal_state_search_invocations",
                "formal_nodes_created": "mini_formal_state_search_nodes_created",
                "formal_nodes_expanded": "mini_formal_state_search_nodes_expanded",
                "formal_lean_checks": "mini_formal_state_search_lean_checks",
                "formal_backtracks": "mini_formal_state_search_backtracks",
                "formal_value_estimates": "mini_formal_state_search_value_estimates",
                "formal_diversity_pruned": "mini_formal_state_search_diversity_pruned",
                "formal_bottleneck_count": "mini_formal_state_search_bottlenecks",
                "formal_root_unlocking_bottleneck_count": (
                    "mini_formal_state_search_root_unlocking_bottlenecks"
                ),
                "formal_operation_timeouts": (
                    "mini_formal_state_search_operation_timeouts"
                ),
                "formal_infrastructure_failures": (
                    "mini_formal_state_search_infrastructure_failures"
                ),
                "formal_completion_rejections": (
                    "mini_formal_state_search_completion_rejections"
                ),
                "formal_candidates_found": (
                    "mini_formal_state_search_candidates_found"
                ),
            }
            for record_key, metric_key in formal_metric_fields.items():
                self._metric_add(metric_key, record.get(record_key))
        if phase == "session_cost_governed_continuation":
            if verdict == "continuation_budget_granted":
                key = "mini_session_cost_governed_continuations"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                grant_key = "mini_session_cost_governed_budget_granted"
                self.metrics[grant_key] = (
                    int(self.metrics.get(grant_key, 0) or 0)
                    + int(record.get("budget_granted_total") or 0)
                )
            elif verdict == "repair_policy_narrowing_released":
                key = "mini_session_cost_governed_repair_policy_released"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "forced_static_conversation_selected":
                key = "mini_session_cost_governed_forced_static_conversation"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "static_dispatch_suppressed_no_serviceable_work":
                key = (
                    "mini_session_cost_governed_static_no_serviceable_work_suppressed"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict in {
                "no_dispatchable_static_llm_lane",
                "forced_static_conversation_unavailable",
            }:
                key = "mini_session_cost_governed_no_dispatch_lane"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "no_cost_budget_capacity":
                key = "mini_session_cost_governed_no_cost_capacity"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "lean_infra_error_cap_deferred":
                key = "mini_session_cost_governed_lean_infra_deferred"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_model_call_deferred_frontier_action"
            and verdict == "selected_action_deferred"
        ):
            key = "mini_session_model_call_deferred_frontier_actions"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        elif (
            phase == "session_model_call_deferred_frontier_action"
            and verdict == "deferred_action_retry_released"
        ):
            key = "mini_session_model_call_deferred_frontier_retry_releases"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        elif (
            phase == "session_model_call_deferred_static_action"
            and verdict == "deferred_static_action_retry_released"
        ):
            key = "mini_session_model_call_deferred_static_retry_releases"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "proof_patch":
            if verdict == "proof_patch_applied":
                key = "mini_session_proof_patches_applied"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if str(record.get("rejection_reason") or "") == "proof_patch_failed":
            key = "mini_session_proof_patch_failures"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if str(record.get("rejection_reason") or "") == "repair_requires_api_search":
            key = "mini_session_unknown_identifier_api_search_policy_rejections"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "post_failure_repair_first"
            and verdict == "deterministic_search_deferred"
        ):
            key = "mini_session_post_failure_repair_first_deferrals"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_local_repair_quota":
            if verdict == "armed":
                key = "mini_session_local_repair_quota_armed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "quota_exhausted":
                key = "mini_session_local_repair_quota_exhausted"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "unscoped_root_quota_suppressed":
                key = "mini_session_local_root_repair_quota_suppressed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "stagnation_fallback_preempted_local_root_repair":
                key = "mini_session_local_root_repair_quota_preempted_by_fallback"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            elif verdict == "scoped_action_selected":
                key = "mini_session_local_repair_quota_scoped_action_selected"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_local_repair_turn"
            and verdict == "conversation_turn_forced"
        ):
            key = "mini_session_local_repair_turns_forced"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_action_outcome":
            if bool(record.get("schedulable_decomposition_created")):
                key = "mini_session_schedulable_decompositions_created"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if bool(record.get("quarantined_residual_diagnostics_created")):
                key = "mini_session_quarantined_residual_diagnostics_created"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_repair_ticket":
            ticket_metric_by_verdict = {
                "created": "mini_session_repair_tickets_created",
                "queued": "mini_session_repair_tickets_queued",
                "promoted": "mini_session_repair_tickets_promoted",
                "conversation_turn_forced": "mini_session_repair_tickets_selected",
                "repair_turn_consumed": "mini_session_repair_tickets_resolved",
                "exhausted": "mini_session_repair_tickets_exhausted",
                "repair_turn_rejected_retry_remaining": (
                    "mini_session_repair_tickets_retry_remaining"
                ),
                "repair_turn_policy_rejected_retry_remaining": (
                    "mini_session_repair_tickets_retry_remaining"
                ),
                "repair_turn_unresolved_retry_remaining": (
                    "mini_session_repair_tickets_retry_remaining"
                ),
                "repair_turn_unresolved_exhausted": (
                    "mini_session_repair_tickets_unresolved_exhausted"
                ),
                "scheduler_blocked_until_repair": (
                    "mini_session_repair_tickets_scheduler_blocked"
                ),
                "blocked_no_conversation_action": (
                    "mini_session_repair_ticket_blocked_no_action"
                ),
                "repeated_repair_failure_observed": (
                    "mini_session_repair_failure_observations"
                ),
                "repeated_repair_target_retired": (
                    "mini_session_repair_targets_retired_repeated_failure"
                ),
                "suppressed_repeated_repair_failure": (
                    "mini_session_repair_tickets_suppressed_repeated_failure"
                ),
                "unscoped_root_repair_replanned": (
                    "mini_session_unscoped_root_repair_replans"
                ),
                "unscoped_root_repair_redirected_to_scope": (
                    "mini_session_unscoped_root_repair_tickets_scope_redirected"
                ),
                "fresh_unscoped_root_repair_ticket_suppressed": (
                    "mini_session_unscoped_root_repair_new_tickets_suppressed"
                ),
                "stagnation_fallback_preempted_unscoped_root_repair": (
                    "mini_session_unscoped_root_repair_tickets_preempted_by_fallback"
                ),
                "unscoped_root_repair_ticket_yielded_to_static_prepass": (
                    "mini_session_unscoped_root_repair_tickets_yielded_to_static_prepass"
                ),
                "scoped_repair_ticket_retained_after_fallback": (
                    "mini_session_scoped_repair_tickets_retained_after_fallback"
                ),
                "stagnation_fallback_preempted_repair_ticket": (
                    "mini_session_repair_tickets_preempted_by_fallback"
                ),
                "target_integrity_repair_ticket_contaminated": (
                    "mini_session_target_integrity_repair_tickets_contaminated"
                ),
                "target_integrity_fresh_repair_ticket_suppressed": (
                    "mini_session_target_integrity_repair_tickets_suppressed"
                ),
            }
            key = ticket_metric_by_verdict.get(verdict)
            if key:
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if (
                    verdict == "unscoped_root_repair_replanned"
                    and bool(record.get("structured_obligation"))
                ):
                    structured_key = (
                        "mini_session_unscoped_root_repair_structured_obligations"
                    )
                    self.metrics[structured_key] = (
                        int(self.metrics.get(structured_key, 0) or 0) + 1
                    )
                if bool(record.get("formalization_duplicate_obligation_reused")):
                    duplicate_key = (
                        "mini_session_graph_formalization_duplicate_obligations_suppressed"
                    )
                    self.metrics[duplicate_key] = (
                        int(self.metrics.get(duplicate_key, 0) or 0) + 1
                    )
            if verdict == "stagnation_fallback_preempted_unscoped_root_repair":
                key = "mini_session_repair_tickets_preempted_by_fallback"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "created" and bool(
                record.get("requires_api_search_for_unknown_identifier")
            ):
                key = "mini_session_unknown_identifier_api_search_required"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if (
                verdict == "created"
                and str(record.get("formalization_failure_class") or "")
                == "code_generation"
            ):
                key = "mini_session_parse_errors_code_generation_failures"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_repair_policy_narrowing"
            and verdict == "scope_materialized"
        ):
            key = "mini_session_repair_policy_scope_materializations"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_repair_policy_narrowing":
            if verdict == "frontier_action_selected":
                key = "mini_session_repair_policy_frontier_selected"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "narrowing_retained_after_no_progress":
                key = (
                    "mini_session_repair_policy_narrowing_retained_after_no_progress"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_root_authoring_gate"
            and verdict == "root_authoring_yielded_to_scoped_frontier"
        ):
            key = "mini_session_root_authoring_yielded_to_scoped_frontier"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_selected_work_liveness"
            and verdict == "terminal_graph_target_suppressed"
        ):
            liveness_status = dict(record.get("liveness_status") or {})
            if str(liveness_status.get("reason") or "") == "promoted_to_proof_state":
                key = "mini_session_promoted_graph_target_restore_suppressed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            key = "mini_session_retired_graph_target_restore_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            key = "mini_session_terminal_graph_target_suppressed_by_reason"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            context = str(record.get("context") or "")
            context_metric = {
                "repair_ticket": (
                    "mini_session_retired_graph_target_repair_ticket_suppressed"
                ),
                "repair_ticket_register": (
                    "mini_session_retired_graph_target_repair_ticket_suppressed"
                ),
                "repair_policy_narrowing": (
                    "mini_session_retired_graph_target_repair_policy_suppressed"
                ),
                "local_repair_quota": (
                    "mini_session_retired_graph_target_local_repair_suppressed"
                ),
                "policy_repair_redirect": (
                    "mini_session_retired_graph_target_policy_redirect_suppressed"
                ),
                "formalization_helper_contract": (
                    "mini_session_retired_graph_target_formalization_suppressed"
                ),
                "frontier_selection": (
                    "mini_session_retired_graph_target_frontier_suppressed"
                ),
            }.get(context)
            if context_metric:
                self.metrics[context_metric] = (
                    int(self.metrics.get(context_metric, 0) or 0) + 1
                )
        if (
            phase == "session_selected_work_liveness"
            and verdict == "terminal_graph_target_repair_bypass_deduped"
        ):
            key = "mini_session_terminal_graph_target_repair_bypass_deduped"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_selected_work_liveness"
            and verdict == "terminal_graph_target_repair_bypassed"
        ):
            key = "mini_session_terminal_graph_target_repair_bypassed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            context = str(record.get("context") or "")
            context_metric = {
                "repair_ticket": (
                    "mini_session_terminal_graph_target_repair_ticket_bypassed"
                ),
                "repair_ticket_register": (
                    "mini_session_terminal_graph_target_repair_ticket_bypassed"
                ),
                "local_repair_quota": (
                    "mini_session_terminal_graph_target_local_repair_bypassed"
                ),
                "local_repair_quota_scoped_action": (
                    "mini_session_terminal_graph_target_local_repair_bypassed"
                ),
            }.get(context)
            if context_metric:
                self.metrics[context_metric] = (
                    int(self.metrics.get(context_metric, 0) or 0) + 1
                )
        if phase == "session_graph_policy_failure":
            key = "mini_session_graph_policy_failures_observed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "graph_policy_target_retired":
                key = "mini_session_graph_policy_targets_retired"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_repair_ticket"
            and verdict == "repeated_repair_target_retired"
            and bool(record.get("materialized_decomposition"))
        ):
            key = "mini_session_repair_retirement_decomposition_materialized"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "graph_native_formalization"
            or verdict == "graph_native_formalization_bridge_rejected"
            or verdict == "graph_native_formalization_bridge_support_recorded"
        ):
            if verdict == "graph_native_formalization_bridge_rejected":
                key = "mini_session_graph_formalization_bridge_rejected"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "graph_native_formalization_bridge_support_recorded":
                key = "mini_session_graph_formalization_bridge_support_recorded"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(
                    record.get("route_support_only_helper")
                    or record.get("hidden_route_support_helper_names")
                ):
                    key = (
                        "mini_session_graph_formalization_route_support_helpers_hidden"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                bridge_status = record.get("formalization_bridge_status")
                if not isinstance(bridge_status, dict):
                    bridge_status = {}
                if bool(
                    bridge_status.get("requires_parent_assembly")
                    or record.get("formalization_bridge_parent_assembly_required")
                ):
                    key = (
                        "mini_session_graph_formalization_bridge_parent_assembly_required"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("formalization_bridge_parent_work_materialized")):
                    key = (
                        "mini_session_graph_formalization_bridge_parent_work_materialized"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("formalization_bridge_parent_work_missing")):
                    key = "mini_session_graph_formalization_bridge_parent_work_missing"
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                if bool(record.get("formalization_bridge_parent_assembly_scheduled")):
                    key = (
                        "mini_session_graph_formalization_bridge_parent_assembly_scheduled"
                    )
                    self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if (
                verdict
                == "graph_native_formalization_bridge_support_reselected_without_parent_work"
            ):
                key = (
                    "mini_session_graph_formalization_bridge_support_reselected_without_parent_work"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if verdict == "graph_native_formalization_repeated_bridge_suppressed":
                key = "mini_session_graph_formalization_repeated_bridge_suppressed"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if verdict == "graph_native_statement_type_rejected":
            key = "mini_session_graph_native_statement_type_rejected"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_root_finalization":
            verdict_text = str(record.get("verdict") or "").strip()
            if "accepted" not in record and verdict_text not in {
                "root_finalization_accepted",
                "root_finalization_blocked",
            }:
                accepted = None
            elif verdict_text == "root_finalization_accepted":
                accepted = True
            elif verdict_text == "root_finalization_blocked":
                accepted = False
            else:
                accepted = bool(record.get("accepted"))
        if phase == "session_root_finalization" and accepted is not None:
            scope = str(record.get("session_scope") or "").strip()
            problem_scope = scope in {"", "problem"}
            if problem_scope:
                key = (
                    "mini_problem_root_finalization_accepted"
                    if accepted
                    else "mini_problem_root_finalization_blocked"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
                legacy_key = (
                    "mini_root_finalization_accepted"
                    if accepted
                    else "mini_root_finalization_blocked"
                )
                self.metrics[legacy_key] = int(self.metrics.get(legacy_key, 0) or 0) + 1
            else:
                key = (
                    "mini_subgoal_root_finalization_accepted"
                    if accepted
                    else "mini_subgoal_root_finalization_blocked"
                )
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "post_failure_giveup_suppressed"
            and verdict == "local_repair_takes_precedence"
        ):
            key = "mini_session_local_repair_giveup_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "target_integrity_signal" and verdict == "detected":
            key = "mini_session_target_integrity_signals"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            kind = str(record.get("kind") or "").strip()
            metric_by_kind = {
                "fake_contradiction_commentary": (
                    "mini_session_target_integrity_fake_contradiction_detected"
                ),
                "unverified_target_refutation": (
                    "mini_session_target_integrity_unverified_refutation_detected"
                ),
                "semantic_bridge_direction": (
                    "mini_session_target_integrity_semantic_bridge_direction_detected"
                ),
            }
            kind_key = metric_by_kind.get(kind)
            if kind_key:
                self.metrics[kind_key] = int(self.metrics.get(kind_key, 0) or 0) + 1
            if str(record.get("source") or "") == "no_proof_extracted":
                key = "mini_session_target_integrity_no_proof_signals"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "target_integrity_local_repair"
            and verdict == "local_repair_bypassed"
        ):
            key = "mini_session_target_integrity_local_repair_bypassed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "target_integrity_proof_state_repair"
            and verdict == "proof_state_repair_bypassed"
        ):
            key = "mini_session_target_integrity_proof_state_repair_bypassed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "target_integrity_adjudication"
            and verdict == "materialized"
        ):
            key = "mini_session_target_integrity_adjudication_materialized"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
            if str(record.get("source") or "") == "no_proof_extracted":
                key = "mini_session_target_integrity_no_proof_adjudication_materialized"
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if bool(record.get("target_integrity_adjudication_progress_suppressed")):
            key = "mini_session_target_integrity_adjudication_progress_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "graph_native_formalization"
            and verdict == "graph_native_formalization_bridge_rejected"
            and str(record.get("lean_error_type") or "")
            == "negative_evidence_bridge_support"
        ):
            key = "mini_session_graph_formalization_negative_bridge_support_rejected"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "soft_progress_streak_saturated"
            and verdict == "soft_progress_treated_as_stagnation"
        ):
            key = "mini_session_soft_progress_streak_saturated"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_assemble_route_static_fallback"
            and verdict == "conversation_suppressed"
        ):
            key = "mini_session_assemble_route_static_conversation_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if (
            phase == "session_root_authoring_gate"
            and verdict == "unscoped_root_authoring_suppressed"
        ):
            key = "mini_session_unscoped_root_authoring_suppressed"
            self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1
        if phase == "session_ready_root_route_drain":
            route_drain_metric_by_verdict = {
                "ready_root_route_drain_selected": (
                    "mini_session_ready_root_route_drain_selected"
                ),
                "ready_root_route_drain_budget_exhausted": (
                    "mini_session_ready_root_route_drain_budget_blocked"
                ),
                "ready_root_route_drain_not_applicable": (
                    "mini_session_ready_root_route_drain_not_applicable"
                ),
                "ready_root_route_drain_headroom_granted": (
                    "mini_session_ready_root_route_drain_headroom_granted"
                ),
            }
            key = route_drain_metric_by_verdict.get(verdict)
            if key:
                self.metrics[key] = int(self.metrics.get(key, 0) or 0) + 1

    def _record_compute_receipt_metrics(self, record: Dict[str, Any]) -> None:
        logs = record.get("tool_call_log") or record.get("mini_tool_call_log") or ()
        if not isinstance(logs, (list, tuple)):
            return
        for receipt in logs:
            if not isinstance(receipt, dict) or receipt.get("name") != "compute_examples":
                continue
            if not bool(receipt.get("runner_invoked")):
                continue
            identity = ":".join(
                str(value or "")
                for value in (
                    record.get("action_dispatch_id")
                    or record.get("session_activation_id"),
                    receipt.get("tool_call_id"),
                    receipt.get("raw_arguments_sha256"),
                    receipt.get("result_sha256"),
                )
            )
            if identity in self._compute_receipt_metric_seen:
                continue
            self._compute_receipt_metric_seen.add(identity)
            self.metrics["mini_compute_examples_calls"] += 1
            try:
                query_count = max(0, int(receipt.get("query_count", 0) or 0))
            except (TypeError, ValueError):
                query_count = 0
            self.metrics["mini_compute_examples_queries"] += query_count
            result_status = str(receipt.get("result_status") or "").strip()
            metric = (
                "mini_compute_examples_successes"
                if result_status == "accepted"
                else "mini_compute_examples_rejected"
                if result_status == "rejected"
                else "mini_compute_examples_errors"
            )
            self.metrics[metric] += 1

    def _metric_add(self, key: str, value: Any) -> None:
        if value is None:
            return
        try:
            amount = float(value) if isinstance(value, float) else int(value)
        except Exception:
            return
        current = self.metrics.get(key, 0.0 if isinstance(amount, float) else 0)
        try:
            self.metrics[key] = current + amount
        except Exception:
            self.metrics[key] = amount

    def _metric_snapshot(self, key: str, value: Any) -> None:
        if value is None:
            return
        self.metrics[key] = value

    def _record_llm_usage_metrics(self, record: Dict[str, Any]) -> None:
        verdict = str(record.get("verdict") or "")
        if verdict == "cost_budget_rejected":
            self._metric_add("llm_budget_rejections", 1)
            for key in (
                "max_cost_usd",
                "cost_usd",
                "estimated_unknown_cost_usd",
                "llm_budget_accounted_cost_usd",
                "llm_budget_committed_cost_usd",
                "llm_budget_remaining_usd",
            ):
                self._metric_snapshot(key, record.get(key))
            terminal = bool(record.get("budget_rejection_terminal"))
            exhausted = terminal and str(
                record.get("budget_rejection_reason") or ""
            ) in {
                "llm_cost_budget_exhausted",
                "llm_cost_budget_unknown_pricing",
                "cost_budget_exhausted",
                "unknown_pricing",
            }
            self._metric_snapshot("llm_cost_budget_exhausted", exhausted)
            reason = str(record.get("budget_rejection_reason") or "").strip()
            if terminal and reason:
                self._metric_snapshot(
                    "llm_cost_budget_terminal_reason",
                    (
                        "llm_cost_budget_unknown_pricing"
                        if reason == "unknown_pricing"
                        else "llm_cost_budget_exhausted"
                        if reason == "cost_budget_exhausted"
                        else reason
                    ),
                )
            return
        if verdict not in {"llm_usage_recorded", "llm_usage_missing"}:
            return
        self._metric_add("llm_usage_events", 1)
        self._metric_add("llm_calls", 1)
        status = str(record.get("status") or "").strip()
        error = str(record.get("error") or "").strip()
        self._metric_snapshot("llm_usage_last_verdict", verdict)
        self._metric_snapshot("llm_usage_last_status", status)
        if error:
            self._metric_snapshot("llm_usage_last_error", error[:1000])
        if verdict == "llm_usage_missing":
            self._metric_add("llm_usage_missing_events", 1)
            if status == "cancelled":
                self._metric_add("llm_usage_cancelled_events", 1)
            elif status == "cancelled_provider_inflight":
                self._metric_add("llm_cancelled_provider_inflight_events", 1)
                self._metric_add(
                    "llm_cancelled_provider_inflight_estimated_cost_usd",
                    record.get("estimated_cost_usd"),
                )
            elif status == "exception":
                self._metric_add("llm_usage_exception_events", 1)
            elif status == "retryable_exception_no_charge":
                self._metric_add("llm_retryable_exception_no_charge_events", 1)
        if not bool(record.get("pricing_known", True)):
            self._metric_add("llm_pricing_unknown_events", 1)
        if bool(record.get("openrouter_affordability_retry")):
            self._metric_add("llm_openrouter_affordability_retries", 1)
        if record.get("temperature_requested") is not None:
            self._metric_add("llm_temperature_requests", 1)
            phase_key = str(record.get("temperature_phase_key") or "").strip()
            if phase_key:
                by_phase = self.metrics.get("llm_temperature_by_phase")
                if not isinstance(by_phase, dict):
                    by_phase = {}
                bucket = dict(by_phase.get(phase_key) or {})
                bucket["requests"] = int(bucket.get("requests", 0) or 0) + 1
                if record.get("temperature_sent") is not None:
                    bucket["effective_calls"] = (
                        int(bucket.get("effective_calls", 0) or 0) + 1
                    )
                if bool(record.get("temperature_provider_dropped")):
                    bucket["provider_dropped"] = (
                        int(bucket.get("provider_dropped", 0) or 0) + 1
                    )
                by_phase[phase_key] = bucket
                self.metrics["llm_temperature_by_phase"] = by_phase
        if record.get("temperature_sent") is not None:
            self._metric_add("llm_temperature_effective_calls", 1)
        if bool(record.get("temperature_provider_dropped")):
            self._metric_add("llm_temperature_provider_dropped", 1)
        for key in (
            "input_tokens",
            "output_tokens",
            "cached_input_tokens",
            "cache_write_tokens",
            "prompt_cache_miss_tokens",
            "reasoning_output_tokens",
            "cost_usd",
            "estimated_unknown_cost_usd",
        ):
            self._metric_add(key, record.get(key))
        role = _canonical_llm_usage_role(str(record.get("role") or ""))
        if role:
            for key in (
                "input_tokens",
                "output_tokens",
                "cached_input_tokens",
                "cache_write_tokens",
                "prompt_cache_miss_tokens",
                "reasoning_output_tokens",
                "cost_usd",
                "estimated_unknown_cost_usd",
            ):
                self._metric_add(f"{role}_{key}", record.get(key))
            observations = record.get("provider_observations")
            if isinstance(observations, list) and observations:
                last = observations[-1]
                if isinstance(last, dict):
                    self._metric_snapshot(f"{role}_model", last.get("model"))
        for key in (
            "max_cost_usd",
            "llm_budget_accounted_cost_usd",
            "llm_budget_committed_cost_usd",
            "llm_budget_remaining_usd",
            "llm_cost_budget_exhausted",
        ):
            self._metric_snapshot(key, record.get(key))

    def record_turn(self, record: Dict[str, Any]) -> None:
        recovery_event_id = (
            str(record.get("llm_recovery_event_id") or "").strip()
            if isinstance(record.get("llm_recovery_event_id"), str)
            else ""
        )
        if (
            recovery_event_id
            and recovery_event_id in self._recovery_event_ids_seen
        ):
            return
        self._turns_fp.flush()
        trace_start = int(os.fstat(self._turns_fp.fileno()).st_size)
        next_turn_index = self.turn_count + 1
        payload = dict(record)
        payload.pop("turn_index", None)
        payload.pop("ts", None)
        payload.pop("elapsed_s", None)
        now = time.time()
        elapsed_s = max(
            float(self._last_elapsed_s or 0.0),
            round(now - self.start_ts, 3),
        )
        record = {
            "turn_index": next_turn_index,
            "ts": now,
            "elapsed_s": elapsed_s,
            **payload,
        }
        prior_metrics = self.metrics
        prior_incremental = self._mini_recursive_incremental_since_complete
        prior_complete_totals = self._last_mini_recursive_complete_totals
        prior_banked_seen = self._formalization_banked_helper_metric_seen
        prior_compute_seen = self._compute_receipt_metric_seen
        self.metrics = copy.deepcopy(prior_metrics)
        self._mini_recursive_incremental_since_complete = dict(prior_incremental)
        self._last_mini_recursive_complete_totals = dict(
            prior_complete_totals
        )
        self._formalization_banked_helper_metric_seen = set(prior_banked_seen)
        self._compute_receipt_metric_seen = set(prior_compute_seen)
        append_started = False
        try:
            self._record_policy_metrics(record)
            self._record_structural_metrics(record)
            encoded_line = json.dumps(record, ensure_ascii=False) + "\n"
            append_started = True
            self._turns_fp.write(encoded_line)
            self._turns_fp.flush()
            if recovery_event_id:
                # Recovery usage is a crash-sensitive accounting receipt.
                # Make the complete row durable before acknowledging it.
                os.fsync(self._turns_fp.fileno())
        except BaseException:
            self.metrics = prior_metrics
            self._mini_recursive_incremental_since_complete = prior_incremental
            self._last_mini_recursive_complete_totals = prior_complete_totals
            self._formalization_banked_helper_metric_seen = prior_banked_seen
            self._compute_receipt_metric_seen = prior_compute_seen
            if append_started:
                try:
                    self._turns_fp.close()
                except BaseException:
                    pass
                turns_path = self.output_dir / "turns.jsonl"
                with turns_path.open("r+b") as handle:
                    handle.truncate(trace_start)
                    handle.flush()
                    os.fsync(handle.fileno())
                self._turns_fp = turns_path.open("a", encoding="utf-8")
            raise
        self.turn_count = next_turn_index
        self._last_elapsed_s = elapsed_s
        self._turns_hasher.update(encoded_line.encode("utf-8"))
        if recovery_event_id:
            self._recovery_event_ids_seen.add(recovery_event_id)
        try:
            self._write_live_trace(record)
        except Exception:
            # Console heartbeat rendering is secondary to the durable trace
            # and must not make the controller retry a committed sink event.
            pass

    def _write_live_trace(self, record: Dict[str, Any]) -> None:
        """Emit a compact console heartbeat for structured recorder events.

        Legacy ``run_conversation`` printed its assistant replies and Lean
        checks directly. The MiniSession path moved most of that activity into
        JSONL recorder events, which made the CLI look frozen during long
        turns. Keep the machine-readable trace as the source of truth, but
        mirror the important records to stdout/run.log in real time.
        """

        try:
            if self.live_trace_mode == "off":
                return
            if self.live_trace_mode == "jsonl":
                print(json.dumps(record, ensure_ascii=False), flush=True)
                return
            lines = self._live_trace_lines(record)
            if not lines:
                return
            for line in lines:
                print(line, flush=True)
        except Exception:
            # Observability must never perturb proof search.
            return

    def _live_trace_lines(self, record: Dict[str, Any]) -> List[str]:
        phase = str(record.get("phase") or "")
        verdict = str(record.get("verdict") or "")
        action_id = str(record.get("action_id") or "")
        elapsed = record.get("elapsed_s")
        elapsed_part = f" t={elapsed}s" if elapsed is not None else ""

        if phase == "session_iteration":
            return [
                "[session]"
                f"{elapsed_part} iter={record.get('iteration')}"
                f" stagnation={record.get('stagnation_counter')}"
                f" applicable={record.get('applicable_action_count')}"
            ]

        if phase == "session_pre_select_snapshot" and verdict == "pre_select_snapshot_failed":
            snapshot = record.get("snapshot") or {}
            error = ""
            if isinstance(snapshot, dict):
                error = str(snapshot.get("error") or snapshot.get("snapshot_error") or "")
            error_part = f" error={error}" if error else ""
            return [
                f"[session_pre_select_snapshot]{elapsed_part}"
                f" verdict={verdict}{error_part}"
            ]

        if phase == "session_pre_select_snapshot":
            return []

        if phase == "session_action_selected":
            target = record.get("selected_work_item") or {}
            target_bits: List[str] = []
            if isinstance(target, dict):
                for key in ("work_type", "node_id", "source", "assembly_id"):
                    value = str(target.get(key) or "").strip()
                    if value:
                        target_bits.append(f"{key}={value}")
            target_part = " " + " ".join(target_bits) if target_bits else ""
            return [
                "=== session"
                f"{elapsed_part} iter={record.get('iteration')}"
                f" action={action_id or '?'}{target_part} ==="
            ]

        if phase in {"session_action_outcome", "session_subaction_outcome"}:
            lean_bits: List[str] = []
            lean_verdict = str(record.get("lean_verdict") or "").strip()
            if lean_verdict:
                lean_bits.append(f"lean={lean_verdict}")
            lean_error = str(record.get("lean_error_type") or "").strip()
            if lean_error:
                lean_bits.append(f"error={lean_error}")
            lean_elapsed = record.get("lean_elapsed_s")
            if lean_elapsed is not None:
                lean_bits.append(f"lean_time={lean_elapsed}s")
            if action_id == "formal_state_search":
                if bool(record.get("formal_rank_improved")):
                    lean_bits.append("formal=rank")
                elif bool(record.get("formal_progress_improved")):
                    lean_bits.append("formal=novelty")
                elif bool(record.get("formal_context_stalled")):
                    lean_bits.append("formal=stalled")
                else:
                    lean_bits.append("formal=none")
                misses = record.get("formal_no_improvement_quanta")
                limit = record.get("formal_no_improvement_limit")
                if misses is not None and limit is not None:
                    lean_bits.append(f"no_improve={misses}/{limit}")
            lean_part = " " + " ".join(lean_bits) if lean_bits else ""
            return [
                "=== session"
                f"{elapsed_part} action={action_id or '?'}"
                f" solved={bool(record.get('solved'))}"
                f" progress={bool(record.get('progress'))}"
                f" helpers={record.get('helpers_added_count', 0)}"
                f" cost={record.get('cost_seconds')}s"
                f"{lean_part}"
                f" verdict={verdict or 'outcome'} ==="
            ]

        lines: List[str] = []
        if verdict:
            turn = record.get("turn_in_phase")
            turn_part = f" turn={turn}" if turn is not None else ""
            error = ""
            analysis = record.get("lean_failure_analysis")
            if isinstance(analysis, dict):
                error_type = str(analysis.get("error_type") or "").strip()
                if error_type:
                    error = f" error={error_type}"
            if not error:
                lean_error = str(record.get("lean_error_type") or "").strip()
                if lean_error:
                    error = f" error={lean_error}"
            rejection_reason = str(record.get("rejection_reason") or "").strip()
            reason_part = f" reason={rejection_reason}" if rejection_reason else ""
            helpers = record.get("helpers_added_count")
            helper_part = f" helpers={helpers}" if helpers is not None else ""
            tools = record.get("tool_calls_used")
            tools_part = f" tools={tools}" if tools is not None else ""
            lean_elapsed = record.get("lean_elapsed_s")
            lean_part = f" lean={lean_elapsed}s" if lean_elapsed is not None else ""
            scope = str(record.get("session_scope") or "").strip()
            phase_label = phase or "record"
            if scope and scope != "problem":
                phase_label = f"{scope} {phase_label}"
            lines.append(
                f"[{phase_label}]{elapsed_part}{turn_part}"
                f" verdict={verdict}{error}{reason_part}{helper_part}{tools_part}{lean_part}"
            )

        # MiniSession conversation turns do not otherwise print assistant
        # content. Avoid duplicating legacy run_conversation, which still
        # prints assistant text directly and has no ``session_scope`` field.
        should_print_llm_response = (
            isinstance(record.get("llm_response"), str)
            and (
                self.live_trace_mode == "full"
                or (
                    bool(record.get("session_scope"))
                    and (
                        verdict == "llm_response"
                        or not bool(record.get("llm_response_recorded"))
                    )
                )
            )
        )
        if should_print_llm_response:
            content = str(record.get("llm_response") or "")
            if content.strip():
                llm_elapsed = record.get("llm_elapsed_s")
                llm_part = f", {llm_elapsed}s" if llm_elapsed is not None else ""
                lines.append(f"  assistant ({len(content)} chars{llm_part}):")
                limit = self.live_trace_response_chars
                preview = content if limit is None else content[:limit]
                lines.extend(f"    {line}" for line in preview.splitlines())
                if limit is not None and len(content) > len(preview):
                    lines.append(f"    ...({len(content) - len(preview)} more chars)")

        return lines

    def write_summary(self, summary: Dict[str, Any]) -> None:
        problem_root_finalization_observed = any(
            int(self.metrics.get(key, 0) or 0) > 0
            for key in (
                "mini_problem_root_finalization_accepted",
                "mini_problem_root_finalization_blocked",
            )
        )
        subgoal_root_finalization_observed = any(
            int(self.metrics.get(key, 0) or 0) > 0
            for key in (
                "mini_subgoal_root_finalization_accepted",
                "mini_subgoal_root_finalization_blocked",
            )
        )
        root_finalization_outcome_keys = {
            "mini_root_finalization_accepted",
            "mini_root_finalization_blocked",
        }
        if subgoal_root_finalization_observed:
            for metric_key in _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS:
                if (
                    metric_key.startswith("mini_root_finalization_")
                    and metric_key not in root_finalization_outcome_keys
                ):
                    self.metrics[metric_key] = 0
        for key in _MINI_DOSSIER_TOOL_METRIC_EXPORT_KEYS:
            if key in summary:
                if (
                    key.startswith("mini_root_finalization_")
                    and (problem_root_finalization_observed or subgoal_root_finalization_observed)
                    and (
                        subgoal_root_finalization_observed
                        or (
                            key not in root_finalization_outcome_keys
                            and not problem_root_finalization_observed
                        )
                    )
                ):
                    continue
                current = self.metrics.get(key)
                incoming = summary[key]
                if isinstance(current, (int, float)) and isinstance(
                    incoming, (int, float)
                ):
                    self.metrics[key] = max(current, incoming)
                else:
                    self.metrics[key] = incoming
                if (
                    not subgoal_root_finalization_observed
                    and isinstance(incoming, (int, float))
                    and key
                    in {
                        "mini_root_finalization_accepted",
                        "mini_root_finalization_blocked",
                    }
                ):
                    problem_key = key.replace(
                        "mini_root_finalization_",
                        "mini_problem_root_finalization_",
                        1,
                    )
                    self.metrics[problem_key] = max(
                        int(self.metrics.get(problem_key, 0) or 0),
                        int(incoming or 0),
                    )
        metrics_for_summary = dict(self.metrics)
        for key in list(metrics_for_summary):
            if key in summary and _is_llm_usage_summary_key(key):
                metrics_for_summary.pop(key, None)
        self._log_fp.flush()
        self._turns_fp.flush()
        os.fsync(self._log_fp.fileno())
        os.fsync(self._turns_fp.fileno())
        _fsync_directory(self.output_dir)
        base_summary = {
            **summary,
            **metrics_for_summary,
            "wall_clock_s": round(time.time() - self.start_ts, 3),
            "total_turns": self.turn_count,
        }
        activation_summary: Dict[str, Any]
        try:
            activation_summary = compact_activation_summary(
                build_activation_telemetry_for_run(
                    self.output_dir,
                    summary=base_summary,
                )
            )
        except Exception as exc:
            activation_summary = {
                "activation_schema_version": 1,
                "error": f"{type(exc).__name__}: {exc}",
            }
        final_summary = {
            **base_summary,
            "activation_telemetry": activation_summary,
        }
        summary_path = self.output_dir / "summary.json"
        _write_json_atomic(summary_path, final_summary)
        try:
            artifact = write_activation_telemetry_for_run(
                self.output_dir,
                summary=final_summary,
            )
            artifact_summary = compact_activation_summary(artifact)
            if artifact_summary != final_summary["activation_telemetry"]:
                final_summary["activation_telemetry"] = artifact_summary
                _write_json_atomic(summary_path, final_summary)
                write_activation_telemetry_for_run(
                    self.output_dir,
                    summary=final_summary,
                )
        except Exception as exc:
            final_summary["activation_telemetry"] = {
                "activation_schema_version": 1,
                "error": f"{type(exc).__name__}: {exc}",
            }
            _write_json_atomic(summary_path, final_summary)

    def close(self) -> None:
        sys.stdout = self._orig_stdout
        sys.stderr = self._orig_stderr
        try:
            self._log_fp.close()
        except Exception:
            pass
        try:
            self._turns_fp.close()
        except Exception:
            pass
