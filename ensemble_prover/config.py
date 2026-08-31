"""Configuration models, loading, normalization, and validation."""

from __future__ import annotations

import logging
import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

import yaml

from .pricing import (
    base_url_matches_provider,
    lookup_known_token_pricing,
    provider_for_base_url,
)

logger = logging.getLogger(__name__)
_LEAN_IMPORT_RE = re.compile(r"^(?:import\s+)?[A-Za-z_][A-Za-z0-9_.]*$")
_PACKAGE_ROOT = Path(__file__).resolve().parent.parent


# ── Config inheritance ────────────────────────────────────────────────


class ConfigError(ValueError):
    """Raised when configuration validation fails."""


def _resolve_lean_scratch_root(cfg: Any) -> Path:
    """Resolve the configured Lean scratch root without coercing arbitrary objects.

    ``LeanConfig.scratch_dir`` is a string. Treat every other runtime value as
    missing so mocks and malformed descriptors cannot become literal
    cwd-relative paths.
    """
    project_dir = Path(cfg.project_dir).resolve()
    raw_scratch = getattr(cfg, "scratch_dir", "")
    if type(raw_scratch) is str:
        configured_scratch = raw_scratch.strip()
    else:
        configured_scratch = ""
    if not configured_scratch:
        return project_dir / "Temp"
    return Path(configured_scratch).expanduser().resolve()


def _deep_merge(base: dict, override: dict) -> dict:
    """Recursively merge *override* into *base* (new dict, no mutation).

    Rules:
      - Dict values are merged recursively.
      - ``null`` in override removes the key entirely.
      - All other values in override replace the base value.
    """
    result = dict(base)
    for key, val in override.items():
        if val is None:
            result.pop(key, None)
        elif isinstance(val, dict) and isinstance(result.get(key), dict):
            result[key] = _deep_merge(result[key], val)
        else:
            result[key] = val
    return result


def _resolve_inheritance(
    data: dict, config_path: Path, _chain: tuple[str, ...] = ()
) -> dict:
    """Resolve ``_base`` inheritance in a YAML config dict.

    If *data* contains a ``_base`` key, load that file, resolve ITS inheritance
    recursively, then deep-merge the current data on top.

    Cycle detection: *_chain* tracks visited files (max depth 5).
    """
    base_ref = data.pop("_base", None)
    if base_ref is None:
        return data

    # Resolve relative to the config file's directory.
    base_path = (config_path.parent / base_ref).resolve()
    base_key = str(base_path)

    if base_key in _chain:
        raise ConfigError(
            f"Circular config inheritance: {' → '.join(_chain)} → {base_key}"
        )
    if len(_chain) >= 5:
        raise ConfigError(f"Config inheritance too deep (max 5): {' → '.join(_chain)}")

    if not base_path.exists():
        raise ConfigError(f"Base config not found: {base_path}")

    base_data = yaml.safe_load(base_path.read_text())
    if not isinstance(base_data, dict):
        raise ConfigError(f"Base config is not a YAML mapping: {base_path}")

    # Recursively resolve the base's own _base.
    base_data = _resolve_inheritance(base_data, base_path, _chain + (base_key,))

    return _deep_merge(base_data, data)


def _as_int(value: Any, default: int) -> int:
    """Parse int safely from YAML values (handles None from explicit ``null``)."""
    if value is None:
        return int(default)
    return int(value)


def _as_float(value: Any, default: float) -> float:
    """Parse float safely from YAML values (handles None from explicit ``null``)."""
    if value is None:
        return float(default)
    return float(value)


def _as_bool(value: Any, default: bool = False) -> bool:
    """Parse booleans safely from YAML/env-style values."""
    if value is None:
        return bool(default)
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        s = value.strip().lower()
        if s in {"1", "true", "yes", "on", "y"}:
            return True
        if s in {"0", "false", "no", "off", "n", ""}:
            return False
    return bool(value)


def _as_str_list(value: Any, default: Optional[Sequence[str]] = None) -> List[str]:
    """Parse a YAML scalar/list into a normalized string list."""
    if value is None:
        return [str(item) for item in list(default or []) if str(item).strip()]
    if isinstance(value, str):
        return [value] if value.strip() else [str(item) for item in list(default or [])]
    if isinstance(value, Sequence) and not isinstance(value, (bytes, bytearray)):
        return [str(item).strip() for item in value if str(item).strip()]
    return [str(item) for item in list(default or []) if str(item).strip()]


def _as_float_vector_map(value: Any) -> Dict[str, List[float]]:
    """Parse ``{name: [floats...]}`` maps while ignoring malformed entries."""
    if not isinstance(value, dict):
        return {}
    parsed: Dict[str, List[float]] = {}
    for raw_key, raw_vec in value.items():
        key = str(raw_key).strip()
        if not key:
            continue
        if isinstance(raw_vec, Sequence) and not isinstance(raw_vec, (str, bytes, bytearray)):
            try:
                parsed[key] = [float(item) for item in raw_vec]
            except Exception:
                continue
    return parsed


def _resolve_config_path(value: Any, *, config_dir: Path) -> Any:
    """Resolve relative filesystem paths against the config file directory."""
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return text
    path = Path(text).expanduser()
    if path.is_absolute():
        return str(path.resolve())
    return str((config_dir / path).resolve())


def _resolve_existing_root_path(value: Any, *, config_dir: Path) -> Any:
    """Resolve a root directory path with config-dir preference and repo fallback.

    This keeps config-file-relative resolution for real configs while preserving
    legacy behavior for tests and inherited configs that rely on repo-root
    defaults like ``./lean_project`` or ``./external/PutnamBench/lean4``.
    """
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return text
    path = Path(text).expanduser()
    if path.is_absolute():
        return str(path.resolve())

    config_candidate = (config_dir / path).resolve()
    if config_candidate.exists():
        return str(config_candidate)

    package_candidate = (_PACKAGE_ROOT / path).resolve()
    if package_candidate.exists():
        return str(package_candidate)

    cwd_candidate = path.resolve()
    if cwd_candidate.exists():
        return str(cwd_candidate)

    return str(config_candidate)


def _expect_mapping(value: Any, label: str) -> Dict[str, Any]:
    """Require a YAML mapping and raise ConfigError with context when malformed."""
    if isinstance(value, dict):
        return value
    kind = "null" if value is None else type(value).__name__
    raise ConfigError(f"{label}: expected YAML mapping, got {kind}")


def _section_mapping(
    data: Dict[str, Any], key: str, *, required: bool = False
) -> Dict[str, Any]:
    """Return a validated top-level mapping section or `{}` when omitted."""
    if key not in data:
        if required:
            raise ConfigError(f"{key}: missing required YAML mapping")
        return {}
    if data[key] is None and not required:
        return {}
    return _expect_mapping(data[key], key)


def _normalize_import_stmt(text: str) -> str:
    raw = str(text or "").strip()
    if not raw:
        return ""
    return raw if raw.startswith("import ") else f"import {raw}"


def _append_imports_to_preamble(preamble: str, extra_imports: Sequence[str]) -> str:
    base_lines = [
        line.rstrip() for line in str(preamble or "").splitlines() if line.strip()
    ]
    import_indexes = [
        index
        for index, line in enumerate(base_lines)
        if re.match(r"\s*(?:public\s+)?import\s+", line)
    ]
    seen = {base_lines[index].strip() for index in import_indexes}
    additions: List[str] = []
    for extra in extra_imports:
        stmt = _normalize_import_stmt(extra)
        if stmt and stmt not in seen:
            additions.append(stmt)
            seen.add(stmt)
    if not additions:
        return "\n".join(base_lines) if base_lines else ""
    if import_indexes:
        insert_at = import_indexes[-1] + 1
    else:
        header_indexes = [
            index
            for index, line in enumerate(base_lines)
            if line.strip() == "prelude"
            or line.strip() == "module"
            or line.lstrip().startswith("module ")
        ]
        insert_at = header_indexes[-1] + 1 if header_indexes else 0
    merged = list(base_lines)
    merged[insert_at:insert_at] = additions
    return "\n".join(merged)


@dataclass
class RoleConfig:
    name: str
    base_url: str
    model: str
    api_key: Optional[str] = None
    temperature: float = 0.2
    top_p: float = 0.95
    max_tokens: int = 1024
    # Optional lane-level override for MiniSession conversation turns. Unlike
    # ``max_tokens`` (the role default/capacity used by ordinary calls), this
    # value is passed as the concrete request limit and may intentionally raise
    # the bounded graph-work defaults for reasoning-heavy providers.
    conversation_max_tokens_override: Optional[int] = None
    # Optional: context window for prompt budgeting (server-side ctx size).
    # When set, prompts can be trimmed to fit within ctx_size - max_tokens.
    context_window: Optional[int] = None
    # Optional reasoning control for compatible OpenAI/DeepSeek models.
    reasoning_effort: Optional[str] = None
    # When true, unsupported-provider fallback must not silently remove
    # explicit reasoning/thinking controls from requests.
    reasoning_control_required: bool = False
    timeout_s: float = 120
    prompt_style: str = "auto"  # "auto" | "standard"
    weight: float = 1.0  # pool candidate allocation weight (only used by ModelPool)
    # DeepSeek extended thinking. For DeepSeek v4 the provider default remains
    # enabled unless reasoning_control_required marks false as an explicit
    # operator opt-out. Thinking mode disables temperature/top_p and requires
    # reasoning_content replay for tool-call conversations.
    thinking_enabled: bool = False


@dataclass
class LeanConfig:
    project_dir: str
    # Writable scratch root for generated theorem checks. When empty, retain
    # the historical ``<project>/Temp`` location. The theorem-project CLI sets
    # this outside the input project so read-only Lake projects remain valid.
    scratch_dir: str = ""
    # Project-owned modules that theorem-project preflight must build before
    # checking the target.  This is distinct from historical ``extra_imports``
    # (which is a prop_complete compatibility hook).
    project_imports: List[str] = field(default_factory=list)
    # Exact source paths for project-owned import targets.  Preflight uses
    # these to distinguish an already-current read-only build from a missing
    # or stale artifact that genuinely requires ``lake build <Module>``.
    project_import_sources: Dict[str, str] = field(default_factory=dict)
    # External supporting Lake projects and the exact module targets imported
    # from each. Empty target lists request Lake's default build graph.
    support_project_builds: Dict[str, List[str]] = field(default_factory=dict)
    preamble_import: str = "import Mathlib"
    preamble_tactics: str = ""  # Custom Lean tactics/macros appended after imports
    max_parallel: int = 8
    timeout_s: int = (
        45  # Max time for a single Lean check (reduced from 60 for throughput)
    )
    # Silence-based fast-fail threshold for backends that can safely support it.
    # The current Lean subprocess backends are silent on success, so they run in
    # hard-timeout-only mode to avoid premature termination.
    fast_fail_timeout_s: int = 20
    # Enable/disable the fast-fail guard. When disabled, only the hard timeout
    # applies. Current Lean subprocess backends already operate this way.
    fast_fail_enabled: bool = True
    # Candidate verification precheck. This is a short-budget Lean run that
    # rejects only decisive failures by default and never rejects on timeout.
    precheck_mode: str = "typecheck"  # none | typecheck | strict
    precheck_timeout_s: float = 8.0
    precheck_max_heartbeats: int = 120000
    # Static fallback caps when MEO does not provide per-problem overrides.
    # 0 means unlimited / disabled.
    max_full_checks: int = 0
    min_score_full_check: float = -1.0
    # Phase 9: cached lean environment
    # Default to True: this skips per-check `lake env` overhead when possible,
    # and falls back safely if environment resolution fails.
    use_repl: bool = True
    # Verifier backend selection. Existing configs can continue to use
    # `use_repl`; this field provides an explicit rollout surface for the
    # persistent verifier path.
    backend_mode: str = "auto"  # auto | lake | env_cached_subprocess | persistent_process
    persistent_workers: int = 0
    persistent_worker_idle_ttl_s: float = 300.0
    persistent_worker_start_timeout_s: float = 30.0
    persistent_request_timeout_buffer_s: float = 2.0
    persistent_max_requests_per_worker: int = 200
    persistent_oracle_workers: int = 0
    persistent_protocol: str = "lsp"
    solved_dir: str = "./runs/solved/"
    extra_imports: List[str] = field(default_factory=list)
    # Additional roots containing already-compiled Lean modules. Mini's
    # persistent theory store uses this instead of copying artifacts into the
    # active conjecture project.
    module_search_paths: List[str] = field(default_factory=list)
    # Optional exact Lake environment resolved before dynamic module roots are
    # activated. ``lake env`` replaces LEAN_PATH, so callers with external
    # compiled roots use these values to invoke Lean directly.
    resolved_lean_path: str = ""
    resolved_lean_executable: str = ""


@dataclass
class SearchConfig:
    max_depth: int = 3
    max_goals: int = 64
    max_attempts_per_goal: int = 6
    candidates_per_goal: int = 4
    planner_subgoals_max: int = 4
    # Per-problem cap on total planner LLM calls across *all* planner call
    # sites (subgoal planning, proof sketches, NL-to-Lean, rerank, etc.).
    # Acts as a defense-in-depth guard against runaway planner usage.
    planner_llm_calls_budget: int = 60
    # Reserve this many planner calls for subgoal planning (plan_subgoals + its
    # replan/repair retries). When the remaining call budget is <= reserve,
    # non-planning planner calls (sketches, NL-to-Lean, rerank) are blocked.
    planner_llm_calls_reserve_for_plan_subgoals: int = 0
    # Validate planner subgoals are well-typed before adding to scheduler.
    # Adds a quick executable scaffold check per subgoal to reject ill-typed statements.
    # Enabled by default so planner output stays grounded in executable proof state.
    validate_planner_subgoals: bool = True
    # Retrieval-first planner pass: ask the planner to name 2-5 Mathlib lemmas
    # that are the crux of the proof and write a complete proof around them.
    # Runs BEFORE the direct-proof attempt. Plain-text output (no JSON) so
    # reasoning models spend their budget on math, not schema compliance.
    retrieval_first_proof_enabled: bool = True
    retrieval_first_proof_max_rounds: int = 2
    retrieval_first_proof_timeout_s: float = 90.0
    # Proof-generation calls must be bounded independently from model role
    # defaults. Some providers expose very large output windows; without a
    # lane-local cap, retrieval/finalize/direct proof attempts can spend many
    # minutes generating prose before Lean sees a candidate.
    proof_generation_max_tokens: int = 8192
    proof_generation_timeout_s: float = 300.0
    retrieval_first_proof_max_tokens: int = 6144
    retrieval_first_proof_call_timeout_s: float = 300.0
    tool_finalize_max_tokens: int = 8192
    tool_finalize_timeout_s: float = 360.0
    recursive_direct_proof_max_tokens: int = 6144
    recursive_direct_proof_timeout_s: float = 300.0
    # Semantic prover fallback is distinct from provider fallback: for root
    # proofs, query multiple configured prover backends and let Lean decide
    # between their candidates. Without this, a secondary "fallback" model only
    # fires when the primary API call fails, not when Lean rejects the proof.
    prover_semantic_fallback_enabled: bool = True
    prover_semantic_fallback_root_only: bool = True
    prover_semantic_fallback_max_backends: int = 2
    # When the planner emits only natural-language subgoals instead of Lean
    # propositions, allow feeding them into later validation as a
    # compatibility fallback. Disabled by default to avoid fail-open drift.
    planner_allow_informal_fallback: bool = False
    # When all planner subgoals fail validation, optionally keep them anyway.
    # Disabled by default to avoid fail-open admission.
    planner_allow_unvalidated_fallback: bool = False
    # When all planner subgoals fail validation, attempt a repair call by default.
    planner_repair_on_all_failed: bool = True
    # Prefix planner subgoals with binders from the root statement to close
    # over implicit variables and reduce free-identifier drift.
    planner_contextualize_subgoals: bool = True
    planner_contextualize_max_chars: int = 256
    # Context-closed subgoal compiler: generate binder-closed variants before
    # scheduling/validation so unknown local variables can be captured rather
    # than dropped as ill-typed.
    subgoal_compiler_enabled: bool = True
    subgoal_compiler_max_variants: int = 4
    subgoal_compiler_max_prefix_chars: int = 600
    # Attempt to extract subgoals from existing proofs in the source file.
    planner_use_proof_subgoals: bool = True
    planner_proof_subgoals_max: int = 6
    # Drop planner subgoals with vacuous eventually-constant antecedents unless
    # the root theorem itself genuinely has that shape.
    planner_filter_vacuous_eventual_subgoals: bool = True
    # Quarantine planner subgoals that are effectively the root theorem in
    # disguise: high lexical overlap, no meaningful difficulty reduction, or
    # outright harder-than-root detours.
    planner_filter_near_restatement_subgoals: bool = True
    planner_subgoal_near_restatement_similarity: float = 0.85
    planner_subgoal_min_difficulty_drop: float = 4.0
    planner_subgoal_max_harder_delta: float = 8.0
    # Quarantine planner subgoals that repeatedly failed across replan rounds.
    # 0 disables this guard.
    planner_replan_failed_subgoal_quarantine_rounds: int = 2
    # Probe a small number of planner subgoals by attempting a cheap proof of
    # their negation; if ¬subgoal is provable, the subgoal is quarantined.
    planner_subgoal_falsify_enabled: bool = True
    planner_subgoal_falsify_max_subgoals: int = 8
    planner_subgoal_falsify_timeout_s: float = 2.0
    # Complementary Nat-sample falsifier (ported from mini-prover's
    # finite_claim_check). Instantiates leading Nat binders with small
    # concrete numerals and asks Lean to prove the negation deterministically
    # (decide +kernel / native_decide / norm_num). Catches false universals
    # over Nat that the primary Lean-probe falsifier may miss.
    planner_subgoal_nat_sample_falsify_enabled: bool = True
    planner_subgoal_nat_sample_falsify_timeout_s: float = 4.0
    planner_subgoal_nat_sample_falsify_max_checks: int = 4
    # Whether the planner should attempt JSON response_format first.
    # Set False for reasoning models that don't support json_object format.
    planner_use_json: bool = True
    refine_rounds: int = 2
    # Max failed proof candidates to send through the generic refiner after a
    # candidate batch fails Lean. 0 disables generic failed-candidate refinement.
    refine_max_failures_per_round: int = 3
    # Phase 2: multi-turn + best-of-N
    best_of_n: int = 1
    multi_turn_refine: bool = False
    # Phase 3: parallel goals
    parallel_candidates: bool = False
    # 0 = auto-size to Lean verifier capacity; otherwise max in-flight candidate
    # checks per ordered batch.
    parallel_candidate_window: int = 0
    parallel_goals: int = 1
    # Phase 3b: parallel beam node processing (all beam nodes proved concurrently)
    parallel_beam_nodes: bool = True
    # Phase 5: tactic-level search
    tactic_level: bool = False
    tactic_beam_width: int = 3
    tactic_max_steps: int = 20
    # Recursive replanning: when beam/MCTS dies, replan with failure context.
    # 0 = unlimited (cost/time budget is the real constraint).
    max_replans: int = 0
    # Minimum remaining seconds to justify a replan cycle.
    min_replan_time_s: float = 120.0
    # When True, unsolved runs should only terminate on real budget exhaustion
    # (time/attempt/node budget) or falsification. Control heuristics may still
    # end the current round, but they must restart/adapt instead of finalizing
    # the problem early.
    budget_only_unsolved_termination: bool = True
    # Allow refiner to signal plan-level changes (output REPLAN: tag).
    # When True, after refine fails on a node, ask refiner if the decomposition
    # needs restructuring.  The signal propagates up to the restart loop.
    refiner_can_replan: bool = True
    # Route composition LLM calls through a specific role.  Composition proofs
    # stitch multiple subgoal proofs together and often need more output tokens
    # than the prover model can provide.  Set to "refiner" to use the refiner
    # (typically higher max_tokens) for composition only — other proving phases
    # (beam, tactic, best-of-N) stay on the prover.
    composition_prover_role: str = "refiner"
    # After a composition candidate fails Lean, send the best failed proof plus
    # its exact diagnostic through the refiner before sampling another blind
    # composition batch.
    composition_refine_failures: bool = True
    composition_refine_max_failures_per_round: int = 1
    composition_refine_turns: int = 2
    # Phase 7: structured feedback
    structured_feedback: bool = True
    include_goal_state_in_prompt: bool = True
    strategy_prompting: bool = True
    strategy_prompting_max_calls: int = 2
    adaptive_llm_temperature: bool = True
    # Role-specific temperature ceilings — formal proof generation degrades
    # above ~0.7 for code-oriented LLMs (DeepSeek-Prover optimized 0.0–0.6).
    # Phase 8: Raised from 0.75 to 0.90.  On hard problems where the system
    # is stuck, the MEO policy needs headroom to push temperature higher for
    # diversity.  The adaptive pipeline EMA-smooths temperature changes,
    # preventing sudden jumps that degrade output quality.
    prover_temp_ceiling: float = 0.90
    refiner_temp_ceiling: float = 0.50
    planner_temp_ceiling: float = 0.30
    # Phase 8: domain-aware prompts
    domain_aware: bool = True
    # Phase 8.5: explicit planner artifacts — generate Lean-checkable
    # intermediate claims before tactic generation.  Disabled by default so
    # ordinary proof turns stay artifact-first instead of planner-first.
    proof_sketch: bool = False
    # When True, only generate planner artifacts for the root goal (ctx.depth==0).
    # This reduces planner LLM churn and avoids weak planner notes corrupting
    # subgoal-level proving.
    proof_sketch_root_only: bool = False
    # When True, extract HAVE: lines from the planner artifact and type-validate them
    # for injection as tactic candidates in tree search.
    sketch_have_extraction: bool = True
    sketch_max_haves: int = 5
    # Max token budget for planner text injected into prover prompt context.
    sketch_budget_tokens: int = 256
    # Phase 10: curriculum + smoke
    curriculum_order: bool = True
    curriculum_shuffle: bool = True
    curriculum_band_width: float = 15.0
    boilerplate_early_exit_threshold: float = 0.6
    # Structured feedback: allow full goal-state inclusion if under budget.
    full_goal_state_budget_tokens: int = 160
    full_goal_state_max_goals: int = 8
    # Limit how many previously-solved synthetic lemmas are injected into the
    # Lean context + LLM prompt for a given goal.  0 = disabled (inject none).
    # Keeping this bounded prevents prompt/context blowups and reduces
    # cross-branch contamination during tree search.
    max_context_solved_lemmas: int = 8
    # Proof potential monitor/pruning.
    # Observe-only by default: collect telemetry without pruning branches.
    proof_potential_enabled: bool = True
    proof_potential_observe_only: bool = True
    proof_potential_non_decrease_window: int = 3
    proof_potential_escape_budget: int = 2
    # Lemma fast path: try deterministic lemma closures (exact <lemma>) before
    # LLM generation.  Uses `first | exact A | exact B` for single Lean call.
    lemma_fast_path: bool = True
    # Max projection terms (And.1/And.2/mp/mpr) to generate from proven lemmas.
    fast_path_max_projections: int = 8
    # Hard per-probe timeout cap (seconds) for deterministic fast-path checks.
    # Prevents fast-path from consuming full "candidate" Lean timeout budgets.
    fast_path_probe_timeout_s: float = 12.0
    # Phase 0 invariant probes — pure observation, no behavior change.
    # See architecture_mapping_for_analysis/proof_graph_first_refactor_plan_2026-04-23.md.
    probes_enabled: bool = False
    probes_output_dir: str = ""
    # Phase 1.5 RootWorkset shadow mode. Writes always happen (zero behavior
    # impact); when this is true, the dual-path guard at
    # _build_root_support_context compares workset support against the
    # existing reconstruction and logs divergence to probes/metrics.
    use_root_workset: bool = False
    # Phase 6 three-lane arbiter gate. True by default: ProofSession.step()
    # drives lane selection between root-planning, local-proving, and
    # root-integration. Set False only to force the legacy sequential path.
    composition_first: bool = True
    # Circuit-break deterministic fast path when it has repeated zero-hit runs.
    # Set either threshold to 0 to disable that component.
    fast_path_zero_hit_min_runs: int = 4
    fast_path_zero_hit_min_attempts: int = 32
    # Circuit-break unknown-id/missing-instance oracle repair when repeated
    # attempts produce zero successful repairs.
    oracle_repair_zero_hit_min_attempts: int = 24
    # Legacy no-op retained for config compatibility. Full Lean verification now
    # receives every ordered candidate; concurrency is bounded by lean.max_parallel
    # and the active verifier backend.
    full_check_batch_cap: int = 12
    # Rich failure aggregation: inject structured failure summaries into prover
    # prompts so the LLM sees what previous rounds tried and how they failed.
    failure_aggregation: bool = True
    failure_aggregation_max_rounds: int = 3
    failure_aggregation_max_patterns_per_round: int = 3
    # Per-problem cap on refiner LLM calls (all call sites: _refine, fallback,
    # _iterative_refine, _refiner_replan_check).  0 = unlimited.
    max_refiner_calls_per_problem: int = 40
    # Reserve this many refiner calls for structural replan checks.
    # Regular refinement calls cannot consume this reserve.
    # 0 = no reserve.
    refiner_replan_reserved_calls: int = 2
    # Number of checked composition failures before activating
    # root-concentrated mode.  Must be >= 1.  3 was too aggressive —
    # restarts with the same (correct) decomposition each count as a
    # failure, so the system yanked focus back to the root before
    # composition had a fair chance to close.
    composition_failure_threshold: int = 6
    # Number of composition candidates per LLM call.  Was hardcoded n=3;
    # higher values improve coverage of the synthesis search space.
    composition_candidates_per_round: int = 6
    # Temperature control mode:
    #   "adaptive" — 11-mechanism adaptive pipeline (legacy, default)
    #   "bandit"   — Thompson Sampling over discrete arm set (prover only)
    #   "fixed"    — constant temperature (prover only)
    #   "round_robin" — deterministic cycling (prover only)
    # Non-prover roles always get None (model default) in non-adaptive modes.
    temperature_mode: str = "adaptive"
    # Bandit arm temperatures (each arm is a Beta(1,1) prior).
    temperature_bandit_arms: List[float] = field(
        default_factory=lambda: [0.50, 0.58, 0.66, 0.72]
    )
    # Fraction of posterior evidence carried across problem boundaries.
    temperature_bandit_carry: float = 0.10
    # Round-robin temperature list (cycled deterministically).
    temperature_round_robin_temps: List[float] = field(
        default_factory=lambda: [0.45, 0.58, 0.70]
    )
    # Fixed temperature value (used when temperature_mode == "fixed").
    temperature_fixed_value: float = 0.60
    # EMA smoothing factor for adaptive prover temperature (0 = frozen EMA,
    # 1 = no smoothing).
    prover_temp_ema_alpha: float = 0.65
    # ── Structural-fix feature gates (commit 20e779b) ──
    # Goal-scoped synth-hash sharing: block proofs containing synthetic lemma
    # refs when they failed on the same goal fingerprint within this session.
    session_synth_hash_sharing: bool = True
    # Independent score penalty for candidates referencing synth lemma names
    # that appeared in prior failures (orthogonal to strategy tag).
    synth_lemma_ref_penalty: bool = True
    # Deprecated no-op. Keep the legacy default enabled so dataclass defaults
    # and YAML loader behavior remain backward-compatible.
    filter_synth_dot_symm: bool = True
    # Per-subgoal guard lemma retrieval in expand_fn (can add latency when
    # many unique subgoals appear).  When False, only root gets guard lemmas
    # from the startup prefetch; subgoals get none.
    guard_per_subgoal_retrieval: bool = False
    # Fraction of time budget after which guard_min_nodes is overridden
    # to allow stale exit.  0.0 = never override, 1.0 = always override.
    stale_check_time_floor_fraction: float = 0.25
    # ── Tool-augmented proving ─────────────────────────────────────
    # Let the prover LLM call search_mathlib / check_type mid-proof
    # via OpenAI-compatible tool_use.  Requires the LLM provider to
    # support the ``tools`` parameter.
    tool_augmented_proving: bool = False
    tool_max_rounds: int = 3
    tool_check_type_timeout_s: float = 10.0
    tool_search_max_results: int = 10
    # ── Executable scaffold executor flags ────────────────────────────
    # The Lean-derived slot executor is now the primary root-closing path.
    executable_scaffold_executor: bool = True
    # Enable scaffold-native slot scheduling.
    scaffold_slot_scheduler: bool = True
    # Planner-written proof tactics are tried first, then repaired this many
    # times before the slot falls back to positive oracle/generic proving.
    plan_locked_max_refinements: int = 3
    # Suppress freeform root search while compiled scaffold is active.
    # Default false: Lean-checked root proofs must remain eligible even while
    # scaffold slots are being explored.
    executable_scaffold_root_suppression: bool = False
    # Max executor rounds per compiled scaffold before abandonment.
    scaffold_max_rounds: int = 20
    # Max rounds with no slot closure before abandonment.
    scaffold_no_progress_rounds: int = 5
    # Max times the same Lean error fingerprint repeats before abandonment.
    scaffold_repeated_error_cutoff: int = 3
    # Minimum remaining LLM cost budget (USD) required to continue scaffold execution.
    scaffold_min_budget_headroom_usd: float = 0.10
    # Cap theorem-scaffold planner calls so root guidance cannot disappear into
    # long opaque waits before skeleton/search execution.
    theorem_scaffold_timeout_s: float = 60.0
    # Cap executable-scaffold template generation separately; this phase should
    # be cheaper than the full theorem scaffold.
    executable_scaffold_template_timeout_s: float = 45.0
    # Cap proof-sketch JSON generation before falling back to tighter lanes.
    proof_sketch_json_timeout_s: float = 60.0
    # Cap the raw/tag fallback even more aggressively.
    proof_sketch_tag_timeout_s: float = 30.0

    def __post_init__(self) -> None:
        self.composition_failure_threshold = max(
            1,
            int(self.composition_failure_threshold or 0),
        )
        self.composition_candidates_per_round = max(
            1,
            int(self.composition_candidates_per_round or 1),
        )
        self.tool_max_rounds = max(1, int(self.tool_max_rounds or 1))
        self.tool_check_type_timeout_s = max(
            1.0, float(self.tool_check_type_timeout_s or 10.0)
        )
        self.tool_search_max_results = max(1, int(self.tool_search_max_results or 10))
        self.prover_semantic_fallback_max_backends = max(
            1,
            int(self.prover_semantic_fallback_max_backends or 1),
        )
        self.scaffold_max_rounds = max(1, int(self.scaffold_max_rounds or 1))
        self.scaffold_no_progress_rounds = max(
            1, int(self.scaffold_no_progress_rounds or 1)
        )
        self.plan_locked_max_refinements = max(
            0, int(self.plan_locked_max_refinements or 0)
        )
        self.scaffold_repeated_error_cutoff = max(
            1, int(self.scaffold_repeated_error_cutoff or 1)
        )
        self.scaffold_min_budget_headroom_usd = max(
            0.0, float(self.scaffold_min_budget_headroom_usd or 0.0)
        )
        self.theorem_scaffold_timeout_s = max(
            5.0, float(self.theorem_scaffold_timeout_s or 5.0)
        )
        self.executable_scaffold_template_timeout_s = max(
            5.0, float(self.executable_scaffold_template_timeout_s or 5.0)
        )
        self.proof_sketch_json_timeout_s = max(
            5.0, float(self.proof_sketch_json_timeout_s or 5.0)
        )
        self.proof_sketch_tag_timeout_s = max(
            5.0, float(self.proof_sketch_tag_timeout_s or 5.0)
        )


@dataclass
class TacticOracleConfig:
    """Lean-native tactic suggestion oracle (exact?, apply?, simp?, rw?).

    When enabled, the orchestrator queries Lean's built-in tactic search
    commands to close compiled scaffold slots and repair failing proof steps.
    This bridges the Mathlib API knowledge gap without additional LLM calls.
    """

    enabled: bool = True
    # Per-call timeout for suggestion commands (exact? can take 5-60s).
    timeout_s: int = 60
    # Lean heartbeat budget for suggestion search.
    max_heartbeats: int = 800000
    # Separate concurrency pool to avoid starving normal proof checks.
    max_concurrent: int = 2
    # Trigger on unknown_identifier / missing_instance failures.
    on_unknown_id: bool = True
    # Trigger on compiled scaffold slots before LLM proving.
    on_compiled_slot: bool = True
    # Inject suggestions as tactic tree candidates.
    on_tactic_tree: bool = True
    # Proactive: try Lean's full tactic vocabulary before any LLM call on a
    # fresh goal. With tiered tactics completing in about 5-8s on cold starts,
    # this is now viable.
    on_goal_start: bool = True
    goal_start_timeout_s: int = 30
    goal_start_max_heartbeats: int = 400000
    goal_start_max_suggestions: int = 3
    goal_start_max_depth: int = 8
    # Comma-separated list of Lean suggestion commands to try (in order).
    # Empty string (new default) = use full tiered tactic vocabulary.
    # Non-empty = legacy sequential mode with single timeout (backward compat).
    commands: str = ""
    # Per-tier timeout and heartbeat budgets for the tiered tactic vocabulary.
    tier1_timeout_s: int = 5
    tier1_max_heartbeats: int = 50000
    tier2_timeout_s: int = 8
    tier2_max_heartbeats: int = 200000
    tier3_timeout_s: int = 15
    tier3_max_heartbeats: int = 400000
    # Tier 4 uses the existing timeout_s / max_heartbeats fields.
    # Tier 5: slow/dangerous opt-in tactics.
    include_decide: bool = True
    decide_timeout_s: int = 10
    decide_max_heartbeats: int = 150000
    include_prop_complete: bool = (
        False  # Lean-native propositional calculus via itauto! *
    )
    prop_complete_timeout_s: int = 8
    prop_complete_max_heartbeats: int = 200000
    include_grind: bool = True  # SMT-style: congruence closure + cutsat + Grobner
    grind_timeout_s: int = 20
    grind_max_heartbeats: int = 600000
    include_polyrith: bool = False  # Requires Sage or network access
    include_native_decide: bool = False  # Can crash the Lean kernel
    # Retrieval-informed oracle: try exact/apply/simp/rw with retrieved
    # Mathlib lemma names before falling back to expensive search tactics.
    retrieval_informed_enabled: bool = True
    retrieval_informed_max_lemmas: int = 5
    retrieval_informed_timeout_s: float = 3.0
    retrieval_informed_max_heartbeats: int = 50000
    # Wall-clock cap for unknown-id oracle repair suggestion search.
    # 0 disables cap (legacy behavior).
    repair_max_wall_s: float = 20.0


@dataclass
class StrategyConfig:
    mode: str = "linear"  # "linear" | "beam" | "mcts" | "tactic_tree"
    beam_width: int = 4
    mcts_simulations: int = 32
    mcts_c_puct: float = 1.4
    backtrack: bool = True
    beam_stale_decay_rate: float = 0.0  # 0.0 = no decay (exact backward compat)
    # Kill beam nodes after this many consecutive no-progress attempts.
    # 0 = disabled.  Prevents 500-attempt stagnation loops on stuck goals.
    beam_stagnation_threshold: int = 20
    # Structural fix #2 (2026-04-16): hard cap on total per-goal failures.
    # Distinct from beam_stagnation_threshold (soft, error-type-sensitive,
    # only deprioritizes). When a goal accumulates this many TOTAL failures
    # (no reset on error-type churn), the scheduler permanently drops it
    # from the queue so the beam stops burning LLM budget on a known-stuck
    # goal. 0 = disabled (revert to old soft-only behavior). Default 12 ≈
    # 4× the soft threshold default of 3, allowing varied-error exploration
    # before the hard cap fires.
    goal_terminal_stagnation_threshold: int = 12


@dataclass
class BudgetConfig:
    time_seconds: int = 3600  # 60 minutes default (increased from 30)
    max_total_attempts: int = 200
    stale_fraction: float = 0.35
    early_exit_min_iterations: int = 5
    # Minimum nodes expanded before stale search can trigger (protects slow searches)
    early_exit_min_nodes: int = 70
    # Per-problem dollar cap: 0 = unlimited.  Checked every search iteration.
    max_cost_per_problem_usd: float = 0.0
    # Sweep-level dollar cap: 0 = unlimited.  Checked between problems in CLI sweep loop.
    max_sweep_cost_usd: float = 0.0
    # Max beam-death restarts per problem: 0 = unlimited (time budget governs).
    max_beam_restarts: int = 0
    # Beam restart temperature escalation.
    beam_restart_temp_boost: float = 0.08  # per-restart scale increment
    beam_restart_temp_cap: float = 1.25  # max temperature scale multiplier


@dataclass
class TokenPricing:
    """Per-million-token pricing for cost tracking and budget enforcement."""

    input_per_m: float = 0.0  # $/1M input tokens (cache miss)
    cached_per_m: float = 0.0  # $/1M cached input tokens
    output_per_m: float = 0.0  # $/1M output tokens


@dataclass
class EnsembleConfig:
    enabled: bool = True
    seed: int = 1337
    embedding_dim: int = 768
    alpha: float = 0.2
    eta: float = 0.1
    epsilon0: float = 1.0
    epsilon_min: float = 0.1
    epsilon_max: float = 5.0
    # Event signal that drives epsilon homeostasis.
    # - hit_rate: candidate-embedding density (legacy behavior)
    # - success_rate: Lean verification success rate
    # - progress_rate: Lean goal-count reduction rate
    # - success_or_progress: max(success, progress) blended signal
    # - blend: weighted blend of hit_rate and success_or_progress
    epsilon_homeostasis_event: str = "hit_rate"
    epsilon_homeostasis_blend_weight: float = 0.6
    r_star0: float = 0.3
    r_star_min: float = 0.05
    r_star_max: float = 0.7
    depth_r_star_decay: float = 0.15  # r_star scale reduction per depth level
    depth_r_star_floor: float = 0.5  # minimum depth scale factor (at depth 4+)
    tau0: float = 1.0
    tau_min: float = 0.2
    tau_max: float = 1.5
    eps_explore0: float = 0.1
    eps_explore_min: float = 0.02
    eps_explore_max: float = 0.6
    # Stall-mode controls for long failure streaks (root-goal recovery).
    stall_failure_streak_threshold: int = 40
    stall_success_rate_threshold: float = 0.05
    stall_decay_floor: float = 0.25
    stall_disable_budget_clamp: bool = True
    # Progress-aware stall detection: when near-miss fraction + progress trend
    # exceed this threshold, use soft stall (severity=0.3) instead of hard stall.
    stall_progress_attenuation_threshold: float = 0.15
    beta: float = 0.3
    memory_size: int = 2000
    # Class-balanced eviction: reserve this fraction of MemoryStore slots for
    # positive examples (reward > 0.5) during eviction.
    memory_success_reserve_ratio: float = 0.2
    recent_window: int = 50
    weight_center: float = 1.0
    weight_utility: float = 0.8
    weight_novelty: float = 0.6
    weight_goal: float = 0.8
    weight_active_goal: float = 0.3
    weight_cost: float = 0.3
    weight_quality: float = 0.7
    cost_scale: float = 200.0  # Token-based scale for candidate length penalty
    cost_penalty: float = 0.1
    penalty_trivial: float = 0.6
    penalty_bad: float = 2.0
    penalty_degenerate: float = 3.0
    progress_reward_weight: float = 0.5
    error_penalty_type_mismatch: float = 0.08  # near-miss: structure right, type wrong
    error_penalty_unknown_identifier: float = 0.25  # far: referencing nonexistent name
    error_penalty_tactic_failed: float = 0.15  # generic: tactic doesn't apply
    error_penalty_missing_instance: float = (
        0.2  # structural: missing typeclass instance
    )
    error_penalty_simp_no_progress: float = 0.1  # mild: wrong simplification target
    error_penalty_timeout: float = 0.3  # hopeless: spinning forever
    error_penalty_unification_failed: float = (
        0.08  # near-miss: unifier close but not quite
    )
    quality_line_target: float = 4.0
    quality_tactic_target: float = 3.0
    # Phase 6: persistent memory + diversity
    persistent_memory_path: Optional[str] = None
    # Optional online model persistence path (manual/explicit use only).
    # Startup auto-load is intentionally disabled; cached embedding models
    # should not replay stale cross-run online weights unless a caller opts in.
    online_models_path: Optional[str] = None
    # Autoload persisted online model weights at startup when a path is set.
    # Defaults to False (manual opt-in only) to avoid replaying stale weights.
    online_model_autoload: bool = False
    diversity_min_strategies: int = 2
    retrieval_k: int = 3
    # Memory embedding backend (stable retrieval embedding)
    memory_embedding_backend: str = "sentence_transformers"
    memory_embedding_model: str = "BAAI/bge-base-en-v1.5"
    memory_embedding_device: Optional[str] = None
    memory_embedding_normalize: bool = True
    memory_embedding_prefer_local_files: bool = True
    memory_embedding_local_files_only: bool = True
    memory_embedding_allow_download: bool = False
    memory_embedding_init_timeout_s: float = 8.0
    # Hybrid BM25 + embedding weights for persistent memory retrieval
    memory_weight_bm25: float = 0.5
    memory_weight_embed: float = 0.5
    # Failed-strategy hinting from memory is high risk on failure-heavy stores,
    # so keep it opt-in and heavily gated.
    memory_failed_strategy_hints_enabled: bool = False
    memory_failed_strategy_gate_threshold: float = 0.25
    memory_failed_strategy_min_recent_success: float = 0.05
    memory_failed_strategy_min_local_support: int = 8
    # Support-aware smoothing for recent statement success rate used by
    # failed-strategy hint gating. A larger prior makes recency less brittle
    # during hard failure streaks (common on Putnam-scale problems).
    memory_failed_strategy_recent_prior_strength: int = 24
    # During stall-mode recovery, disable full-strength failed-strategy hints
    # (the orchestrator forces degraded mode to cap hint volume).
    memory_failed_strategy_disable_during_stall: bool = True
    # Failed-strategy handling:
    # - Structured prior: penalize candidate/goal strategies that repeatedly fail
    #   (local + memory), instead of steering the LLM with natural-language hints.
    # - Prompt hints are kept optional for debugging, but disabled by default
    #   because models can over-index on them.
    failed_strategy_prior_enabled: bool = True
    failed_strategy_prior_penalty: float = 0.35
    # Phase 8: Enabled by default.  Without this, the LLM repeatedly tries
    # strategies that have already failed many times on the same goal, wasting
    # budget.  The prompt hint lists recently-failed strategy families so the
    # LLM can diversify.
    failed_strategy_prompt_hints_enabled: bool = True
    # Early-stop gate driven by ensemble novelty/success signals.
    # Keep disabled by default for hard theorem proving where long plateaus are normal.
    early_exit_ensemble_signals_enabled: bool = False
    # Spec gaps: adaptive ensemble extensions
    adaptive_embedding: bool = False
    embedding_lr: float = 0.01
    world_model_lr: float = 0.05
    utility_lr: float = 0.03
    # L2 weight decay for online models (WorldModel, UtilityPredictor).
    # Prevents weight drift in long runs.
    weight_decay: float = 1e-4
    # MLP + Experience Replay (M4/M5 fix).
    model_hidden_dim: int = (
        32  # Hidden layer width for WorldModel/UtilityPredictor MLPs
    )
    replay_buffer_size: int = 200  # Circular experience replay buffer size per model
    replay_batch: int = 4  # Samples replayed per update step
    replay_lr_scale: float = 0.5  # Learning rate multiplier for replay updates
    hidden_lr_scale: float = (
        0.2  # Learning rate multiplier for hidden layer (slow features)
    )
    # Stratified replay: sample ~50/50 positive/negative for WorldModelMLP.
    # For UtilityPredictorMLP, opt-in via this flag (continuous labels make 0.5 threshold less meaningful).
    replay_stratified_utility: bool = False
    negation_closure: bool = True
    max_closure_expansion: int = 3
    grow_rate: float = 0.1
    prune_rate: float = 0.05
    # Strategy priors
    strategy_prior_weight: float = 0.3
    # Learning loop: fast policy/value guidance (loaded from disk)
    guidance_enabled: bool = True
    guidance_dir: str = "./runs/guidance"
    guidance_policy_path: Optional[str] = None
    guidance_value_path: Optional[str] = None
    guidance_min_policy_conf: float = 0.45
    guidance_min_value_conf: float = 0.55
    guidance_fallback_to_llm: bool = True
    # Optional guidance auto-training from persistent memory.
    guidance_autotrain: bool = False
    guidance_autotrain_min_examples: int = 200
    guidance_autotrain_min_new_examples: int = 50
    guidance_autotrain_max_examples: int = 0  # 0 = no cap
    # Adaptive tactic lexicon (harvested from passive observations).
    tactic_lexicon_enabled: bool = True
    tactic_lexicon_path: str = "./runs/tactic_observations.jsonl"
    tactic_lexicon_promote_support: int = 8
    tactic_lexicon_unknown_prior: float = 0.35
    tactic_lexicon_demote_after_failures: int = 3
    tactic_lexicon_demote_decay: float = 0.20
    # Master Ensemble Orchestrator (MEO): when enabled, the ensemble acts as a
    # global policy layer (search strategy, budgets, rerank mode, etc.).
    master_enabled: bool = True
    master_log_decisions: bool = True
    # One-shot hardening: extra robustness for single-problem runs.
    one_shot_hardening: bool = False
    # MEO difficulty estimation (AST-based option + cache).
    meo_use_ast_difficulty: bool = False
    meo_ast_difficulty_timeout_s: float = 2.0
    meo_difficulty_cache_size: int = 2048
    # MEO policy refresh: recompute during a goal after N attempts.
    meo_policy_refresh_cycle: int = 4
    # Planner learning: when enabled, include planner outcomes in online updates.
    planner_learning_enabled: bool = False
    # Curiosity-driven intrinsic reward parameters (spec: R_int := curiosity_gain(err, M))
    curiosity_novelty_scale: float = (
        1.0  # Scale for novelty contribution (0 = pure error)
    )
    curiosity_novelty_k: int = 5  # k for k-NN novelty computation
    curiosity_decay_enabled: bool = False  # Decay for repeatedly-visited states
    curiosity_decay_window: int = 100  # Window for visit counting
    # Blend ramp parameters: controls how quickly learned predictors are trusted
    # blend = min(blend_max, predictor._n / blend_warmup)
    blend_warmup: int = 75  # Samples until blend reaches max
    blend_max: float = 0.65  # Maximum blend weight for learned predictor
    # Per-problem blend ramp resets each problem; global floor activates after
    # cumulative training samples exceed blend_warmup_global.
    blend_warmup_global: int = 150  # Cumulative _n threshold for global floor
    blend_global_floor: float = 0.20  # Minimum blend once global warmup met
    # --- Spec Alignment: Opportunity 1 (Covariance / Mahalanobis) ---
    use_mahalanobis: bool = True  # Use Mahalanobis instead of cosine distance
    precision_lr: float = 0.005  # Learning rate for diagonal precision update
    precision_min: float = 0.1  # Floor per-dimension precision
    precision_max: float = 10.0  # Cap per-dimension precision
    use_full_spd_metric: bool = (
        False  # Use full SPD covariance/precision metric updates
    )
    spd_cov_beta: float = 0.15  # EMA blend for covariance updates
    spd_cov_shrinkage: float = (
        0.02  # Identity shrinkage (lambda) for covariance stabilization
    )
    spd_cov_jitter: float = 1e-6  # Jitter added before Cholesky inversion
    spd_cov_min_variance: float = 1e-9  # Floor for diagonal covariance entries
    spd_tail_quantile: float = 0.95  # Tail quantile for instability summaries
    # --- Spec Alignment: Opportunity 3 (Discrete Actions) ---
    action_adjust_closure: bool = True  # Enable adjust_closure action
    action_tighten_filter: bool = True  # Enable tighten_filter action
    action_relax_filter: bool = True  # Enable relax_filter action
    action_weight_grow: float = 0.25  # w_g: grow action weight
    action_weight_prune: float = 0.20  # w_p: prune action weight
    action_weight_closure: float = 0.20  # w_c: adjust_closure weight
    action_weight_tighten: float = 0.20  # w_t: tighten_filter weight
    action_weight_relax: float = 0.15  # w_r: relax_filter weight
    # --- Spec Alignment: Opportunity 4 (Semantic Closure) ---
    semantic_closure: bool = True  # Enable embedding-space closure expansion
    semantic_closure_max: int = 5  # Max candidates from semantic closure
    # --- Spec Alignment: Opportunity 5 (Formal/Learned Mode) ---
    controller_mode: str = "auto"  # "auto" | "formal" | "learned"
    blend_threshold_tau: float = 0.3  # Below this blend: formal mode (centroid-based)
    admission_formal_threshold: float = 0.20
    admission_learned_threshold: float = 0.15
    admission_floor: int = 1  # minimum consistent candidates to retain when possible
    formal_consistency_mode: str = "theorem_prover"  # "syntactic" | "theorem_prover"
    learned_collapse_enabled: bool = True
    learned_collapse_threshold: float = 0.55
    learned_collapse_similarity_threshold: float = 0.90
    negation_closure_policy_enabled: bool = True
    policy_semantic_closure_enabled: bool = True
    policy_semantic_closure_max: int = 5
    policy_negation_closure_max: int = 3
    # --- Delta-space controller geometry (alongside embedding geometry) ---
    delta_geometry_enabled: bool = True
    delta_geometry_epsilon0: float = 1.0
    delta_geometry_epsilon_min: float = 0.1
    delta_geometry_epsilon_max: float = 4.0
    delta_geometry_cov_beta: float = 0.15
    delta_geometry_shrinkage: float = 0.05
    delta_geometry_metric_mode: str = "mixture_learned_spd"  # whitened | learned_spd | mixture | mixture_learned_spd
    delta_geometry_regimes: int = 2
    delta_geometry_selector_lr: float = 0.05
    delta_geometry_learned_metric_blend: float = 0.20
    # --- Typed controller action dimensions ---
    typed_actions_enabled: bool = True
    growth_action_dims: List[str] = field(
        default_factory=lambda: [
            "search_width",
            "retrieval_width",
            "closure_scope",
            "temperature",
        ]
    )
    prune_action_dims: List[str] = field(
        default_factory=lambda: [
            "verification_strictness",
            "search_width",
            "retrieval_width",
        ]
    )
    selector_vectors: Dict[str, List[float]] = field(default_factory=dict)
    # --- Delta-Homeostasis: blend reward signals into geometric acceptance ---
    delta_homeostasis_enabled: bool = (
        True  # Master switch for delta-homeostasis integration
    )
    delta_homeostasis_lambda: float = 0.15  # Epsilon law blend coefficient
    delta_homeostasis_sigma_blend: float = 0.10  # Centroid alpha modulation strength
    delta_homeostasis_precision_blend: float = 0.10  # Precision lr modulation strength
    delta_homeostasis_score_factor: float = (
        0.15  # Sigmoid weight_center modulation strength
    )
    delta_homeostasis_closure_factor: float = (
        0.20  # Closure epsilon modulation strength
    )
    # Configurable meta-signal weights for _combined_meta_signal().
    # 4-way blend: success history + reward trend + delta quality + world model.
    meta_signal_w_success: float = 0.40
    meta_signal_w_reward: float = 0.20
    meta_signal_w_delta: float = 0.15
    meta_signal_w_wm: float = 0.25
    # v2.2 Three-Layer Coherence: Forward Model (Layer 1 substrate)
    forward_model_enabled: bool = False  # master gate — OFF by default
    forward_model_lr: float = 0.01  # gradient descent learning rate for A, b
    forward_model_history_len: int = 20  # sigma trajectory buffer size
    forward_model_residual_capacity: int = 100  # whitened residual ring buffer capacity
    forward_model_lambda_res: float = 1e-4  # Tikhonov regularization for Cov_pred
    forward_model_res_cov_beta: float = (
        0.1  # EMA rate for forward-model internal (raw) residual covariance
    )
    forward_model_clip_interval: int = 10  # clip A singular values every N updates
    # v2.2 Layer 2: Directional Coherence
    layer2_whitened_cov_beta: float = (
        0.1  # EMA rate for whitened residual covariance (Layer 2 directional analysis)
    )
    layer2_theta_aniso: float = 3.0  # anisotropy threshold
    layer2_theta_align: float = 0.7  # alignment threshold
    layer2_theta_dir: float = 2.0  # combined directional coherence threshold
    layer2_gamma_dir: float = 0.5  # weight: anisotropy vs alignment in composite
    layer2_buffer_capacity: int = 30  # anisotropy/alignment ring buffer size
    # v2.2 Layer 3: Relational Coherence
    layer3_min_cluster_size: int = 5  # minimum residuals per source tag for inclusion
    layer3_theta_rel: float = 0.3  # relational coherence threshold
    layer3_theta_gram_stability: float = 0.8  # Gram stability threshold
    layer3_gram_history_capacity: int = 20  # Gram matrix history ring buffer size
    layer3_w_c: float = 1.0 / 3.0  # centroid alignment weight in Gram
    layer3_w_p: float = 1.0 / 3.0  # principal direction weight in Gram
    layer3_w_s: float = 1.0 / 3.0  # spread similarity weight in Gram
    # v2.2 Rupture Pressure (used to gate the Layer 2 rupture action)
    rupture_theta_stall: int = 15  # cycles of homeostatic failure before "stalled"
    rupture_theta_pressure: float = 5.0  # pressure threshold for rupture eligibility
    rupture_pressure_decay: float = 0.95  # exponential decay when not stalled
    rupture_k_max: int = 50  # maximum dimensionality
    rupture_w_L1: float = 1.0  # Layer 1 weight in pressure
    rupture_w_L2: float = 2.0  # Layer 2 weight in pressure
    rupture_w_L3: float = 2.0  # Layer 3 weight in pressure


@dataclass
class RetrievalConfig:
    enabled: bool = True
    index_path: str = "./runs/lemma_index.jsonl"
    meta_path: str = "./runs/lemma_index.meta.json"
    # Optional dense index for fast semantic retrieval over all lemmas.
    dense_index_path: str = "./runs/lemma_dense.npy"
    dense_meta_path: str = "./runs/lemma_dense.meta.json"
    mathlib_root: Optional[str] = None  # static Mathlib API search only
    project_root: Optional[str] = None  # project/support retrieval roots
    include_mathlib: bool = True  # enable static Mathlib API search
    include_project: bool = True  # enable project/support retrieval
    update_on_start: bool = False
    max_lemmas: int = 250000
    top_k: int = 250
    max_prompt_lemmas: int = 30
    min_score: float = 0.05
    # BM25
    bm25_k1: float = 1.2
    bm25_b: float = 0.75
    weight_bm25: float = 1.0
    # Symbol/name overlap
    weight_symbol: float = 0.25
    weight_name: float = 0.35
    # Embedding re-rank
    use_embeddings: bool = True
    embedding_dim: int = 768
    embedding_seed: int = 1337
    weight_embed: float = 0.35
    # Dense retrieval (hybrid)
    dense_retrieval_enabled: bool = False
    dense_build_on_start: bool = False
    dense_top_k: int = 200
    hybrid_pool_multiplier: int = 5
    # Dense search mode:
    # - "full": full-matrix top-k (fast with BLAS but still O(ND) per query)
    # - "bm25_filtered": compute dense similarity only on BM25 candidate pool (much cheaper)
    dense_search_mode: str = "full"  # "full" | "bm25_filtered"
    # Embedding backend
    embedding_backend: str = "sentence_transformers"
    embedding_model: str = "BAAI/bge-base-en-v1.5"
    embedding_device: Optional[str] = None
    embedding_normalize: bool = True
    embedding_prefer_local_files: bool = True
    embedding_local_files_only: bool = True
    embedding_allow_download: bool = False
    embedding_init_timeout_s: float = 8.0
    embedding_cache_size: int = 10000
    query_embedding_cache_size: int = 512
    # Dense index build performance tuning
    dense_build_batch_size: int = 256
    # Boosts
    boost_domain_prefix: float = 1.2
    include_docstrings: bool = False
    # Goal-conditioned retrieval
    goal_conditioned: bool = True
    goal_query_weight: float = 1.0
    # Reranking (optional)
    rerank_mode: str = "none"  # "none" | "cross_encoder" | "llm"
    rerank_top_n: int = 50
    rerank_llm_role: str = "planner"  # "planner" | "prover"
    cross_encoder_model: str = "BAAI/bge-reranker-v2-minicpm-layerwise"
    cross_encoder_fallback_model: str = "BAAI/bge-reranker-large"
    # When true, skip layerwise FlagEmbedding reranker and use
    # sentence-transformers CrossEncoder directly.
    cross_encoder_force_sentence_transformers: bool = False
    cross_encoder_device: Optional[str] = None
    cross_encoder_cache_size: int = 5000
    # Hard timeout for one cross-encoder scoring call (seconds). If exceeded,
    # layerwise reranker is disabled for the remainder of the run and fallback
    # CrossEncoder is used.
    cross_encoder_score_timeout_s: float = 20.0
    cross_encoder_cutoff_layers: List[int] = field(default_factory=lambda: [28])
    cross_encoder_use_fp16: bool = True
    # Failure recovery policy for cross-encoder reranking.
    # Transient failures (timeouts/network/device hiccups) are disabled only
    # temporarily and retried after cooldown; repeated transient failures can
    # be escalated to permanent disable for the current process.
    cross_encoder_transient_cooldown_s: float = 120.0
    cross_encoder_max_transient_failures: int = 3
    # If true, clear transient cross-encoder disable state at problem
    # boundaries so one failed theorem does not suppress reranking for the
    # entire sweep process.
    cross_encoder_reset_on_problem_start: bool = True
    # Learning-to-rank (online, optional)
    ltr_enabled: bool = False
    ltr_weights_path: str = "./runs/retrieval_ltr_weights.json"
    ltr_learning_rate: float = 0.05
    ltr_warmup_updates: int = 50
    ltr_min_updates: int = 10
    ltr_negative_samples: int = 32
    ltr_positive_weight: float = 2.0
    ltr_weight_decay: float = 0.999
    # Prompt budgeting / packing
    prompt_budget_enabled: bool = True
    prompt_budget_tokens: int = 1200
    # Hard cap to prevent runaway prompt growth (applies even if budgeting is off).
    prompt_budget_hard_cap_tokens: int = 20000
    prompt_budget_dedup_jaccard: float = 0.92
    # Observability
    log_scores: bool = False
    log_top_k: int = 10


@dataclass
class ProvenLemmaConfig:
    """Cross-problem proven lemma index configuration."""

    enabled: bool = True
    path: str = "./runs/proven_lemmas.jsonl"
    max_entries: int = 50000
    top_k: int = 20
    max_prompt_lemmas: int = 10
    bm25_k1: float = 1.2
    bm25_b: float = 0.75
    weight_bm25: float = 0.6
    weight_embed: float = 0.4
    pool_multiplier: int = 5
    min_score: float = 0.25
    embedding_backend: str = "sentence_transformers"
    embedding_model: str = "BAAI/bge-base-en-v1.5"
    embedding_device: Optional[str] = None
    embedding_normalize: bool = True
    embedding_prefer_local_files: bool = True
    embedding_local_files_only: bool = True
    embedding_allow_download: bool = False
    embedding_init_timeout_s: float = 8.0
    embedding_dim: int = 768
    embedding_seed: int = 1337


@dataclass
class TacticTreeConfig:
    enabled: bool = True  # Tactic-level search is a key feature
    mode: str = "beam"
    beam_width: int = 3
    max_steps: int = 20
    max_candidates_per_node: int = 5
    mcts_simulations: int = 64
    mcts_c_puct: float = 1.4
    time_limit: float = 300.0
    max_depth: int = 25
    weight_progress: float = 0.5
    weight_prior: float = 0.2
    weight_ensemble: float = 0.2
    depth_penalty_factor: float = 0.02
    multi_tactic: bool = True
    num_tactic_candidates: int = 5
    max_cache_entries: int = 10000
    # Tactic-level feedback: feed individual tactic evaluations back to ensemble.
    feedback_enabled: bool = True
    # Whether tactic-level feedback should write to proof memory (usually False
    # to avoid polluting proof memory with individual tactic fragments).
    feedback_memory: bool = False
    # Recursive proving controller:
    # one proof function handles the root theorem and every descendant subgoal.
    # The local tactic tree (beam/MCTS) becomes one direct prover inside that
    # controller rather than a root-only side lane.
    recursive_enabled: bool = False
    recursive_max_depth: int = 8
    recursive_max_nodes: int = 160
    recursive_retrieval_rounds: int = 2
    recursive_direct_rounds: int = 2
    recursive_assembly_rounds: int = 4
    recursive_decomposition_enabled: bool = True
    recursive_tactic_tree_time_limit: float = 60.0



@dataclass
class AppConfig:
    roles: Dict[str, Any]  # str -> RoleConfig | List[RoleConfig]
    lean: LeanConfig
    search: SearchConfig
    budgets: BudgetConfig
    ensemble: EnsembleConfig
    retrieval: RetrievalConfig
    strategy: StrategyConfig = None  # type: ignore[assignment]
    tactic_tree: TacticTreeConfig = None  # type: ignore[assignment]
    proven_lemma: ProvenLemmaConfig = None  # type: ignore[assignment]
    model_pool: Dict[str, bool] = None  # type: ignore[assignment]
    token_pricing: TokenPricing = None  # type: ignore[assignment]
    tactic_oracle: TacticOracleConfig = None  # type: ignore[assignment]

    def __post_init__(self) -> None:
        if self.strategy is None:
            self.strategy = StrategyConfig()
        if self.tactic_tree is None:
            self.tactic_tree = TacticTreeConfig()
        if self.proven_lemma is None:  # type: ignore[truthy-bool]
            self.proven_lemma = ProvenLemmaConfig()
        if self.model_pool is None:  # type: ignore[truthy-bool]
            self.model_pool = {}
        if self.token_pricing is None:  # type: ignore[truthy-bool]
            self.token_pricing = TokenPricing()
        if self.tactic_oracle is None:  # type: ignore[truthy-bool]
            self.tactic_oracle = TacticOracleConfig()


def _role_from_dict(name: str, data: Dict[str, Any]) -> RoleConfig:
    data = _expect_mapping(data, f"roles.{name}")
    base_url = str(data.get("base_url", "")).strip()
    model = str(data.get("model", "")).strip()
    missing_fields = [
        field_name
        for field_name in ("base_url", "model")
        if data.get(field_name) is None or not str(data.get(field_name)).strip()
    ]
    if missing_fields:
        raise ConfigError(
            f"roles.{name}: missing required field(s): {', '.join(missing_fields)}"
        )
    api_key = data.get("api_key")
    if isinstance(api_key, str):
        api_key = api_key.strip()
    # Convenience: allow configs to keep a placeholder and source the real key
    # from the environment. This prevents accidental key commits and makes CLI
    # usage consistent with the `run_*_chatgpt.sh` wrappers.
    if not api_key or str(api_key).strip() == "REPLACE_WITH_OPENAI_API_KEY":
        # Use ONLY the provider-specific env var. The previous fallback
        # from ``DEEPSEEK_API_KEY`` to ``OPENAI_API_KEY`` (and similar)
        # silently sent an OpenAI key to DeepSeek's endpoint, producing
        # mysterious intermittent 401s for roles whose fallback chain
        # included a DeepSeek model. If the required env var is missing
        # we leave ``api_key`` unset; the role-level validation at
        # lines ~1397 will surface a precise error pointing the user at
        # the exact variable to set.
        provider = provider_for_base_url(base_url)
        if provider == "deepseek":
            env_key = os.getenv("DEEPSEEK_API_KEY")
            if not env_key and os.getenv("OPENAI_API_KEY"):
                logger.warning(
                    "roles.%s: DEEPSEEK_API_KEY is unset but OPENAI_API_KEY "
                    "is set — NOT using the OpenAI key for the DeepSeek "
                    "endpoint (would 401). Set DEEPSEEK_API_KEY.",
                    name,
                )
        elif provider == "openai":
            env_key = os.getenv("OPENAI_API_KEY")
        else:
            env_key = None
        if env_key and env_key.strip():
            api_key = env_key.strip()
    return RoleConfig(
        name=name,
        base_url=base_url,
        model=model,
        api_key=api_key,
        temperature=float(data.get("temperature", 0.2)),
        top_p=float(data.get("top_p", 0.95)),
        max_tokens=int(data.get("max_tokens", 1024)),
        conversation_max_tokens_override=(
            int(data["conversation_max_tokens_override"])
            if data.get("conversation_max_tokens_override") is not None
            else None
        ),
        context_window=(
            int(data["context_window"])
            if data.get("context_window") is not None
            else None
        ),
        reasoning_effort=(
            str(data["reasoning_effort"]).strip()
            if data.get("reasoning_effort") is not None
            and str(data["reasoning_effort"]).strip()
            else None
        ),
        reasoning_control_required=_as_bool(
            data.get("reasoning_control_required", False),
            default=False,
        ),
        timeout_s=float(data.get("timeout_s", 120)),
        prompt_style=str(data.get("prompt_style", "auto")),
        weight=float(data.get("weight", 1.0)),
        thinking_enabled=_as_bool(data.get("thinking_enabled", False), default=False),
    )


def _roles_from_data(data: Dict[str, Any]) -> Dict[str, Any]:
    """Parse roles, supporting both single-dict and list-of-dicts (model chains)."""
    data = _expect_mapping(data, "roles")
    roles: Dict[str, Any] = {}
    for name, cfg in data.items():
        if isinstance(cfg, list):
            roles[name] = [_role_from_dict(name, c) for c in cfg]
        else:
            roles[name] = _role_from_dict(name, cfg)
    return roles


def validate_config(cfg: AppConfig) -> None:
    """Validate semantic constraints that type coercion alone cannot catch.

    Raises ``ConfigError`` with all detected problems at once so the user
    can fix them in a single pass.
    """
    errors: List[str] = []

    def _require(cond: bool, msg: str) -> None:
        if not cond:
            errors.append(msg)

    # --- Required roles (orchestrator.py:88-90) ---
    for role_name in ("planner", "prover", "refiner"):
        _require(role_name in cfg.roles, f"roles: missing required role '{role_name}'")
        role_cfg = cfg.roles.get(role_name)
        if isinstance(role_cfg, list):
            _require(
                len(role_cfg) > 0,
                f"roles.{role_name}: role list must include at least one model",
            )

    def _flatten_role_configs() -> List[RoleConfig]:
        flattened: List[RoleConfig] = []
        for role_name in ("planner", "prover", "refiner"):
            role_cfg = cfg.roles.get(role_name)
            if isinstance(role_cfg, list):
                flattened.extend(role_cfg)
            elif isinstance(role_cfg, RoleConfig):
                flattened.append(role_cfg)
        return flattened

    # --- Role-level checks ---
    def _check_role(rc: RoleConfig) -> None:
        _require(
            bool(str(rc.base_url).strip()),
            f"roles.{rc.name}: base_url must be non-empty",
        )
        _require(
            bool(str(rc.model).strip()), f"roles.{rc.name}: model must be non-empty"
        )
        _require(
            rc.temperature >= 0,
            f"roles.{rc.name}: temperature must be >= 0, got {rc.temperature}",
        )
        _require(rc.top_p > 0, f"roles.{rc.name}: top_p must be > 0, got {rc.top_p}")
        _require(
            rc.top_p <= 1.0, f"roles.{rc.name}: top_p must be <= 1.0, got {rc.top_p}"
        )
        _require(
            rc.max_tokens >= 1,
            f"roles.{rc.name}: max_tokens must be >= 1, got {rc.max_tokens}",
        )
        _require(
            rc.timeout_s > 0,
            f"roles.{rc.name}: timeout_s must be > 0, got {rc.timeout_s}",
        )
        if rc.reasoning_effort is not None:
            _require(
                str(rc.reasoning_effort).strip().lower()
                in {"none", "low", "medium", "high", "max"},
                (
                    f"roles.{rc.name}: reasoning_effort must be one of "
                    "none|low|medium|high|max when provided"
                ),
            )
        if rc.context_window is not None:
            _require(
                int(rc.context_window) > 0,
                f"roles.{rc.name}: context_window must be > 0, got {rc.context_window}",
            )
            # Require some headroom for prompt content beyond max_tokens.
            min_prompt = 256
            _require(
                int(rc.context_window) >= int(rc.max_tokens) + min_prompt,
                (
                    f"roles.{rc.name}: context_window ({rc.context_window}) must be >= "
                    f"max_tokens ({rc.max_tokens}) + {min_prompt}"
                ),
            )
        _require(
            rc.prompt_style in ("auto", "standard"),
            f"roles.{rc.name}: prompt_style must be auto|standard, got '{rc.prompt_style}'",
        )
        # Catch common misconfigurations early (avoid opaque 401s later).
        if base_url_matches_provider(rc.base_url, "openai"):
            _require(
                bool(rc.api_key)
                and str(rc.api_key).strip() != "REPLACE_WITH_OPENAI_API_KEY",
                f"roles.{rc.name}: api_key is required for api.openai.com (set env OPENAI_API_KEY or roles.{rc.name}.api_key)",
            )
        if base_url_matches_provider(rc.base_url, "deepseek"):
            _require(
                bool(rc.api_key)
                and str(rc.api_key).strip() != "REPLACE_WITH_OPENAI_API_KEY",
                f"roles.{rc.name}: api_key is required for api.deepseek.com (set env DEEPSEEK_API_KEY or roles.{rc.name}.api_key)",
            )

    _require(
        cfg.search.failure_aggregation_max_rounds > 0,
        (
            "search.failure_aggregation_max_rounds must be > 0, "
            f"got {cfg.search.failure_aggregation_max_rounds}"
        ),
    )
    _require(
        cfg.search.failure_aggregation_max_patterns_per_round > 0,
        (
            "search.failure_aggregation_max_patterns_per_round must be > 0, "
            f"got {cfg.search.failure_aggregation_max_patterns_per_round}"
        ),
    )
    _require(
        0.0 <= cfg.search.planner_subgoal_near_restatement_similarity <= 1.0,
        (
            "search.planner_subgoal_near_restatement_similarity must be in [0,1], "
            f"got {cfg.search.planner_subgoal_near_restatement_similarity}"
        ),
    )
    _require(
        cfg.search.planner_subgoal_min_difficulty_drop >= 0.0,
        (
            "search.planner_subgoal_min_difficulty_drop must be >= 0, "
            f"got {cfg.search.planner_subgoal_min_difficulty_drop}"
        ),
    )
    _require(
        cfg.search.planner_subgoal_max_harder_delta >= 0.0,
        (
            "search.planner_subgoal_max_harder_delta must be >= 0, "
            f"got {cfg.search.planner_subgoal_max_harder_delta}"
        ),
    )
    _require(
        cfg.search.planner_replan_failed_subgoal_quarantine_rounds >= 0,
        (
            "search.planner_replan_failed_subgoal_quarantine_rounds must be >= 0, "
            f"got {cfg.search.planner_replan_failed_subgoal_quarantine_rounds}"
        ),
    )
    _require(
        cfg.search.planner_subgoal_falsify_max_subgoals >= 0,
        (
            "search.planner_subgoal_falsify_max_subgoals must be >= 0, "
            f"got {cfg.search.planner_subgoal_falsify_max_subgoals}"
        ),
    )
    _require(
        cfg.search.planner_subgoal_falsify_timeout_s >= 0.0,
        (
            "search.planner_subgoal_falsify_timeout_s must be >= 0, "
            f"got {cfg.search.planner_subgoal_falsify_timeout_s}"
        ),
    )
    _require(
        cfg.search.proof_potential_non_decrease_window >= 1,
        (
            "search.proof_potential_non_decrease_window must be >= 1, "
            f"got {cfg.search.proof_potential_non_decrease_window}"
        ),
    )
    _require(
        cfg.search.proof_potential_escape_budget >= 0,
        (
            "search.proof_potential_escape_budget must be >= 0, "
            f"got {cfg.search.proof_potential_escape_budget}"
        ),
    )
    _require(
        cfg.search.subgoal_compiler_max_variants >= 1,
        (
            "search.subgoal_compiler_max_variants must be >= 1, "
            f"got {cfg.search.subgoal_compiler_max_variants}"
        ),
    )
    _require(
        cfg.search.subgoal_compiler_max_prefix_chars >= 64,
        (
            "search.subgoal_compiler_max_prefix_chars must be >= 64, "
            f"got {cfg.search.subgoal_compiler_max_prefix_chars}"
        ),
    )

    for name, role_or_chain in cfg.roles.items():
        if isinstance(role_or_chain, list):
            _require(
                len(role_or_chain) > 0,
                f"roles.{name}: role list must include at least one model",
            )
            for idx, rc in enumerate(role_or_chain):
                if isinstance(rc, RoleConfig):
                    _check_role(rc)
                else:
                    errors.append(
                        f"roles.{name}[{idx}]: expected RoleConfig, got {type(rc).__name__}"
                    )
        elif isinstance(role_or_chain, RoleConfig):
            _check_role(role_or_chain)
        else:
            errors.append(
                f"roles.{name}: expected RoleConfig or list, got {type(role_or_chain).__name__}"
            )

    # --- Model pool checks ---
    pool_flags = getattr(cfg, "model_pool", None) or {}
    for role_name, enabled in pool_flags.items():
        _require(
            isinstance(enabled, bool),
            f"model_pool.{role_name}: expected boolean flag, got {type(enabled).__name__}",
        )
        if not isinstance(enabled, bool):
            continue
        if enabled:
            role_cfg = cfg.roles.get(role_name)
            _require(
                role_cfg is not None,
                f"model_pool.{role_name}: no matching roles.{role_name} config found",
            )
            if role_cfg is None:
                continue
            _require(
                isinstance(role_cfg, list),
                f"model_pool.{role_name}: pool mode requires a list of models, "
                f"but roles.{role_name} is a single config",
            )
    # Weight must be positive for all roles (only meaningful for pool mode)
    for name, role_or_chain in cfg.roles.items():
        if isinstance(role_or_chain, list):
            for rc in role_or_chain:
                _require(
                    rc.weight > 0,
                    f"roles.{name}: weight must be > 0, got {rc.weight} for model {rc.model}",
                )

    # --- Lean (C2: max_parallel=0 → Semaphore(0) deadlock at lean_runner.py:31) ---
    _require(
        cfg.lean.max_parallel >= 1,
        f"lean.max_parallel must be >= 1, got {cfg.lean.max_parallel}",
    )
    _require(
        cfg.lean.max_parallel <= 32,
        f"lean.max_parallel must be <= 32, got {cfg.lean.max_parallel}",
    )
    _require(
        cfg.lean.timeout_s > 0, f"lean.timeout_s must be > 0, got {cfg.lean.timeout_s}"
    )
    _require(
        cfg.lean.fast_fail_timeout_s > 0,
        f"lean.fast_fail_timeout_s must be > 0, got {cfg.lean.fast_fail_timeout_s}",
    )
    _require(
        cfg.lean.fast_fail_timeout_s <= cfg.lean.timeout_s,
        f"lean.fast_fail_timeout_s ({cfg.lean.fast_fail_timeout_s}) must be <= timeout_s ({cfg.lean.timeout_s})",
    )
    _require(
        str(cfg.lean.backend_mode).lower()
        in {"auto", "lake", "env_cached_subprocess", "persistent_process"},
        "lean.backend_mode must be one of auto|lake|env_cached_subprocess|persistent_process, "
        f"got {cfg.lean.backend_mode}",
    )
    _require(
        str(cfg.lean.precheck_mode).lower() in {"none", "typecheck", "strict"},
        "lean.precheck_mode must be one of none|typecheck|strict, "
        f"got {cfg.lean.precheck_mode}",
    )
    _require(
        float(cfg.lean.precheck_timeout_s) > 0.0,
        f"lean.precheck_timeout_s must be > 0, got {cfg.lean.precheck_timeout_s}",
    )
    _require(
        float(cfg.lean.precheck_timeout_s) <= float(cfg.lean.timeout_s),
        "lean.precheck_timeout_s must be <= lean.timeout_s, "
        f"got {cfg.lean.precheck_timeout_s} > {cfg.lean.timeout_s}",
    )
    _require(
        int(cfg.lean.precheck_max_heartbeats) > 0,
        "lean.precheck_max_heartbeats must be > 0, "
        f"got {cfg.lean.precheck_max_heartbeats}",
    )
    _require(
        int(cfg.lean.persistent_workers) >= 0,
        f"lean.persistent_workers must be >= 0, got {cfg.lean.persistent_workers}",
    )
    _require(
        int(cfg.lean.persistent_oracle_workers) >= 0,
        "lean.persistent_oracle_workers must be >= 0, "
        f"got {cfg.lean.persistent_oracle_workers}",
    )
    _require(
        float(cfg.lean.persistent_worker_idle_ttl_s) >= 0.0,
        "lean.persistent_worker_idle_ttl_s must be >= 0, "
        f"got {cfg.lean.persistent_worker_idle_ttl_s}",
    )
    _require(
        float(cfg.lean.persistent_worker_start_timeout_s) > 0.0,
        "lean.persistent_worker_start_timeout_s must be > 0, "
        f"got {cfg.lean.persistent_worker_start_timeout_s}",
    )
    _require(
        float(cfg.lean.persistent_request_timeout_buffer_s) >= 0.0,
        "lean.persistent_request_timeout_buffer_s must be >= 0, "
        f"got {cfg.lean.persistent_request_timeout_buffer_s}",
    )
    _require(
        int(cfg.lean.persistent_max_requests_per_worker) > 0,
        "lean.persistent_max_requests_per_worker must be > 0, "
        f"got {cfg.lean.persistent_max_requests_per_worker}",
    )
    _require(
        str(cfg.lean.persistent_protocol).lower() in {"lsp"},
        "lean.persistent_protocol must be one of lsp, "
        f"got {cfg.lean.persistent_protocol}",
    )
    if str(cfg.lean.backend_mode).lower() == "persistent_process":
        _require(
            int(cfg.lean.persistent_workers) > 0,
            "lean.persistent_workers must be > 0 when "
            "lean.backend_mode=persistent_process",
        )
    _require(
        int(cfg.lean.max_full_checks) >= 0,
        f"lean.max_full_checks must be >= 0, got {cfg.lean.max_full_checks}",
    )

    # --- Search ---
    _require(
        cfg.search.max_depth >= 0,
        f"search.max_depth must be >= 0, got {cfg.search.max_depth}",
    )
    _require(
        cfg.search.max_goals >= 1,
        f"search.max_goals must be >= 1, got {cfg.search.max_goals}",
    )
    _require(
        cfg.search.max_attempts_per_goal >= 1,
        f"search.max_attempts_per_goal must be >= 1, got {cfg.search.max_attempts_per_goal}",
    )
    _require(
        cfg.search.candidates_per_goal >= 1,
        f"search.candidates_per_goal must be >= 1, got {cfg.search.candidates_per_goal}",
    )
    _require(
        cfg.search.best_of_n >= 1,
        f"search.best_of_n must be >= 1, got {cfg.search.best_of_n}",
    )
    _require(
        cfg.search.parallel_goals >= 1,
        f"search.parallel_goals must be >= 1, got {cfg.search.parallel_goals}",
    )
    _require(
        int(cfg.search.parallel_candidate_window) >= 0,
        "search.parallel_candidate_window must be >= 0, "
        f"got {cfg.search.parallel_candidate_window}",
    )
    _require(
        int(cfg.search.plan_locked_max_refinements) >= 0,
        "search.plan_locked_max_refinements must be >= 0, "
        f"got {cfg.search.plan_locked_max_refinements}",
    )
    _require(
        cfg.search.tactic_beam_width >= 1,
        f"search.tactic_beam_width must be >= 1, got {cfg.search.tactic_beam_width}",
    )
    _require(
        cfg.search.tactic_max_steps >= 1,
        f"search.tactic_max_steps must be >= 1, got {cfg.search.tactic_max_steps}",
    )
    _require(
        0.0 <= cfg.search.boilerplate_early_exit_threshold <= 1.0,
        f"search.boilerplate_early_exit_threshold must be in [0,1], got {cfg.search.boilerplate_early_exit_threshold}",
    )
    _require(
        cfg.search.full_goal_state_budget_tokens >= 0,
        f"search.full_goal_state_budget_tokens must be >= 0, got {cfg.search.full_goal_state_budget_tokens}",
    )
    _require(
        cfg.search.full_goal_state_max_goals >= 0,
        f"search.full_goal_state_max_goals must be >= 0, got {cfg.search.full_goal_state_max_goals}",
    )
    _require(
        cfg.search.max_context_solved_lemmas >= 0,
        f"search.max_context_solved_lemmas must be >= 0, got {cfg.search.max_context_solved_lemmas}",
    )
    _require(
        cfg.search.curriculum_band_width > 0.0,
        f"search.curriculum_band_width must be > 0, got {cfg.search.curriculum_band_width}",
    )
    _require(
        cfg.search.max_replans >= 0,
        f"search.max_replans must be >= 0, got {cfg.search.max_replans}",
    )
    _require(
        cfg.search.min_replan_time_s >= 0,
        f"search.min_replan_time_s must be >= 0, got {cfg.search.min_replan_time_s}",
    )
    _require(
        isinstance(cfg.search.budget_only_unsolved_termination, bool),
        (
            "search.budget_only_unsolved_termination must be a bool, "
            f"got {type(cfg.search.budget_only_unsolved_termination).__name__}"
        ),
    )
    _require(
        str(cfg.search.composition_prover_role).strip().lower()
        in {"prover", "refiner", "planner"},
        (
            "search.composition_prover_role must be one of "
            "{'prover','refiner','planner'}, "
            f"got {cfg.search.composition_prover_role!r}"
        ),
    )
    _require(
        isinstance(cfg.search.composition_refine_failures, bool),
        (
            "search.composition_refine_failures must be a bool, "
            f"got {type(cfg.search.composition_refine_failures).__name__}"
        ),
    )
    _require(
        cfg.search.composition_refine_max_failures_per_round >= 0,
        (
            "search.composition_refine_max_failures_per_round must be >= 0, "
            f"got {cfg.search.composition_refine_max_failures_per_round}"
        ),
    )
    _require(
        cfg.search.refine_max_failures_per_round >= 0,
        (
            "search.refine_max_failures_per_round must be >= 0, "
            f"got {cfg.search.refine_max_failures_per_round}"
        ),
    )
    _require(
        cfg.search.composition_refine_turns >= 1,
        (
            "search.composition_refine_turns must be >= 1, "
            f"got {cfg.search.composition_refine_turns}"
        ),
    )
    _require(
        0.05 <= cfg.search.prover_temp_ceiling <= 1.5,
        f"search.prover_temp_ceiling must be in [0.05, 1.5], got {cfg.search.prover_temp_ceiling}",
    )
    _require(
        0.05 <= cfg.search.refiner_temp_ceiling <= 1.5,
        f"search.refiner_temp_ceiling must be in [0.05, 1.5], got {cfg.search.refiner_temp_ceiling}",
    )
    _require(
        0.05 <= cfg.search.planner_temp_ceiling <= 1.5,
        f"search.planner_temp_ceiling must be in [0.05, 1.5], got {cfg.search.planner_temp_ceiling}",
    )
    _require(
        cfg.search.planner_llm_calls_budget >= 1,
        (
            "search.planner_llm_calls_budget must be >= 1, "
            f"got {cfg.search.planner_llm_calls_budget}"
        ),
    )
    _require(
        cfg.search.planner_llm_calls_reserve_for_plan_subgoals >= 0,
        (
            "search.planner_llm_calls_reserve_for_plan_subgoals must be >= 0, "
            f"got {cfg.search.planner_llm_calls_reserve_for_plan_subgoals}"
        ),
    )
    _require(
        cfg.search.planner_llm_calls_reserve_for_plan_subgoals
        <= cfg.search.planner_llm_calls_budget,
        (
            "search.planner_llm_calls_reserve_for_plan_subgoals must be <= "
            f"planner_llm_calls_budget ({cfg.search.planner_llm_calls_budget}), "
            f"got {cfg.search.planner_llm_calls_reserve_for_plan_subgoals}"
        ),
    )
    _require(
        cfg.search.temperature_mode in ("adaptive", "bandit", "fixed", "round_robin"),
        f"search.temperature_mode must be one of adaptive/bandit/fixed/round_robin, "
        f"got {cfg.search.temperature_mode!r}",
    )
    _require(
        len(cfg.search.temperature_bandit_arms) >= 2,
        f"search.temperature_bandit_arms must have >= 2 arms, "
        f"got {len(cfg.search.temperature_bandit_arms)}",
    )
    _require(
        0.0 <= cfg.search.temperature_bandit_carry <= 1.0,
        f"search.temperature_bandit_carry must be in [0.0, 1.0], "
        f"got {cfg.search.temperature_bandit_carry}",
    )
    _require(
        len(cfg.search.temperature_round_robin_temps) >= 1,
        "search.temperature_round_robin_temps must have >= 1 entry",
    )
    _require(
        0.01 <= cfg.search.temperature_fixed_value <= 2.0,
        f"search.temperature_fixed_value must be in [0.01, 2.0], "
        f"got {cfg.search.temperature_fixed_value}",
    )
    _require(
        cfg.search.refiner_replan_reserved_calls >= 0,
        (
            "search.refiner_replan_reserved_calls must be >= 0, "
            f"got {cfg.search.refiner_replan_reserved_calls}"
        ),
    )
    _require(
        0.0 <= cfg.search.prover_temp_ema_alpha <= 1.0,
        f"search.prover_temp_ema_alpha must be in [0.0, 1.0], "
        f"got {cfg.search.prover_temp_ema_alpha}",
    )
    _require(
        cfg.search.fast_path_probe_timeout_s > 0.0,
        (
            "search.fast_path_probe_timeout_s must be > 0, "
            f"got {cfg.search.fast_path_probe_timeout_s}"
        ),
    )
    _require(
        0.0 <= cfg.search.stale_check_time_floor_fraction <= 1.0,
        (
            "search.stale_check_time_floor_fraction must be in [0,1], "
            f"got {cfg.search.stale_check_time_floor_fraction}"
        ),
    )

    # --- Strategy ---
    _require(
        cfg.strategy.mode in ("linear", "beam", "mcts", "tactic_tree"),
        f"strategy.mode must be linear|beam|mcts|tactic_tree, got '{cfg.strategy.mode}'",
    )
    _require(
        cfg.strategy.beam_width >= 1,
        f"strategy.beam_width must be >= 1, got {cfg.strategy.beam_width}",
    )
    _require(
        cfg.strategy.mcts_simulations >= 1,
        f"strategy.mcts_simulations must be >= 1, got {cfg.strategy.mcts_simulations}",
    )

    # --- Budgets ---
    _require(
        cfg.budgets.time_seconds > 0,
        f"budgets.time_seconds must be > 0, got {cfg.budgets.time_seconds}",
    )
    _require(
        cfg.budgets.max_total_attempts > 0,
        f"budgets.max_total_attempts must be > 0, got {cfg.budgets.max_total_attempts}",
    )
    _require(
        0.0 < cfg.budgets.stale_fraction <= 1.0,
        f"budgets.stale_fraction must be in (0, 1], got {cfg.budgets.stale_fraction}",
    )
    _require(
        cfg.budgets.early_exit_min_iterations >= 1,
        f"budgets.early_exit_min_iterations must be >= 1, got {cfg.budgets.early_exit_min_iterations}",
    )
    _require(
        cfg.budgets.max_cost_per_problem_usd >= 0,
        f"budgets.max_cost_per_problem_usd must be >= 0, got {cfg.budgets.max_cost_per_problem_usd}",
    )
    _require(
        cfg.budgets.max_sweep_cost_usd >= 0,
        f"budgets.max_sweep_cost_usd must be >= 0, got {cfg.budgets.max_sweep_cost_usd}",
    )
    _require(
        0.01 <= cfg.budgets.beam_restart_temp_boost <= 0.5,
        f"budgets.beam_restart_temp_boost must be in [0.01, 0.5], got {cfg.budgets.beam_restart_temp_boost}",
    )
    _require(
        1.0 <= cfg.budgets.beam_restart_temp_cap <= 2.0,
        f"budgets.beam_restart_temp_cap must be in [1.0, 2.0], got {cfg.budgets.beam_restart_temp_cap}",
    )

    # --- Cost pricing sanity ---
    role_pricing = []
    role_pricing_known = True
    for rc in _flatten_role_configs():
        pricing = lookup_known_token_pricing(rc.base_url, rc.model)
        if pricing is None:
            role_pricing_known = False
            break
        role_pricing.append(pricing)
    cfg_pricing = (
        float(cfg.token_pricing.input_per_m),
        float(cfg.token_pricing.cached_per_m),
        float(cfg.token_pricing.output_per_m),
    )
    has_cfg_pricing = any(v > 0 for v in cfg_pricing)
    if role_pricing and role_pricing_known:
        unique_role_pricing = {tuple(p) for p in role_pricing}
        if len(unique_role_pricing) == 1 and has_cfg_pricing:
            expected = next(iter(unique_role_pricing))
            _require(
                cfg_pricing == expected,
                (
                    "token_pricing does not match the configured role model pricing; "
                    f"expected {expected}, got {cfg_pricing}"
                ),
            )
        elif len(unique_role_pricing) > 1 and has_cfg_pricing:
            _require(
                False,
                (
                    "token_pricing is ambiguous for mixed model/provider roles; "
                    "leave it unset/zero and let runtime per-role pricing handle cost accounting"
                ),
            )

    # --- Ensemble (C3: embedding_dim=0 silently disables embeddings) ---
    e = cfg.ensemble
    _require(
        e.embedding_dim >= 1,
        f"ensemble.embedding_dim must be >= 1, got {e.embedding_dim}",
    )
    _require(
        e.embedding_dim == 768,
        f"ensemble.embedding_dim must be 768, got {e.embedding_dim}",
    )
    _require(
        e.memory_size >= 1, f"ensemble.memory_size must be >= 1, got {e.memory_size}"
    )
    _require(
        e.recent_window >= 1,
        f"ensemble.recent_window must be >= 1, got {e.recent_window}",
    )
    _require(
        e.weight_active_goal >= 0.0,
        f"ensemble.weight_active_goal must be >= 0, got {e.weight_active_goal}",
    )
    # Min/max range pairs
    _require(
        e.epsilon_min <= e.epsilon_max,
        f"ensemble: epsilon_min ({e.epsilon_min}) must be <= epsilon_max ({e.epsilon_max})",
    )
    _require(
        e.r_star_min <= e.r_star_max,
        f"ensemble: r_star_min ({e.r_star_min}) must be <= r_star_max ({e.r_star_max})",
    )
    _require(
        e.tau_min <= e.tau_max,
        f"ensemble: tau_min ({e.tau_min}) must be <= tau_max ({e.tau_max})",
    )
    _require(
        e.eps_explore_min <= e.eps_explore_max,
        f"ensemble: eps_explore_min ({e.eps_explore_min}) must be <= eps_explore_max ({e.eps_explore_max})",
    )
    # Initial values within their ranges
    _require(
        e.epsilon_min <= e.epsilon0 <= e.epsilon_max,
        f"ensemble: epsilon0 ({e.epsilon0}) must be in [{e.epsilon_min}, {e.epsilon_max}]",
    )
    _require(
        e.r_star_min <= e.r_star0 <= e.r_star_max,
        f"ensemble: r_star0 ({e.r_star0}) must be in [{e.r_star_min}, {e.r_star_max}]",
    )
    _require(
        0.0 <= e.depth_r_star_decay <= 1.0,
        f"ensemble: depth_r_star_decay must be in [0,1], got {e.depth_r_star_decay}",
    )
    _require(
        0.0 < e.depth_r_star_floor <= 1.0,
        f"ensemble: depth_r_star_floor must be in (0,1], got {e.depth_r_star_floor}",
    )
    _event = str(getattr(e, "epsilon_homeostasis_event", "hit_rate") or "hit_rate")
    _allowed = {
        "hit_rate",
        "success_rate",
        "progress_rate",
        "success_or_progress",
        "blend",
    }
    _require(
        _event in _allowed,
        f"ensemble: epsilon_homeostasis_event must be one of {sorted(_allowed)}, got '{_event}'",
    )
    _require(
        0.0 <= float(getattr(e, "epsilon_homeostasis_blend_weight", 0.6)) <= 1.0,
        f"ensemble: epsilon_homeostasis_blend_weight must be in [0,1], got {e.epsilon_homeostasis_blend_weight}",
    )
    _require(
        e.tau_min <= e.tau0 <= e.tau_max,
        f"ensemble: tau0 ({e.tau0}) must be in [{e.tau_min}, {e.tau_max}]",
    )
    _require(
        e.eps_explore_min <= e.eps_explore0 <= e.eps_explore_max,
        f"ensemble: eps_explore0 ({e.eps_explore0}) must be in [{e.eps_explore_min}, {e.eps_explore_max}]",
    )
    _require(
        e.stall_failure_streak_threshold >= 1,
        f"ensemble.stall_failure_streak_threshold must be >= 1, got {e.stall_failure_streak_threshold}",
    )
    _require(
        0.0 <= e.stall_success_rate_threshold <= 1.0,
        f"ensemble.stall_success_rate_threshold must be in [0,1], got {e.stall_success_rate_threshold}",
    )
    _require(
        0.0 <= e.stall_decay_floor <= 1.0,
        f"ensemble.stall_decay_floor must be in [0,1], got {e.stall_decay_floor}",
    )
    _require(
        0.0 <= e.guidance_min_policy_conf <= 1.0,
        f"ensemble.guidance_min_policy_conf must be in [0,1], got {e.guidance_min_policy_conf}",
    )
    _require(
        0.0 <= e.guidance_min_value_conf <= 1.0,
        f"ensemble.guidance_min_value_conf must be in [0,1], got {e.guidance_min_value_conf}",
    )
    # Learning rates and regularization
    _require(
        e.embedding_lr > 0, f"ensemble.embedding_lr must be > 0, got {e.embedding_lr}"
    )
    _require(
        e.world_model_lr > 0,
        f"ensemble.world_model_lr must be > 0, got {e.world_model_lr}",
    )
    _require(e.utility_lr > 0, f"ensemble.utility_lr must be > 0, got {e.utility_lr}")
    _require(
        e.weight_decay >= 0, f"ensemble.weight_decay must be >= 0, got {e.weight_decay}"
    )
    _require(
        e.model_hidden_dim >= 1,
        f"ensemble.model_hidden_dim must be >= 1, got {e.model_hidden_dim}",
    )
    _require(
        e.replay_buffer_size >= 0,
        f"ensemble.replay_buffer_size must be >= 0, got {e.replay_buffer_size}",
    )
    _require(
        e.replay_batch >= 0, f"ensemble.replay_batch must be >= 0, got {e.replay_batch}"
    )
    _require(
        0 < e.replay_lr_scale <= 1.0,
        f"ensemble.replay_lr_scale must be in (0,1], got {e.replay_lr_scale}",
    )
    _require(
        0 < e.hidden_lr_scale <= 1.0,
        f"ensemble.hidden_lr_scale must be in (0,1], got {e.hidden_lr_scale}",
    )
    # Grow/prune, quality, diversity
    _require(e.grow_rate > 0, f"ensemble.grow_rate must be > 0, got {e.grow_rate}")
    _require(e.prune_rate > 0, f"ensemble.prune_rate must be > 0, got {e.prune_rate}")
    _require(
        e.quality_line_target > 0,
        f"ensemble.quality_line_target must be > 0, got {e.quality_line_target}",
    )
    _require(
        e.quality_tactic_target > 0,
        f"ensemble.quality_tactic_target must be > 0, got {e.quality_tactic_target}",
    )
    _require(
        e.diversity_min_strategies >= 1,
        f"ensemble.diversity_min_strategies must be >= 1, got {e.diversity_min_strategies}",
    )
    _require(
        0.0 <= e.strategy_prior_weight <= 1.0,
        f"ensemble.strategy_prior_weight must be in [0,1], got {e.strategy_prior_weight}",
    )
    _require(
        e.meo_ast_difficulty_timeout_s >= 0,
        f"ensemble.meo_ast_difficulty_timeout_s must be >= 0, got {e.meo_ast_difficulty_timeout_s}",
    )
    _require(
        e.meo_difficulty_cache_size >= 0,
        f"ensemble.meo_difficulty_cache_size must be >= 0, got {e.meo_difficulty_cache_size}",
    )
    if e.online_models_path is not None:
        _require(
            bool(str(e.online_models_path).strip()),
            "ensemble.online_models_path must be a non-empty path when provided",
        )
    _require(
        e.guidance_autotrain_min_examples >= 0,
        f"ensemble.guidance_autotrain_min_examples must be >= 0, got {e.guidance_autotrain_min_examples}",
    )
    _require(
        e.guidance_autotrain_min_new_examples >= 0,
        f"ensemble.guidance_autotrain_min_new_examples must be >= 0, got {e.guidance_autotrain_min_new_examples}",
    )
    _require(
        e.guidance_autotrain_max_examples >= 0,
        f"ensemble.guidance_autotrain_max_examples must be >= 0, got {e.guidance_autotrain_max_examples}",
    )
    _require(
        e.tactic_lexicon_promote_support >= 1,
        (
            "ensemble.tactic_lexicon_promote_support must be >= 1, "
            f"got {e.tactic_lexicon_promote_support}"
        ),
    )
    _require(
        0.0 <= e.tactic_lexicon_unknown_prior <= 1.0,
        (
            "ensemble.tactic_lexicon_unknown_prior must be in [0,1], "
            f"got {e.tactic_lexicon_unknown_prior}"
        ),
    )
    _require(
        e.tactic_lexicon_demote_after_failures >= 1,
        (
            "ensemble.tactic_lexicon_demote_after_failures must be >= 1, "
            f"got {e.tactic_lexicon_demote_after_failures}"
        ),
    )
    _require(
        0.0 <= e.tactic_lexicon_demote_decay <= 1.0,
        (
            "ensemble.tactic_lexicon_demote_decay must be in [0,1], "
            f"got {e.tactic_lexicon_demote_decay}"
        ),
    )
    _require(
        e.meo_policy_refresh_cycle >= 0,
        f"ensemble.meo_policy_refresh_cycle must be >= 0, got {e.meo_policy_refresh_cycle}",
    )
    _require(
        0.0 <= e.memory_failed_strategy_gate_threshold <= 1.0,
        f"ensemble.memory_failed_strategy_gate_threshold must be in [0,1], got {e.memory_failed_strategy_gate_threshold}",
    )
    _require(
        0.0 <= e.memory_failed_strategy_min_recent_success <= 1.0,
        f"ensemble.memory_failed_strategy_min_recent_success must be in [0,1], got {e.memory_failed_strategy_min_recent_success}",
    )
    _require(
        e.memory_failed_strategy_min_local_support >= 1,
        f"ensemble.memory_failed_strategy_min_local_support must be >= 1, got {e.memory_failed_strategy_min_local_support}",
    )
    _require(
        e.memory_failed_strategy_recent_prior_strength >= 0,
        f"ensemble.memory_failed_strategy_recent_prior_strength must be >= 0, got {e.memory_failed_strategy_recent_prior_strength}",
    )
    _require(
        e.failed_strategy_prior_penalty >= 0.0,
        f"ensemble.failed_strategy_prior_penalty must be >= 0, got {e.failed_strategy_prior_penalty}",
    )
    _require(
        e.memory_embedding_backend == "sentence_transformers",
        "ensemble.memory_embedding_backend must be 'sentence_transformers', "
        f"got '{e.memory_embedding_backend}'",
    )
    _require(
        e.memory_embedding_init_timeout_s > 0.0,
        f"ensemble.memory_embedding_init_timeout_s must be > 0, got {e.memory_embedding_init_timeout_s}",
    )
    _require(
        not e.adaptive_embedding,
        "ensemble.adaptive_embedding is no longer supported; use fixed sentence-transformer embeddings",
    )
    # Curiosity parameters
    _require(
        e.curiosity_novelty_scale >= 0,
        f"ensemble.curiosity_novelty_scale must be >= 0, got {e.curiosity_novelty_scale}",
    )
    _require(
        e.curiosity_novelty_k >= 1,
        f"ensemble.curiosity_novelty_k must be >= 1, got {e.curiosity_novelty_k}",
    )
    _require(
        e.curiosity_decay_window >= 1,
        f"ensemble.curiosity_decay_window must be >= 1, got {e.curiosity_decay_window}",
    )
    # Blend ramp parameters (blend_max > 1.0 inverts memory utility signal)
    _require(
        0.0 <= e.blend_max <= 1.0,
        f"ensemble.blend_max must be in [0,1], got {e.blend_max}",
    )
    _require(
        e.blend_warmup >= 1, f"ensemble.blend_warmup must be >= 1, got {e.blend_warmup}"
    )
    _require(
        e.controller_mode in {"auto", "formal", "learned"},
        "ensemble.controller_mode must be one of {'auto','formal','learned'}, "
        f"got {e.controller_mode!r}",
    )
    _require(
        0.0 <= e.blend_threshold_tau <= 1.0,
        f"ensemble.blend_threshold_tau must be in [0,1], got {e.blend_threshold_tau}",
    )
    _require(
        0.0 <= e.admission_formal_threshold <= 1.0,
        "ensemble.admission_formal_threshold must be in [0,1], "
        f"got {e.admission_formal_threshold}",
    )
    _require(
        0.0 <= e.admission_learned_threshold <= 1.0,
        "ensemble.admission_learned_threshold must be in [0,1], "
        f"got {e.admission_learned_threshold}",
    )
    _require(
        e.admission_floor >= 0,
        f"ensemble.admission_floor must be >= 0, got {e.admission_floor}",
    )
    _require(
        e.formal_consistency_mode in {"syntactic", "theorem_prover"},
        "ensemble.formal_consistency_mode must be one of {'syntactic','theorem_prover'}, "
        f"got {e.formal_consistency_mode!r}",
    )
    _require(
        0.0 <= e.learned_collapse_threshold <= 1.0,
        "ensemble.learned_collapse_threshold must be in [0,1], "
        f"got {e.learned_collapse_threshold}",
    )
    _require(
        0.0 <= e.learned_collapse_similarity_threshold <= 1.0,
        "ensemble.learned_collapse_similarity_threshold must be in [0,1], "
        f"got {e.learned_collapse_similarity_threshold}",
    )
    _require(
        e.delta_geometry_epsilon_min <= e.delta_geometry_epsilon_max,
        (
            "ensemble.delta_geometry_epsilon_min "
            f"({e.delta_geometry_epsilon_min}) must be <= "
            f"delta_geometry_epsilon_max ({e.delta_geometry_epsilon_max})"
        ),
    )
    _require(
        e.delta_geometry_epsilon_min
        <= e.delta_geometry_epsilon0
        <= e.delta_geometry_epsilon_max,
        (
            "ensemble.delta_geometry_epsilon0 "
            f"({e.delta_geometry_epsilon0}) must be in "
            f"[{e.delta_geometry_epsilon_min}, {e.delta_geometry_epsilon_max}]"
        ),
    )
    _require(
        0.0 < e.delta_geometry_cov_beta <= 1.0,
        "ensemble.delta_geometry_cov_beta must be in (0,1], "
        f"got {e.delta_geometry_cov_beta}",
    )
    _require(
        0.0 <= e.delta_geometry_shrinkage <= 1.0,
        "ensemble.delta_geometry_shrinkage must be in [0,1], "
        f"got {e.delta_geometry_shrinkage}",
    )
    _require(
        e.delta_geometry_metric_mode
        in {"whitened", "learned_spd", "mixture", "mixture_learned_spd"},
        "ensemble.delta_geometry_metric_mode must be one of "
        "{'whitened','learned_spd','mixture','mixture_learned_spd'}, "
        f"got {e.delta_geometry_metric_mode!r}",
    )
    _require(
        e.delta_geometry_regimes >= 1,
        f"ensemble.delta_geometry_regimes must be >= 1, got {e.delta_geometry_regimes}",
    )
    _require(
        0.0 <= e.delta_geometry_selector_lr <= 1.0,
        "ensemble.delta_geometry_selector_lr must be in [0,1], "
        f"got {e.delta_geometry_selector_lr}",
    )
    _require(
        0.0 <= e.delta_geometry_learned_metric_blend <= 1.0,
        "ensemble.delta_geometry_learned_metric_blend must be in [0,1], "
        f"got {e.delta_geometry_learned_metric_blend}",
    )
    _require(
        len(e.growth_action_dims) >= 1,
        "ensemble.growth_action_dims must contain at least one dimension",
    )
    _require(
        len(e.prune_action_dims) >= 1,
        "ensemble.prune_action_dims must contain at least one dimension",
    )
    _require(
        all(str(dim).strip() for dim in e.growth_action_dims),
        "ensemble.growth_action_dims may not contain empty values",
    )
    _require(
        all(str(dim).strip() for dim in e.prune_action_dims),
        "ensemble.prune_action_dims may not contain empty values",
    )
    _supported_growth_dims = {
        "search_width",
        "retrieval_width",
        "closure_scope",
        "temperature",
    }
    _supported_prune_dims = {
        "verification_strictness",
        "search_width",
        "retrieval_width",
        "closure_scope",
        "temperature",
    }
    _invalid_growth_dims = sorted(
        {str(dim).strip() for dim in e.growth_action_dims if str(dim).strip()}
        - _supported_growth_dims
    )
    _invalid_prune_dims = sorted(
        {str(dim).strip() for dim in e.prune_action_dims if str(dim).strip()}
        - _supported_prune_dims
    )
    _require(
        not _invalid_growth_dims,
        "ensemble.growth_action_dims contains unsupported values: "
        f"{_invalid_growth_dims}. Supported: {sorted(_supported_growth_dims)}",
    )
    _require(
        not _invalid_prune_dims,
        "ensemble.prune_action_dims contains unsupported values: "
        f"{_invalid_prune_dims}. Supported: {sorted(_supported_prune_dims)}",
    )
    _require(
        e.precision_lr >= 0.0,
        f"ensemble.precision_lr must be >= 0, got {e.precision_lr}",
    )
    _require(
        e.precision_min > 0.0,
        f"ensemble.precision_min must be > 0, got {e.precision_min}",
    )
    _require(
        e.precision_min <= e.precision_max,
        f"ensemble.precision_min ({e.precision_min}) must be <= precision_max ({e.precision_max})",
    )
    _require(
        0.0 < e.spd_cov_beta <= 1.0,
        f"ensemble.spd_cov_beta must be in (0,1], got {e.spd_cov_beta}",
    )
    _require(
        0.0 <= e.spd_cov_shrinkage <= 1.0,
        f"ensemble.spd_cov_shrinkage must be in [0,1], got {e.spd_cov_shrinkage}",
    )
    _require(
        e.spd_cov_jitter > 0.0,
        f"ensemble.spd_cov_jitter must be > 0, got {e.spd_cov_jitter}",
    )
    _require(
        e.spd_cov_min_variance > 0.0,
        f"ensemble.spd_cov_min_variance must be > 0, got {e.spd_cov_min_variance}",
    )
    _require(
        0.0 < e.spd_tail_quantile < 1.0,
        f"ensemble.spd_tail_quantile must be in (0,1), got {e.spd_tail_quantile}",
    )
    # Delta-homeostasis range checks
    _require(
        0.0 <= e.delta_homeostasis_lambda <= 1.0,
        f"ensemble.delta_homeostasis_lambda must be in [0,1], got {e.delta_homeostasis_lambda}",
    )
    _require(
        0.0 <= e.delta_homeostasis_sigma_blend <= 1.0,
        f"ensemble.delta_homeostasis_sigma_blend must be in [0,1], got {e.delta_homeostasis_sigma_blend}",
    )
    _require(
        0.0 <= e.delta_homeostasis_precision_blend <= 1.0,
        f"ensemble.delta_homeostasis_precision_blend must be in [0,1], got {e.delta_homeostasis_precision_blend}",
    )
    _require(
        0.0 <= e.delta_homeostasis_score_factor <= 1.0,
        f"ensemble.delta_homeostasis_score_factor must be in [0,1], got {e.delta_homeostasis_score_factor}",
    )
    _require(
        0.0 <= e.delta_homeostasis_closure_factor <= 1.0,
        f"ensemble.delta_homeostasis_closure_factor must be in [0,1], got {e.delta_homeostasis_closure_factor}",
    )
    # Phase 3D / online-model / meta-signal fields
    _require(
        0.0 <= e.memory_success_reserve_ratio <= 1.0,
        f"ensemble.memory_success_reserve_ratio must be in [0,1], got {e.memory_success_reserve_ratio}",
    )
    _require(
        e.meta_signal_w_success >= 0,
        f"ensemble.meta_signal_w_success must be >= 0, got {e.meta_signal_w_success}",
    )
    _require(
        e.meta_signal_w_reward >= 0,
        f"ensemble.meta_signal_w_reward must be >= 0, got {e.meta_signal_w_reward}",
    )
    _require(
        e.meta_signal_w_delta >= 0,
        f"ensemble.meta_signal_w_delta must be >= 0, got {e.meta_signal_w_delta}",
    )
    _require(
        e.meta_signal_w_wm >= 0,
        f"ensemble.meta_signal_w_wm must be >= 0, got {e.meta_signal_w_wm}",
    )
    _require(
        0.0 <= e.stall_progress_attenuation_threshold <= 1.0,
        f"ensemble.stall_progress_attenuation_threshold must be in [0,1], got {e.stall_progress_attenuation_threshold}",
    )
    _require(
        e.blend_warmup_global >= 0,
        f"ensemble.blend_warmup_global must be >= 0, got {e.blend_warmup_global}",
    )
    _require(
        0.0 <= e.blend_global_floor <= 1.0,
        f"ensemble.blend_global_floor must be in [0,1], got {e.blend_global_floor}",
    )
    _require(
        cfg.search.max_refiner_calls_per_problem >= 0,
        f"search.max_refiner_calls_per_problem must be >= 0, got {cfg.search.max_refiner_calls_per_problem}",
    )
    # v2.2 forward model
    _require(
        0.0 < e.forward_model_lr <= 1.0,
        f"ensemble.forward_model_lr must be in (0,1], got {e.forward_model_lr}",
    )
    _require(
        e.forward_model_history_len >= 2,
        f"ensemble.forward_model_history_len must be >= 2, got {e.forward_model_history_len}",
    )
    _require(
        e.forward_model_residual_capacity >= 1,
        f"ensemble.forward_model_residual_capacity must be >= 1, got {e.forward_model_residual_capacity}",
    )
    _require(
        e.forward_model_clip_interval >= 1,
        f"ensemble.forward_model_clip_interval must be >= 1, got {e.forward_model_clip_interval}",
    )
    # v2.2 Layer 2
    _require(
        0.0 <= e.layer2_whitened_cov_beta <= 1.0,
        f"ensemble.layer2_whitened_cov_beta must be in [0,1], got {e.layer2_whitened_cov_beta}",
    )
    _require(
        e.layer2_theta_aniso > 0.0,
        f"ensemble.layer2_theta_aniso must be > 0, got {e.layer2_theta_aniso}",
    )
    _require(
        0.0 <= e.layer2_theta_align <= 1.0,
        f"ensemble.layer2_theta_align must be in [0,1], got {e.layer2_theta_align}",
    )
    _require(
        0.0 <= e.layer2_gamma_dir <= 1.0,
        f"ensemble.layer2_gamma_dir must be in [0,1], got {e.layer2_gamma_dir}",
    )
    _require(
        e.layer2_buffer_capacity >= 1,
        f"ensemble.layer2_buffer_capacity must be >= 1, got {e.layer2_buffer_capacity}",
    )
    # v2.2 Layer 3
    _require(
        e.layer3_min_cluster_size >= 1,
        f"ensemble.layer3_min_cluster_size must be >= 1, got {e.layer3_min_cluster_size}",
    )
    _require(
        e.layer3_gram_history_capacity >= 1,
        f"ensemble.layer3_gram_history_capacity must be >= 1, got {e.layer3_gram_history_capacity}",
    )
    # v2.2 Rupture
    _require(
        e.rupture_theta_stall >= 1,
        f"ensemble.rupture_theta_stall must be >= 1, got {e.rupture_theta_stall}",
    )
    _require(
        e.rupture_theta_pressure > 0.0,
        f"ensemble.rupture_theta_pressure must be > 0, got {e.rupture_theta_pressure}",
    )
    _require(
        0.0 < e.rupture_pressure_decay <= 1.0,
        f"ensemble.rupture_pressure_decay must be in (0,1], got {e.rupture_pressure_decay}",
    )

    # --- Tactic tree ---
    tt = cfg.tactic_tree
    _require(
        tt.mode in ("beam", "mcts"),
        f"tactic_tree.mode must be beam|mcts, got '{tt.mode}'",
    )
    _require(
        tt.beam_width >= 1, f"tactic_tree.beam_width must be >= 1, got {tt.beam_width}"
    )
    _require(
        tt.max_steps >= 1, f"tactic_tree.max_steps must be >= 1, got {tt.max_steps}"
    )
    _require(
        tt.max_candidates_per_node >= 1,
        f"tactic_tree.max_candidates_per_node must be >= 1, got {tt.max_candidates_per_node}",
    )
    _require(
        tt.max_depth >= 1, f"tactic_tree.max_depth must be >= 1, got {tt.max_depth}"
    )
    _require(
        tt.recursive_max_depth >= 0,
        f"tactic_tree.recursive_max_depth must be >= 0, got {tt.recursive_max_depth}",
    )
    _require(
        tt.recursive_max_nodes >= 1,
        f"tactic_tree.recursive_max_nodes must be >= 1, got {tt.recursive_max_nodes}",
    )
    _require(
        tt.recursive_retrieval_rounds >= 0,
        "tactic_tree.recursive_retrieval_rounds must be >= 0, "
        f"got {tt.recursive_retrieval_rounds}",
    )
    _require(
        tt.recursive_direct_rounds >= 0,
        "tactic_tree.recursive_direct_rounds must be >= 0, "
        f"got {tt.recursive_direct_rounds}",
    )
    _require(
        tt.recursive_assembly_rounds >= 0,
        "tactic_tree.recursive_assembly_rounds must be >= 0, "
        f"got {tt.recursive_assembly_rounds}",
    )
    _require(
        tt.recursive_tactic_tree_time_limit >= 0.0,
        "tactic_tree.recursive_tactic_tree_time_limit must be >= 0, "
        f"got {tt.recursive_tactic_tree_time_limit}",
    )
    # --- Retrieval ---
    r = cfg.retrieval
    _require(
        r.max_lemmas >= 1, f"retrieval.max_lemmas must be >= 1, got {r.max_lemmas}"
    )
    _require(r.top_k >= 1, f"retrieval.top_k must be >= 1, got {r.top_k}")
    _require(
        r.max_prompt_lemmas >= 1,
        f"retrieval.max_prompt_lemmas must be >= 1, got {r.max_prompt_lemmas}",
    )
    _require(
        r.max_prompt_lemmas <= r.top_k,
        f"retrieval: max_prompt_lemmas ({r.max_prompt_lemmas}) must be <= top_k ({r.top_k})",
    )
    _require(r.min_score >= 0.0, f"retrieval.min_score must be >= 0, got {r.min_score}")
    _require(r.bm25_k1 > 0.0, f"retrieval.bm25_k1 must be > 0, got {r.bm25_k1}")
    _require(
        0.0 <= r.bm25_b <= 1.0, f"retrieval.bm25_b must be in [0,1], got {r.bm25_b}"
    )
    _require(
        r.weight_bm25 >= 0.0, f"retrieval.weight_bm25 must be >= 0, got {r.weight_bm25}"
    )
    _require(
        r.weight_symbol >= 0.0,
        f"retrieval.weight_symbol must be >= 0, got {r.weight_symbol}",
    )
    _require(
        r.weight_name >= 0.0, f"retrieval.weight_name must be >= 0, got {r.weight_name}"
    )
    _require(
        r.weight_embed >= 0.0,
        f"retrieval.weight_embed must be >= 0, got {r.weight_embed}",
    )
    _require(
        r.boost_domain_prefix > 0.0,
        f"retrieval.boost_domain_prefix must be > 0, got {r.boost_domain_prefix}",
    )
    if r.use_embeddings:
        _require(
            r.embedding_dim >= 1,
            f"retrieval.embedding_dim must be >= 1, got {r.embedding_dim}",
        )
    _require(
        r.embedding_dim == 768,
        f"retrieval.embedding_dim must be 768, got {r.embedding_dim}",
    )
    _require(
        r.embedding_cache_size >= 0,
        f"retrieval.embedding_cache_size must be >= 0, got {r.embedding_cache_size}",
    )
    _require(
        r.embedding_backend == "sentence_transformers",
        f"retrieval.embedding_backend must be 'sentence_transformers', got '{r.embedding_backend}'",
    )
    _require(
        r.embedding_init_timeout_s > 0.0,
        f"retrieval.embedding_init_timeout_s must be > 0, got {r.embedding_init_timeout_s}",
    )
    _require(
        r.dense_top_k >= 1, f"retrieval.dense_top_k must be >= 1, got {r.dense_top_k}"
    )
    _require(
        r.hybrid_pool_multiplier >= 1,
        f"retrieval.hybrid_pool_multiplier must be >= 1, got {r.hybrid_pool_multiplier}",
    )
    _require(
        r.rerank_mode in ("none", "cross_encoder", "llm"),
        f"retrieval.rerank_mode must be none|cross_encoder|llm, got '{r.rerank_mode}'",
    )
    _require(
        r.rerank_top_n >= 0,
        f"retrieval.rerank_top_n must be >= 0, got {r.rerank_top_n}",
    )
    _require(
        r.rerank_llm_role in ("planner", "prover"),
        f"retrieval.rerank_llm_role must be planner|prover, got '{r.rerank_llm_role}'",
    )
    _require(
        r.goal_query_weight >= 0.0,
        f"retrieval.goal_query_weight must be >= 0, got {r.goal_query_weight}",
    )
    _require(
        r.prompt_budget_tokens >= 0,
        f"retrieval.prompt_budget_tokens must be >= 0, got {r.prompt_budget_tokens}",
    )
    _require(
        r.prompt_budget_hard_cap_tokens >= 0,
        f"retrieval.prompt_budget_hard_cap_tokens must be >= 0, got {r.prompt_budget_hard_cap_tokens}",
    )
    _require(
        0.0 <= r.prompt_budget_dedup_jaccard <= 1.0,
        f"retrieval.prompt_budget_dedup_jaccard must be in [0,1], got {r.prompt_budget_dedup_jaccard}",
    )
    _require(
        r.query_embedding_cache_size >= 0,
        f"retrieval.query_embedding_cache_size must be >= 0, got {r.query_embedding_cache_size}",
    )
    _require(
        r.dense_build_batch_size >= 1,
        f"retrieval.dense_build_batch_size must be >= 1, got {r.dense_build_batch_size}",
    )
    _require(
        (r.dense_search_mode or "full") in ("full", "bm25_filtered"),
        f"retrieval.dense_search_mode must be 'full' or 'bm25_filtered', got {r.dense_search_mode}",
    )
    _require(
        r.cross_encoder_cache_size >= 0,
        f"retrieval.cross_encoder_cache_size must be >= 0, got {r.cross_encoder_cache_size}",
    )
    _require(
        r.cross_encoder_score_timeout_s > 0.0,
        f"retrieval.cross_encoder_score_timeout_s must be > 0, got {r.cross_encoder_score_timeout_s}",
    )
    _require(
        r.cross_encoder_transient_cooldown_s > 0.0,
        f"retrieval.cross_encoder_transient_cooldown_s must be > 0, got {r.cross_encoder_transient_cooldown_s}",
    )
    _require(
        r.cross_encoder_max_transient_failures >= 1,
        f"retrieval.cross_encoder_max_transient_failures must be >= 1, got {r.cross_encoder_max_transient_failures}",
    )
    _require(
        r.ltr_learning_rate > 0.0,
        f"retrieval.ltr_learning_rate must be > 0, got {r.ltr_learning_rate}",
    )
    _require(
        r.ltr_warmup_updates >= 0,
        f"retrieval.ltr_warmup_updates must be >= 0, got {r.ltr_warmup_updates}",
    )
    _require(
        r.ltr_min_updates >= 0,
        f"retrieval.ltr_min_updates must be >= 0, got {r.ltr_min_updates}",
    )
    _require(
        r.ltr_negative_samples >= 0,
        f"retrieval.ltr_negative_samples must be >= 0, got {r.ltr_negative_samples}",
    )
    _require(
        r.ltr_positive_weight >= 0.0,
        f"retrieval.ltr_positive_weight must be >= 0, got {r.ltr_positive_weight}",
    )
    _require(
        0.0 < r.ltr_weight_decay <= 1.0,
        f"retrieval.ltr_weight_decay must be in (0,1], got {r.ltr_weight_decay}",
    )
    _require(r.log_top_k >= 1, f"retrieval.log_top_k must be >= 1, got {r.log_top_k}")

    # --- Proven lemma index ---
    pl = cfg.proven_lemma
    _require(
        pl.embedding_backend == "sentence_transformers",
        "proven_lemma.embedding_backend must be 'sentence_transformers', "
        f"got '{pl.embedding_backend}'",
    )
    _require(
        pl.embedding_init_timeout_s > 0.0,
        f"proven_lemma.embedding_init_timeout_s must be > 0, got {pl.embedding_init_timeout_s}",
    )
    _require(
        pl.embedding_dim == 768,
        f"proven_lemma.embedding_dim must be 768, got {pl.embedding_dim}",
    )

    # ---- Tactic Oracle ----
    to = cfg.tactic_oracle
    _require(
        to.timeout_s > 0,
        f"tactic_oracle.timeout_s must be > 0, got {to.timeout_s}",
    )
    _require(
        to.max_heartbeats > 0,
        f"tactic_oracle.max_heartbeats must be > 0, got {to.max_heartbeats}",
    )
    _require(
        to.max_concurrent >= 1,
        f"tactic_oracle.max_concurrent must be >= 1 (0 causes deadlock), got {to.max_concurrent}",
    )
    _require(
        to.goal_start_timeout_s > 0,
        f"tactic_oracle.goal_start_timeout_s must be > 0, got {to.goal_start_timeout_s}",
    )
    _require(
        to.goal_start_max_heartbeats > 0,
        f"tactic_oracle.goal_start_max_heartbeats must be > 0, got {to.goal_start_max_heartbeats}",
    )
    _require(
        to.goal_start_max_suggestions >= 1,
        f"tactic_oracle.goal_start_max_suggestions must be >= 1, got {to.goal_start_max_suggestions}",
    )
    _require(
        to.goal_start_max_depth >= 0,
        f"tactic_oracle.goal_start_max_depth must be >= 0, got {to.goal_start_max_depth}",
    )
    _require(
        to.repair_max_wall_s >= 0.0,
        f"tactic_oracle.repair_max_wall_s must be >= 0, got {to.repair_max_wall_s}",
    )
    _require(
        to.tier1_timeout_s > 0,
        f"tactic_oracle.tier1_timeout_s must be > 0, got {to.tier1_timeout_s}",
    )
    _require(
        to.tier2_timeout_s > 0,
        f"tactic_oracle.tier2_timeout_s must be > 0, got {to.tier2_timeout_s}",
    )
    _require(
        to.tier3_timeout_s > 0,
        f"tactic_oracle.tier3_timeout_s must be > 0, got {to.tier3_timeout_s}",
    )
    _require(
        to.decide_timeout_s > 0,
        f"tactic_oracle.decide_timeout_s must be > 0, got {to.decide_timeout_s}",
    )
    _require(
        to.prop_complete_timeout_s > 0,
        "tactic_oracle.prop_complete_timeout_s must be > 0, "
        f"got {to.prop_complete_timeout_s}",
    )
    _require(
        to.prop_complete_max_heartbeats > 0,
        "tactic_oracle.prop_complete_max_heartbeats must be > 0, "
        f"got {to.prop_complete_max_heartbeats}",
    )
    _require(
        to.grind_timeout_s > 0,
        f"tactic_oracle.grind_timeout_s must be > 0, got {to.grind_timeout_s}",
    )

    # --- H4a: lean.project_dir existence ---
    _lean_dir = Path(cfg.lean.project_dir)
    _require(
        _lean_dir.exists(),
        f"lean.project_dir does not exist: {cfg.lean.project_dir!r} "
        f"(resolved: {_lean_dir.resolve()})",
    )
    _require(
        all(
            _LEAN_IMPORT_RE.fullmatch(str(item or "").strip())
            for item in (getattr(cfg.lean, "extra_imports", []) or [])
            if str(item or "").strip()
        ),
        "lean.extra_imports must contain only Lean module names like Foo.Bar",
    )

    if errors:
        raise ConfigError("Configuration validation failed:\n  " + "\n  ".join(errors))


def load_config(path: str | Path) -> AppConfig:
    config_path = Path(path).resolve()
    config_dir = config_path.parent
    data = yaml.safe_load(config_path.read_text())
    if not isinstance(data, dict):
        raise ConfigError(f"Config file is not a YAML mapping: {config_path}")
    data = _resolve_inheritance(data, config_path)
    roles = _roles_from_data(_section_mapping(data, "roles", required=True))
    lean_data = _section_mapping(data, "lean")
    search_data = _section_mapping(data, "search")
    removed_top_level_sections = {
        "scheduler": "The round-robin sweep scheduler has been removed. Use the sequential benchmark/sweep path instead.",
        "formalization": "The formalization repair pipeline has been removed from the live runtime.",
    }
    for removed_key, message in removed_top_level_sections.items():
        if data.get(removed_key) not in (None, {}):
            raise ConfigError(f"{removed_key}: removed. {message}")
    removed_search_keys = {
        "proof_skeleton_enabled": "Legacy proof-skeleton execution has been removed.",
        "composition_sorry_fill_enabled": "Legacy composition sorry-fill has been removed.",
        "composition_sorry_fill_max_holes": "Legacy composition sorry-fill has been removed.",
        "composition_sorry_fill_time_s": "Legacy composition sorry-fill has been removed.",
        "post_skeleton_composition_max_rounds": "Post-skeleton composition burst control has been removed with the proof-skeleton lane.",
        "post_skeleton_composition_time_fraction": "Post-skeleton composition burst control has been removed with the proof-skeleton lane.",
        "post_skeleton_root_focus_on_burst_exhaustion": "Post-skeleton composition burst control has been removed with the proof-skeleton lane.",
        "hole_driven": "Legacy sorry-driven hole decomposition has been removed.",
        "max_sorry_holes": "Legacy sorry-driven hole decomposition has been removed.",
        "hole_skeleton_few_shot": "Legacy sorry-driven hole decomposition has been removed.",
        "hole_max_depth": "Legacy sorry-driven hole decomposition has been removed.",
        "hole_budget_fraction": "Legacy sorry-driven hole decomposition has been removed.",
        "min_hole_time_s": "Legacy sorry-driven hole decomposition has been removed.",
        "hole_skeleton_n": "Legacy sorry-driven hole decomposition has been removed.",
        "placeholder_lean_check_budget": "Legacy placeholder rescue has been removed.",
        "composition_stall_pivot_threshold": "Legacy composition sorry-hole pivoting has been removed.",
        "composition_stall_circular_similarity": "Legacy composition sorry-hole pivoting has been removed.",
        "tool_authority_auto_check_max_refs": "Legacy tool authority auto-check rescue has been removed.",
    }
    for removed_key, message in removed_search_keys.items():
        if removed_key in search_data:
            raise ConfigError(f"search.{removed_key}: removed. {message}")
    tactic_oracle_data = _section_mapping(data, "tactic_oracle")
    if "on_sorry_hole" in tactic_oracle_data:
        raise ConfigError(
            "tactic_oracle.on_sorry_hole: removed. Legacy sorry-hole oracle triggering has been removed. "
            "Use tactic_oracle.on_compiled_slot instead."
        )
    budget_data = _section_mapping(data, "budgets")
    ensemble_data = _section_mapping(data, "ensemble")
    retrieval_data = _section_mapping(data, "retrieval")
    strategy_data = _section_mapping(data, "strategy")
    tactic_tree_data = _section_mapping(data, "tactic_tree")
    proven_lemma_data = _section_mapping(data, "proven_lemma")
    removed_tactic_tree_keys = {
        "adaptive_retrieval": "Adaptive mid-tree goal-state retrieval has been removed.",
        "adaptive_retrieval_max_extra": "Adaptive mid-tree goal-state retrieval has been removed.",
        "adaptive_retrieval_budget": "Adaptive mid-tree goal-state retrieval has been removed.",
        "adaptive_retrieval_depth_min": "Adaptive mid-tree goal-state retrieval has been removed.",
    }
    for removed_key, message in removed_tactic_tree_keys.items():
        if removed_key in tactic_tree_data:
            raise ConfigError(f"tactic_tree.{removed_key}: removed. {message}")
    lean_extra_imports_raw = lean_data.get("extra_imports", []) or []
    if isinstance(lean_extra_imports_raw, str):
        lean_extra_imports_raw = [lean_extra_imports_raw]
    elif not isinstance(lean_extra_imports_raw, (list, tuple)):
        lean_extra_imports_raw = [lean_extra_imports_raw]
    lean = LeanConfig(
        project_dir=_resolve_existing_root_path(
            lean_data.get("project_dir", "./lean_project"),
            config_dir=config_dir,
        ),
        preamble_import=lean_data.get("preamble_import", "import Mathlib"),
        preamble_tactics=str(lean_data.get("preamble_tactics", "") or ""),
        max_parallel=_as_int(lean_data.get("max_parallel", 8), 8),
        timeout_s=_as_int(lean_data.get("timeout_s", 45), 45),
        fast_fail_timeout_s=_as_int(lean_data.get("fast_fail_timeout_s", 20), 20),
        fast_fail_enabled=_as_bool(
            lean_data.get("fast_fail_enabled", True), default=True
        ),
        precheck_mode=str(lean_data.get("precheck_mode", "typecheck") or "typecheck"),
        precheck_timeout_s=_as_float(
            lean_data.get("precheck_timeout_s", 8.0),
            8.0,
        ),
        precheck_max_heartbeats=_as_int(
            lean_data.get("precheck_max_heartbeats", 120000),
            120000,
        ),
        max_full_checks=_as_int(lean_data.get("max_full_checks", 0), 0),
        min_score_full_check=_as_float(
            lean_data.get("min_score_full_check", -1.0),
            -1.0,
        ),
        use_repl=_as_bool(lean_data.get("use_repl", True), default=True),
        backend_mode=str(
            lean_data.get(
                "backend_mode",
                "env_cached_subprocess"
                if _as_bool(lean_data.get("use_repl", True), default=True)
                else "lake",
            )
            or "env_cached_subprocess"
        ),
        persistent_workers=_as_int(lean_data.get("persistent_workers", 0), 0),
        persistent_worker_idle_ttl_s=_as_float(
            lean_data.get("persistent_worker_idle_ttl_s", 300.0),
            300.0,
        ),
        persistent_worker_start_timeout_s=_as_float(
            lean_data.get("persistent_worker_start_timeout_s", 30.0),
            30.0,
        ),
        persistent_request_timeout_buffer_s=_as_float(
            lean_data.get("persistent_request_timeout_buffer_s", 2.0),
            2.0,
        ),
        persistent_max_requests_per_worker=_as_int(
            lean_data.get("persistent_max_requests_per_worker", 200),
            200,
        ),
        persistent_oracle_workers=_as_int(
            lean_data.get("persistent_oracle_workers", 0),
            0,
        ),
        persistent_protocol=str(
            lean_data.get("persistent_protocol", "lsp") or "lsp"
        ),
        solved_dir=str(lean_data.get("solved_dir", "./runs/solved/")),
        extra_imports=[
            str(item).strip() for item in lean_extra_imports_raw if str(item).strip()
        ],
    )
    search = SearchConfig(
        max_depth=_as_int(search_data.get("max_depth", 3), 3),
        max_goals=_as_int(search_data.get("max_goals", 64), 64),
        max_attempts_per_goal=_as_int(search_data.get("max_attempts_per_goal", 6), 6),
        candidates_per_goal=_as_int(search_data.get("candidates_per_goal", 4), 4),
        planner_subgoals_max=_as_int(search_data.get("planner_subgoals_max", 4), 4),
        planner_llm_calls_budget=_as_int(
            search_data.get("planner_llm_calls_budget", 60), 60
        ),
        planner_llm_calls_reserve_for_plan_subgoals=_as_int(
            search_data.get("planner_llm_calls_reserve_for_plan_subgoals", 0), 0
        ),
        validate_planner_subgoals=_as_bool(
            search_data.get("validate_planner_subgoals", True), default=True
        ),
        retrieval_first_proof_enabled=_as_bool(
            search_data.get("retrieval_first_proof_enabled", True), default=True
        ),
        retrieval_first_proof_max_rounds=_as_int(
            search_data.get("retrieval_first_proof_max_rounds", 2), 2
        ),
        retrieval_first_proof_timeout_s=_as_float(
            search_data.get("retrieval_first_proof_timeout_s", 90.0), 90.0
        ),
        proof_generation_max_tokens=max(
            0, _as_int(search_data.get("proof_generation_max_tokens", 8192), 8192)
        ),
        proof_generation_timeout_s=max(
            0.0,
            _as_float(search_data.get("proof_generation_timeout_s", 300.0), 300.0),
        ),
        retrieval_first_proof_max_tokens=max(
            0,
            _as_int(
                search_data.get("retrieval_first_proof_max_tokens", 6144),
                6144,
            ),
        ),
        retrieval_first_proof_call_timeout_s=max(
            0.0,
            _as_float(
                search_data.get("retrieval_first_proof_call_timeout_s", 300.0),
                300.0,
            ),
        ),
        tool_finalize_max_tokens=max(
            0, _as_int(search_data.get("tool_finalize_max_tokens", 8192), 8192)
        ),
        tool_finalize_timeout_s=max(
            0.0, _as_float(search_data.get("tool_finalize_timeout_s", 360.0), 360.0)
        ),
        recursive_direct_proof_max_tokens=max(
            0,
            _as_int(
                search_data.get("recursive_direct_proof_max_tokens", 6144),
                6144,
            ),
        ),
        recursive_direct_proof_timeout_s=max(
            0.0,
            _as_float(
                search_data.get("recursive_direct_proof_timeout_s", 300.0),
                300.0,
            ),
        ),
        prover_semantic_fallback_enabled=_as_bool(
            search_data.get("prover_semantic_fallback_enabled", True),
            default=True,
        ),
        prover_semantic_fallback_root_only=_as_bool(
            search_data.get("prover_semantic_fallback_root_only", True),
            default=True,
        ),
        prover_semantic_fallback_max_backends=_as_int(
            search_data.get("prover_semantic_fallback_max_backends", 2), 2
        ),
        planner_allow_informal_fallback=_as_bool(
            search_data.get("planner_allow_informal_fallback", False), default=False
        ),
        planner_allow_unvalidated_fallback=_as_bool(
            search_data.get("planner_allow_unvalidated_fallback", False), default=False
        ),
        planner_repair_on_all_failed=_as_bool(
            search_data.get("planner_repair_on_all_failed", True), default=True
        ),
        planner_contextualize_subgoals=_as_bool(
            search_data.get("planner_contextualize_subgoals", True), default=True
        ),
        planner_contextualize_max_chars=_as_int(
            search_data.get("planner_contextualize_max_chars", 256), 256
        ),
        subgoal_compiler_enabled=_as_bool(
            search_data.get("subgoal_compiler_enabled", True), default=True
        ),
        subgoal_compiler_max_variants=_as_int(
            search_data.get("subgoal_compiler_max_variants", 4), 4
        ),
        subgoal_compiler_max_prefix_chars=_as_int(
            search_data.get("subgoal_compiler_max_prefix_chars", 600), 600
        ),
        planner_use_proof_subgoals=_as_bool(
            search_data.get("planner_use_proof_subgoals", True), default=True
        ),
        planner_proof_subgoals_max=_as_int(
            search_data.get("planner_proof_subgoals_max", 6), 6
        ),
        planner_filter_vacuous_eventual_subgoals=_as_bool(
            search_data.get("planner_filter_vacuous_eventual_subgoals", True),
            default=True,
        ),
        planner_filter_near_restatement_subgoals=_as_bool(
            search_data.get("planner_filter_near_restatement_subgoals", True),
            default=True,
        ),
        planner_subgoal_near_restatement_similarity=_as_float(
            search_data.get("planner_subgoal_near_restatement_similarity", 0.85),
            0.85,
        ),
        planner_subgoal_min_difficulty_drop=_as_float(
            search_data.get("planner_subgoal_min_difficulty_drop", 4.0),
            4.0,
        ),
        planner_subgoal_max_harder_delta=_as_float(
            search_data.get("planner_subgoal_max_harder_delta", 8.0),
            8.0,
        ),
        planner_replan_failed_subgoal_quarantine_rounds=int(
            search_data.get("planner_replan_failed_subgoal_quarantine_rounds", 2)
        ),
        planner_subgoal_falsify_enabled=_as_bool(
            search_data.get("planner_subgoal_falsify_enabled", True), default=True
        ),
        planner_subgoal_falsify_max_subgoals=int(
            search_data.get("planner_subgoal_falsify_max_subgoals", 8)
        ),
        planner_subgoal_falsify_timeout_s=float(
            search_data.get("planner_subgoal_falsify_timeout_s", 2.0)
        ),
        planner_subgoal_nat_sample_falsify_enabled=_as_bool(
            search_data.get(
                "planner_subgoal_nat_sample_falsify_enabled", True
            ),
            default=True,
        ),
        planner_subgoal_nat_sample_falsify_timeout_s=float(
            search_data.get(
                "planner_subgoal_nat_sample_falsify_timeout_s", 4.0
            )
        ),
        planner_subgoal_nat_sample_falsify_max_checks=int(
            search_data.get(
                "planner_subgoal_nat_sample_falsify_max_checks", 4
            )
        ),
        planner_use_json=_as_bool(
            search_data.get("planner_use_json", True), default=True
        ),
        refine_rounds=_as_int(search_data.get("refine_rounds", 2), 2),
        refine_max_failures_per_round=_as_int(
            search_data.get("refine_max_failures_per_round", 3), 3
        ),
        best_of_n=int(search_data.get("best_of_n", 1)),
        multi_turn_refine=_as_bool(
            search_data.get("multi_turn_refine", False), default=False
        ),
        parallel_candidates=_as_bool(
            search_data.get("parallel_candidates", False), default=False
        ),
        parallel_candidate_window=int(search_data.get("parallel_candidate_window", 0)),
        parallel_goals=int(search_data.get("parallel_goals", 1)),
        parallel_beam_nodes=_as_bool(
            search_data.get("parallel_beam_nodes", True), default=True
        ),
        tactic_level=_as_bool(search_data.get("tactic_level", False), default=False),
        tactic_beam_width=int(search_data.get("tactic_beam_width", 3)),
        tactic_max_steps=int(search_data.get("tactic_max_steps", 20)),
        max_replans=int(search_data.get("max_replans", 0)),
        min_replan_time_s=float(search_data.get("min_replan_time_s", 120.0)),
        budget_only_unsolved_termination=_as_bool(
            search_data.get("budget_only_unsolved_termination", True),
            default=True,
        ),
        refiner_can_replan=_as_bool(
            search_data.get("refiner_can_replan", True), default=True
        ),
        composition_prover_role=str(
            search_data.get("composition_prover_role", "prover")
        ),
        composition_refine_failures=_as_bool(
            search_data.get("composition_refine_failures", True), default=True
        ),
        composition_refine_max_failures_per_round=int(
            search_data.get("composition_refine_max_failures_per_round", 1)
        ),
        composition_refine_turns=int(
            search_data.get("composition_refine_turns", 2)
        ),
        structured_feedback=_as_bool(
            search_data.get("structured_feedback", True), default=True
        ),
        include_goal_state_in_prompt=_as_bool(
            search_data.get("include_goal_state_in_prompt", True), default=True
        ),
        strategy_prompting=_as_bool(
            search_data.get("strategy_prompting", True), default=True
        ),
        strategy_prompting_max_calls=int(
            search_data.get("strategy_prompting_max_calls", 2)
        ),
        adaptive_llm_temperature=_as_bool(
            search_data.get("adaptive_llm_temperature", True), default=True
        ),
        prover_temp_ceiling=_as_float(
            search_data.get("prover_temp_ceiling", 0.90), 0.90
        ),
        refiner_temp_ceiling=_as_float(
            search_data.get("refiner_temp_ceiling", 0.50), 0.50
        ),
        planner_temp_ceiling=_as_float(
            search_data.get("planner_temp_ceiling", 0.30), 0.30
        ),
        domain_aware=_as_bool(search_data.get("domain_aware", True), default=True),
        proof_sketch=_as_bool(search_data.get("proof_sketch", False), default=False),
        proof_sketch_root_only=_as_bool(
            search_data.get("proof_sketch_root_only", False), default=False
        ),
        sketch_have_extraction=_as_bool(
            search_data.get("sketch_have_extraction", True), default=True
        ),
        sketch_max_haves=int(search_data.get("sketch_max_haves", 5)),
        sketch_budget_tokens=int(search_data.get("sketch_budget_tokens", 256)),
        curriculum_order=_as_bool(
            search_data.get("curriculum_order", True), default=True
        ),
        curriculum_shuffle=_as_bool(
            search_data.get("curriculum_shuffle", True), default=True
        ),
        curriculum_band_width=float(search_data.get("curriculum_band_width", 15.0)),
        boilerplate_early_exit_threshold=float(
            search_data.get("boilerplate_early_exit_threshold", 0.6)
        ),
        full_goal_state_budget_tokens=int(
            search_data.get("full_goal_state_budget_tokens", 160)
        ),
        full_goal_state_max_goals=int(search_data.get("full_goal_state_max_goals", 8)),
        max_context_solved_lemmas=int(search_data.get("max_context_solved_lemmas", 8)),
        proof_potential_enabled=_as_bool(
            search_data.get("proof_potential_enabled", True), default=True
        ),
        proof_potential_observe_only=_as_bool(
            search_data.get("proof_potential_observe_only", True), default=True
        ),
        proof_potential_non_decrease_window=int(
            search_data.get("proof_potential_non_decrease_window", 3)
        ),
        proof_potential_escape_budget=int(
            search_data.get("proof_potential_escape_budget", 2)
        ),
        lemma_fast_path=_as_bool(
            search_data.get("lemma_fast_path", True), default=True
        ),
        fast_path_max_projections=int(search_data.get("fast_path_max_projections", 8)),
        fast_path_probe_timeout_s=_as_float(
            search_data.get("fast_path_probe_timeout_s", 12.0), 12.0
        ),
        probes_enabled=_as_bool(
            search_data.get("probes_enabled", False), default=False
        ),
        probes_output_dir=str(search_data.get("probes_output_dir", "") or ""),
        use_root_workset=_as_bool(
            search_data.get("use_root_workset", False), default=False
        ),
        composition_first=_as_bool(
            search_data.get("composition_first", True), default=True
        ),
        fast_path_zero_hit_min_runs=int(
            search_data.get("fast_path_zero_hit_min_runs", 4)
        ),
        fast_path_zero_hit_min_attempts=int(
            search_data.get("fast_path_zero_hit_min_attempts", 32)
        ),
        oracle_repair_zero_hit_min_attempts=int(
            search_data.get("oracle_repair_zero_hit_min_attempts", 24)
        ),
        full_check_batch_cap=int(search_data.get("full_check_batch_cap", 12)),
        failure_aggregation=_as_bool(
            search_data.get("failure_aggregation", True), default=True
        ),
        failure_aggregation_max_rounds=int(
            search_data.get("failure_aggregation_max_rounds", 3)
        ),
        failure_aggregation_max_patterns_per_round=int(
            search_data.get("failure_aggregation_max_patterns_per_round", 3)
        ),
        max_refiner_calls_per_problem=_as_int(
            search_data.get("max_refiner_calls_per_problem", 40), 40
        ),
        refiner_replan_reserved_calls=_as_int(
            search_data.get("refiner_replan_reserved_calls", 2), 2
        ),
        composition_failure_threshold=max(
            1, _as_int(search_data.get("composition_failure_threshold", 6), 6)
        ),
        composition_candidates_per_round=max(
            1,
            _as_int(search_data.get("composition_candidates_per_round", 6), 6),
        ),
        temperature_mode=str(search_data.get("temperature_mode", "adaptive")),
        temperature_bandit_arms=[
            float(x)
            for x in (
                search_data.get("temperature_bandit_arms") or [0.50, 0.58, 0.66, 0.72]
            )
        ],
        temperature_bandit_carry=_as_float(
            search_data.get("temperature_bandit_carry", 0.10), 0.10
        ),
        temperature_round_robin_temps=[
            float(x)
            for x in (
                search_data.get("temperature_round_robin_temps") or [0.45, 0.58, 0.70]
            )
        ],
        temperature_fixed_value=_as_float(
            search_data.get("temperature_fixed_value", 0.60), 0.60
        ),
        prover_temp_ema_alpha=_as_float(
            search_data.get("prover_temp_ema_alpha", 0.65), 0.65
        ),
        session_synth_hash_sharing=_as_bool(
            search_data.get("session_synth_hash_sharing", True), default=True
        ),
        synth_lemma_ref_penalty=_as_bool(
            search_data.get("synth_lemma_ref_penalty", True), default=True
        ),
        filter_synth_dot_symm=_as_bool(
            search_data.get("filter_synth_dot_symm", True), default=True
        ),
        guard_per_subgoal_retrieval=_as_bool(
            search_data.get("guard_per_subgoal_retrieval", False), default=False
        ),
        stale_check_time_floor_fraction=_as_float(
            search_data.get("stale_check_time_floor_fraction", 0.25), 0.25
        ),
        tool_augmented_proving=_as_bool(
            search_data.get("tool_augmented_proving", False), default=False
        ),
        tool_max_rounds=_as_int(search_data.get("tool_max_rounds", 3), 3),
        tool_check_type_timeout_s=_as_float(
            search_data.get("tool_check_type_timeout_s", 10.0), 10.0
        ),
        tool_search_max_results=_as_int(
            search_data.get("tool_search_max_results", 10), 10
        ),
        executable_scaffold_executor=_as_bool(
            search_data.get("executable_scaffold_executor", True), default=True
        ),
        scaffold_slot_scheduler=_as_bool(
            search_data.get("scaffold_slot_scheduler", True), default=True
        ),
        plan_locked_max_refinements=_as_int(
            search_data.get("plan_locked_max_refinements", 3), 3
        ),
        executable_scaffold_root_suppression=_as_bool(
            search_data.get("executable_scaffold_root_suppression", False),
            default=False,
        ),
        scaffold_max_rounds=_as_int(search_data.get("scaffold_max_rounds", 20), 20),
        scaffold_no_progress_rounds=_as_int(
            search_data.get("scaffold_no_progress_rounds", 5), 5
        ),
        scaffold_repeated_error_cutoff=_as_int(
            search_data.get("scaffold_repeated_error_cutoff", 3), 3
        ),
        scaffold_min_budget_headroom_usd=_as_float(
            search_data.get("scaffold_min_budget_headroom_usd", 0.10), 0.10
        ),
        theorem_scaffold_timeout_s=_as_float(
            search_data.get("theorem_scaffold_timeout_s", 60.0), 60.0
        ),
        executable_scaffold_template_timeout_s=_as_float(
            search_data.get("executable_scaffold_template_timeout_s", 45.0), 45.0
        ),
        proof_sketch_json_timeout_s=_as_float(
            search_data.get("proof_sketch_json_timeout_s", 60.0), 60.0
        ),
        proof_sketch_tag_timeout_s=_as_float(
            search_data.get("proof_sketch_tag_timeout_s", 30.0), 30.0
        ),
    )
    # Warn if contradictory temperature flags are explicitly set in YAML.
    # Only warn when adaptive_llm_temperature is explicitly set to False
    # (actively trying to disable) alongside a non-adaptive mode.  Inherited
    # True from base config is not a conflict — bandit/fixed simply supersede.
    _explicit_mode = "temperature_mode" in search_data
    _explicit_adaptive_off = (
        "adaptive_llm_temperature" in search_data
        and not search.adaptive_llm_temperature
    )
    if (
        _explicit_mode
        and search.temperature_mode != "adaptive"
        and _explicit_adaptive_off
    ):
        logger.warning(
            "Both temperature_mode=%r and adaptive_llm_temperature=%r are explicitly "
            "set in YAML. temperature_mode takes precedence; adaptive_llm_temperature "
            "is only used when temperature_mode='adaptive'.",
            search.temperature_mode,
            search.adaptive_llm_temperature,
        )
    strategy = StrategyConfig(
        mode=str(strategy_data.get("mode", "linear")),
        beam_width=_as_int(strategy_data.get("beam_width", 4), 4),
        mcts_simulations=_as_int(strategy_data.get("mcts_simulations", 32), 32),
        mcts_c_puct=_as_float(strategy_data.get("mcts_c_puct", 1.4), 1.4),
        backtrack=_as_bool(strategy_data.get("backtrack", True), default=True),
        beam_stale_decay_rate=_as_float(
            strategy_data.get("beam_stale_decay_rate", 0.0), 0.0
        ),
        beam_stagnation_threshold=_as_int(
            strategy_data.get("beam_stagnation_threshold", 20), 20
        ),
        goal_terminal_stagnation_threshold=_as_int(
            strategy_data.get("goal_terminal_stagnation_threshold", 12), 12
        ),
    )
    budgets = BudgetConfig(
        time_seconds=_as_int(budget_data.get("time_seconds", 3600), 3600),
        max_total_attempts=_as_int(budget_data.get("max_total_attempts", 200), 200),
        stale_fraction=_as_float(budget_data.get("stale_fraction", 0.35), 0.35),
        early_exit_min_iterations=_as_int(
            budget_data.get("early_exit_min_iterations", 5), 5
        ),
        early_exit_min_nodes=_as_int(budget_data.get("early_exit_min_nodes", 70), 70),
        max_cost_per_problem_usd=_as_float(
            budget_data.get(
                "max_cost_per_problem_usd", budget_data.get("max_cost_usd", 0.0)
            ),
            0.0,
        ),
        max_sweep_cost_usd=float(budget_data.get("max_sweep_cost_usd", 0.0)),
        max_beam_restarts=int(budget_data.get("max_beam_restarts", 0)),
        beam_restart_temp_boost=float(budget_data.get("beam_restart_temp_boost", 0.08)),
        beam_restart_temp_cap=float(budget_data.get("beam_restart_temp_cap", 1.25)),
    )
    pricing_data = _section_mapping(data, "token_pricing")
    token_pricing = TokenPricing(
        input_per_m=float(pricing_data.get("input_per_m", 0.0)),
        cached_per_m=float(pricing_data.get("cached_per_m", 0.0)),
        output_per_m=float(pricing_data.get("output_per_m", 0.0)),
    )
    raw_online_models_path = ensemble_data.get("online_models_path")
    online_models_path = None
    if raw_online_models_path is not None:
        stripped = str(raw_online_models_path).strip()
        if stripped:
            online_models_path = stripped

    ensemble = EnsembleConfig(
        enabled=_as_bool(ensemble_data.get("enabled", True), default=True),
        seed=int(ensemble_data.get("seed", 1337)),
        embedding_dim=int(ensemble_data.get("embedding_dim", 768)),
        alpha=float(ensemble_data.get("alpha", 0.2)),
        eta=float(ensemble_data.get("eta", 0.1)),
        epsilon0=float(ensemble_data.get("epsilon0", 1.0)),
        epsilon_min=float(ensemble_data.get("epsilon_min", 0.1)),
        epsilon_max=float(ensemble_data.get("epsilon_max", 5.0)),
        epsilon_homeostasis_event=str(
            ensemble_data.get("epsilon_homeostasis_event", "hit_rate")
        ),
        epsilon_homeostasis_blend_weight=float(
            ensemble_data.get("epsilon_homeostasis_blend_weight", 0.6)
        ),
        r_star0=float(ensemble_data.get("r_star0", 0.3)),
        r_star_min=float(ensemble_data.get("r_star_min", 0.05)),
        r_star_max=float(ensemble_data.get("r_star_max", 0.7)),
        depth_r_star_decay=float(ensemble_data.get("depth_r_star_decay", 0.15)),
        depth_r_star_floor=float(ensemble_data.get("depth_r_star_floor", 0.5)),
        tau0=float(ensemble_data.get("tau0", 1.0)),
        tau_min=float(ensemble_data.get("tau_min", 0.2)),
        tau_max=float(ensemble_data.get("tau_max", 1.5)),
        eps_explore0=float(ensemble_data.get("eps_explore0", 0.1)),
        eps_explore_min=float(ensemble_data.get("eps_explore_min", 0.02)),
        eps_explore_max=float(ensemble_data.get("eps_explore_max", 0.6)),
        stall_failure_streak_threshold=int(
            ensemble_data.get("stall_failure_streak_threshold", 40)
        ),
        stall_success_rate_threshold=float(
            ensemble_data.get("stall_success_rate_threshold", 0.05)
        ),
        stall_decay_floor=float(ensemble_data.get("stall_decay_floor", 0.25)),
        stall_disable_budget_clamp=_as_bool(
            ensemble_data.get("stall_disable_budget_clamp", True), default=True
        ),
        stall_progress_attenuation_threshold=float(
            ensemble_data.get("stall_progress_attenuation_threshold", 0.15)
        ),
        beta=float(ensemble_data.get("beta", 0.3)),
        memory_size=int(ensemble_data.get("memory_size", 2000)),
        memory_success_reserve_ratio=float(
            ensemble_data.get("memory_success_reserve_ratio", 0.2)
        ),
        replay_stratified_utility=_as_bool(
            ensemble_data.get("replay_stratified_utility", False), default=False
        ),
        recent_window=int(ensemble_data.get("recent_window", 50)),
        weight_center=float(ensemble_data.get("weight_center", 1.0)),
        weight_utility=float(ensemble_data.get("weight_utility", 0.8)),
        weight_novelty=float(ensemble_data.get("weight_novelty", 0.6)),
        weight_goal=float(ensemble_data.get("weight_goal", 0.8)),
        weight_active_goal=float(ensemble_data.get("weight_active_goal", 0.3)),
        weight_cost=float(ensemble_data.get("weight_cost", 0.3)),
        weight_quality=float(ensemble_data.get("weight_quality", 0.7)),
        cost_scale=float(ensemble_data.get("cost_scale", 200.0)),
        cost_penalty=float(ensemble_data.get("cost_penalty", 0.1)),
        penalty_trivial=float(ensemble_data.get("penalty_trivial", 0.6)),
        penalty_bad=float(ensemble_data.get("penalty_bad", 2.0)),
        penalty_degenerate=float(ensemble_data.get("penalty_degenerate", 3.0)),
        progress_reward_weight=float(ensemble_data.get("progress_reward_weight", 0.5)),
        error_penalty_type_mismatch=float(
            ensemble_data.get("error_penalty_type_mismatch", 0.08)
        ),
        error_penalty_unknown_identifier=float(
            ensemble_data.get("error_penalty_unknown_identifier", 0.25)
        ),
        error_penalty_tactic_failed=float(
            ensemble_data.get("error_penalty_tactic_failed", 0.15)
        ),
        error_penalty_missing_instance=float(
            ensemble_data.get("error_penalty_missing_instance", 0.2)
        ),
        error_penalty_simp_no_progress=float(
            ensemble_data.get("error_penalty_simp_no_progress", 0.1)
        ),
        error_penalty_timeout=float(ensemble_data.get("error_penalty_timeout", 0.3)),
        error_penalty_unification_failed=float(
            ensemble_data.get("error_penalty_unification_failed", 0.08)
        ),
        quality_line_target=float(ensemble_data.get("quality_line_target", 4.0)),
        quality_tactic_target=float(ensemble_data.get("quality_tactic_target", 3.0)),
        persistent_memory_path=ensemble_data.get("persistent_memory_path"),
        online_models_path=online_models_path,
        diversity_min_strategies=int(ensemble_data.get("diversity_min_strategies", 2)),
        retrieval_k=int(ensemble_data.get("retrieval_k", 3)),
        memory_embedding_backend=str(
            ensemble_data.get("memory_embedding_backend", "sentence_transformers")
        ),
        memory_embedding_model=str(
            ensemble_data.get("memory_embedding_model", "BAAI/bge-base-en-v1.5")
        ),
        memory_embedding_device=ensemble_data.get("memory_embedding_device", None),
        memory_embedding_normalize=_as_bool(
            ensemble_data.get("memory_embedding_normalize", True), default=True
        ),
        memory_embedding_prefer_local_files=_as_bool(
            ensemble_data.get("memory_embedding_prefer_local_files", True),
            default=True,
        ),
        memory_embedding_local_files_only=_as_bool(
            ensemble_data.get("memory_embedding_local_files_only", True),
            default=True,
        ),
        memory_embedding_allow_download=_as_bool(
            ensemble_data.get("memory_embedding_allow_download", False),
            default=False,
        ),
        memory_embedding_init_timeout_s=float(
            ensemble_data.get("memory_embedding_init_timeout_s", 8.0)
        ),
        memory_weight_bm25=float(ensemble_data.get("memory_weight_bm25", 0.5)),
        memory_weight_embed=float(ensemble_data.get("memory_weight_embed", 0.5)),
        memory_failed_strategy_hints_enabled=_as_bool(
            ensemble_data.get("memory_failed_strategy_hints_enabled", False),
            default=False,
        ),
        memory_failed_strategy_gate_threshold=float(
            ensemble_data.get("memory_failed_strategy_gate_threshold", 0.25)
        ),
        memory_failed_strategy_min_recent_success=float(
            ensemble_data.get("memory_failed_strategy_min_recent_success", 0.05)
        ),
        memory_failed_strategy_min_local_support=int(
            ensemble_data.get("memory_failed_strategy_min_local_support", 8)
        ),
        memory_failed_strategy_recent_prior_strength=int(
            ensemble_data.get("memory_failed_strategy_recent_prior_strength", 24)
        ),
        memory_failed_strategy_disable_during_stall=_as_bool(
            ensemble_data.get("memory_failed_strategy_disable_during_stall", True),
            default=True,
        ),
        failed_strategy_prior_enabled=_as_bool(
            ensemble_data.get("failed_strategy_prior_enabled", True),
            default=True,
        ),
        failed_strategy_prior_penalty=float(
            ensemble_data.get("failed_strategy_prior_penalty", 0.35)
        ),
        failed_strategy_prompt_hints_enabled=_as_bool(
            ensemble_data.get("failed_strategy_prompt_hints_enabled", True),
            default=True,
        ),
        early_exit_ensemble_signals_enabled=_as_bool(
            ensemble_data.get("early_exit_ensemble_signals_enabled", False),
            default=False,
        ),
        adaptive_embedding=_as_bool(
            ensemble_data.get("adaptive_embedding", False), default=False
        ),
        embedding_lr=float(ensemble_data.get("embedding_lr", 0.01)),
        world_model_lr=float(ensemble_data.get("world_model_lr", 0.05)),
        utility_lr=float(ensemble_data.get("utility_lr", 0.03)),
        weight_decay=float(ensemble_data.get("weight_decay", 1e-4)),
        model_hidden_dim=int(ensemble_data.get("model_hidden_dim", 32)),
        replay_buffer_size=int(ensemble_data.get("replay_buffer_size", 200)),
        replay_batch=int(ensemble_data.get("replay_batch", 4)),
        replay_lr_scale=float(ensemble_data.get("replay_lr_scale", 0.5)),
        hidden_lr_scale=float(ensemble_data.get("hidden_lr_scale", 0.2)),
        negation_closure=_as_bool(
            ensemble_data.get("negation_closure", True), default=True
        ),
        max_closure_expansion=int(ensemble_data.get("max_closure_expansion", 3)),
        grow_rate=float(ensemble_data.get("grow_rate", 0.1)),
        prune_rate=float(ensemble_data.get("prune_rate", 0.05)),
        strategy_prior_weight=float(ensemble_data.get("strategy_prior_weight", 0.3)),
        guidance_enabled=_as_bool(
            ensemble_data.get("guidance_enabled", True), default=True
        ),
        guidance_dir=str(ensemble_data.get("guidance_dir", "./runs/guidance")),
        guidance_policy_path=ensemble_data.get("guidance_policy_path"),
        guidance_value_path=ensemble_data.get("guidance_value_path"),
        guidance_min_policy_conf=float(
            ensemble_data.get("guidance_min_policy_conf", 0.45)
        ),
        guidance_min_value_conf=float(
            ensemble_data.get("guidance_min_value_conf", 0.55)
        ),
        guidance_fallback_to_llm=_as_bool(
            ensemble_data.get("guidance_fallback_to_llm", True), default=True
        ),
        guidance_autotrain=_as_bool(
            ensemble_data.get("guidance_autotrain", False), default=False
        ),
        guidance_autotrain_min_examples=int(
            ensemble_data.get("guidance_autotrain_min_examples", 200)
        ),
        guidance_autotrain_min_new_examples=int(
            ensemble_data.get("guidance_autotrain_min_new_examples", 50)
        ),
        guidance_autotrain_max_examples=int(
            ensemble_data.get("guidance_autotrain_max_examples", 0)
        ),
        tactic_lexicon_enabled=_as_bool(
            ensemble_data.get("tactic_lexicon_enabled", True), default=True
        ),
        tactic_lexicon_path=str(
            ensemble_data.get("tactic_lexicon_path", "./runs/tactic_observations.jsonl")
        ),
        tactic_lexicon_promote_support=int(
            ensemble_data.get("tactic_lexicon_promote_support", 8)
        ),
        tactic_lexicon_unknown_prior=float(
            ensemble_data.get("tactic_lexicon_unknown_prior", 0.35)
        ),
        tactic_lexicon_demote_after_failures=int(
            ensemble_data.get("tactic_lexicon_demote_after_failures", 3)
        ),
        tactic_lexicon_demote_decay=float(
            ensemble_data.get("tactic_lexicon_demote_decay", 0.20)
        ),
        master_enabled=_as_bool(
            ensemble_data.get("master_enabled", True), default=True
        ),
        master_log_decisions=_as_bool(
            ensemble_data.get("master_log_decisions", True), default=True
        ),
        one_shot_hardening=_as_bool(
            ensemble_data.get("one_shot_hardening", False), default=False
        ),
        meo_use_ast_difficulty=_as_bool(
            ensemble_data.get("meo_use_ast_difficulty", False), default=False
        ),
        meo_ast_difficulty_timeout_s=float(
            ensemble_data.get("meo_ast_difficulty_timeout_s", 2.0)
        ),
        meo_difficulty_cache_size=int(
            ensemble_data.get("meo_difficulty_cache_size", 2048)
        ),
        meo_policy_refresh_cycle=int(ensemble_data.get("meo_policy_refresh_cycle", 4)),
        planner_learning_enabled=_as_bool(
            ensemble_data.get("planner_learning_enabled", False), default=False
        ),
        curiosity_novelty_scale=float(
            ensemble_data.get("curiosity_novelty_scale", 1.0)
        ),
        curiosity_novelty_k=int(ensemble_data.get("curiosity_novelty_k", 5)),
        curiosity_decay_enabled=_as_bool(
            ensemble_data.get("curiosity_decay_enabled", False), default=False
        ),
        curiosity_decay_window=int(ensemble_data.get("curiosity_decay_window", 100)),
        blend_warmup=int(ensemble_data.get("blend_warmup", 75)),
        blend_max=float(ensemble_data.get("blend_max", 0.65)),
        blend_warmup_global=int(ensemble_data.get("blend_warmup_global", 150)),
        blend_global_floor=float(ensemble_data.get("blend_global_floor", 0.20)),
        # Spec alignment fields
        use_mahalanobis=_as_bool(
            ensemble_data.get("use_mahalanobis", True), default=True
        ),
        precision_lr=float(ensemble_data.get("precision_lr", 0.005)),
        precision_min=float(ensemble_data.get("precision_min", 0.1)),
        precision_max=float(ensemble_data.get("precision_max", 10.0)),
        use_full_spd_metric=_as_bool(
            ensemble_data.get("use_full_spd_metric", False), default=False
        ),
        spd_cov_beta=float(ensemble_data.get("spd_cov_beta", 0.15)),
        spd_cov_shrinkage=float(ensemble_data.get("spd_cov_shrinkage", 0.02)),
        spd_cov_jitter=float(ensemble_data.get("spd_cov_jitter", 1e-6)),
        spd_cov_min_variance=float(ensemble_data.get("spd_cov_min_variance", 1e-9)),
        spd_tail_quantile=float(ensemble_data.get("spd_tail_quantile", 0.95)),
        action_adjust_closure=_as_bool(
            ensemble_data.get("action_adjust_closure", True), default=True
        ),
        action_tighten_filter=_as_bool(
            ensemble_data.get("action_tighten_filter", True), default=True
        ),
        action_relax_filter=_as_bool(
            ensemble_data.get("action_relax_filter", True), default=True
        ),
        action_weight_grow=float(ensemble_data.get("action_weight_grow", 0.25)),
        action_weight_prune=float(ensemble_data.get("action_weight_prune", 0.20)),
        action_weight_closure=float(ensemble_data.get("action_weight_closure", 0.20)),
        action_weight_tighten=float(ensemble_data.get("action_weight_tighten", 0.20)),
        action_weight_relax=float(ensemble_data.get("action_weight_relax", 0.15)),
        semantic_closure=_as_bool(
            ensemble_data.get("semantic_closure", True), default=True
        ),
        semantic_closure_max=int(ensemble_data.get("semantic_closure_max", 5)),
        controller_mode=str(ensemble_data.get("controller_mode", "auto") or "auto"),
        blend_threshold_tau=float(ensemble_data.get("blend_threshold_tau", 0.3)),
        admission_formal_threshold=float(
            ensemble_data.get("admission_formal_threshold", 0.20)
        ),
        admission_learned_threshold=float(
            ensemble_data.get("admission_learned_threshold", 0.15)
        ),
        admission_floor=int(ensemble_data.get("admission_floor", 1)),
        formal_consistency_mode=str(
            ensemble_data.get("formal_consistency_mode", "theorem_prover")
            or "theorem_prover"
        ),
        learned_collapse_enabled=_as_bool(
            ensemble_data.get("learned_collapse_enabled", True), default=True
        ),
        learned_collapse_threshold=float(
            ensemble_data.get("learned_collapse_threshold", 0.55)
        ),
        learned_collapse_similarity_threshold=float(
            ensemble_data.get("learned_collapse_similarity_threshold", 0.90)
        ),
        negation_closure_policy_enabled=_as_bool(
            ensemble_data.get("negation_closure_policy_enabled", True), default=True
        ),
        policy_semantic_closure_enabled=_as_bool(
            ensemble_data.get("policy_semantic_closure_enabled", True), default=True
        ),
        policy_semantic_closure_max=int(
            ensemble_data.get("policy_semantic_closure_max", 5)
        ),
        policy_negation_closure_max=int(
            ensemble_data.get("policy_negation_closure_max", 3)
        ),
        delta_geometry_enabled=_as_bool(
            ensemble_data.get("delta_geometry_enabled", True), default=True
        ),
        delta_geometry_epsilon0=float(
            ensemble_data.get("delta_geometry_epsilon0", 1.0)
        ),
        delta_geometry_epsilon_min=float(
            ensemble_data.get("delta_geometry_epsilon_min", 0.1)
        ),
        delta_geometry_epsilon_max=float(
            ensemble_data.get("delta_geometry_epsilon_max", 4.0)
        ),
        delta_geometry_cov_beta=float(
            ensemble_data.get("delta_geometry_cov_beta", 0.15)
        ),
        delta_geometry_shrinkage=float(
            ensemble_data.get("delta_geometry_shrinkage", 0.05)
        ),
        delta_geometry_metric_mode=str(
            ensemble_data.get("delta_geometry_metric_mode", "mixture_learned_spd")
            or "mixture_learned_spd"
        ),
        delta_geometry_regimes=int(ensemble_data.get("delta_geometry_regimes", 2)),
        delta_geometry_selector_lr=float(
            ensemble_data.get("delta_geometry_selector_lr", 0.05)
        ),
        delta_geometry_learned_metric_blend=float(
            ensemble_data.get("delta_geometry_learned_metric_blend", 0.20)
        ),
        typed_actions_enabled=_as_bool(
            ensemble_data.get("typed_actions_enabled", True), default=True
        ),
        growth_action_dims=_as_str_list(
            ensemble_data.get("growth_action_dims"),
            default=[
                "search_width",
                "retrieval_width",
                "closure_scope",
                "temperature",
            ],
        ),
        prune_action_dims=_as_str_list(
            ensemble_data.get("prune_action_dims"),
            default=[
                "verification_strictness",
                "search_width",
                "retrieval_width",
            ],
        ),
        selector_vectors=_as_float_vector_map(ensemble_data.get("selector_vectors")),
        # Meta-signal weights (Phase 3B)
        meta_signal_w_success=float(ensemble_data.get("meta_signal_w_success", 0.40)),
        meta_signal_w_reward=float(ensemble_data.get("meta_signal_w_reward", 0.20)),
        meta_signal_w_delta=float(ensemble_data.get("meta_signal_w_delta", 0.15)),
        meta_signal_w_wm=float(ensemble_data.get("meta_signal_w_wm", 0.25)),
        # Delta-homeostasis
        delta_homeostasis_enabled=_as_bool(
            ensemble_data.get("delta_homeostasis_enabled", True), default=True
        ),
        delta_homeostasis_lambda=float(
            ensemble_data.get("delta_homeostasis_lambda", 0.15)
        ),
        delta_homeostasis_sigma_blend=float(
            ensemble_data.get("delta_homeostasis_sigma_blend", 0.10)
        ),
        delta_homeostasis_precision_blend=float(
            ensemble_data.get("delta_homeostasis_precision_blend", 0.10)
        ),
        delta_homeostasis_score_factor=float(
            ensemble_data.get("delta_homeostasis_score_factor", 0.15)
        ),
        delta_homeostasis_closure_factor=float(
            ensemble_data.get("delta_homeostasis_closure_factor", 0.20)
        ),
        # v2.2 Forward Model
        forward_model_enabled=_as_bool(
            ensemble_data.get("forward_model_enabled", False), default=False
        ),
        forward_model_lr=_as_float(ensemble_data.get("forward_model_lr", 0.01), 0.01),
        forward_model_history_len=_as_int(
            ensemble_data.get("forward_model_history_len", 20), 20
        ),
        forward_model_residual_capacity=_as_int(
            ensemble_data.get("forward_model_residual_capacity", 100), 100
        ),
        forward_model_lambda_res=_as_float(
            ensemble_data.get("forward_model_lambda_res", 1e-4), 1e-4
        ),
        forward_model_res_cov_beta=_as_float(
            ensemble_data.get("forward_model_res_cov_beta", 0.1), 0.1
        ),
        forward_model_clip_interval=_as_int(
            ensemble_data.get("forward_model_clip_interval", 10), 10
        ),
        # Layer 2
        layer2_whitened_cov_beta=_as_float(
            ensemble_data.get("layer2_whitened_cov_beta", 0.1), 0.1
        ),
        layer2_theta_aniso=_as_float(ensemble_data.get("layer2_theta_aniso", 3.0), 3.0),
        layer2_theta_align=_as_float(ensemble_data.get("layer2_theta_align", 0.7), 0.7),
        layer2_theta_dir=_as_float(ensemble_data.get("layer2_theta_dir", 2.0), 2.0),
        layer2_gamma_dir=_as_float(ensemble_data.get("layer2_gamma_dir", 0.5), 0.5),
        layer2_buffer_capacity=_as_int(
            ensemble_data.get("layer2_buffer_capacity", 30), 30
        ),
        # Layer 3
        layer3_min_cluster_size=_as_int(
            ensemble_data.get("layer3_min_cluster_size", 5), 5
        ),
        layer3_theta_rel=_as_float(ensemble_data.get("layer3_theta_rel", 0.3), 0.3),
        layer3_theta_gram_stability=_as_float(
            ensemble_data.get("layer3_theta_gram_stability", 0.8), 0.8
        ),
        layer3_gram_history_capacity=_as_int(
            ensemble_data.get("layer3_gram_history_capacity", 20), 20
        ),
        layer3_w_c=_as_float(ensemble_data.get("layer3_w_c", 1.0 / 3.0), 1.0 / 3.0),
        layer3_w_p=_as_float(ensemble_data.get("layer3_w_p", 1.0 / 3.0), 1.0 / 3.0),
        layer3_w_s=_as_float(ensemble_data.get("layer3_w_s", 1.0 / 3.0), 1.0 / 3.0),
        # Rupture pressure
        rupture_theta_stall=_as_int(ensemble_data.get("rupture_theta_stall", 15), 15),
        rupture_theta_pressure=_as_float(
            ensemble_data.get("rupture_theta_pressure", 5.0), 5.0
        ),
        rupture_pressure_decay=_as_float(
            ensemble_data.get("rupture_pressure_decay", 0.95), 0.95
        ),
        rupture_k_max=_as_int(ensemble_data.get("rupture_k_max", 50), 50),
        rupture_w_L1=_as_float(ensemble_data.get("rupture_w_L1", 1.0), 1.0),
        rupture_w_L2=_as_float(ensemble_data.get("rupture_w_L2", 2.0), 2.0),
        rupture_w_L3=_as_float(ensemble_data.get("rupture_w_L3", 2.0), 2.0),
        online_model_autoload=_as_bool(
            ensemble_data.get("online_model_autoload", False), default=False
        ),
    )
    retrieval = RetrievalConfig(
        enabled=_as_bool(retrieval_data.get("enabled", True), default=True),
        index_path=str(
            _resolve_config_path(
                retrieval_data.get("index_path", "./runs/lemma_index.jsonl"),
                config_dir=config_dir,
            )
        ),
        meta_path=str(
            _resolve_config_path(
                retrieval_data.get("meta_path", "./runs/lemma_index.meta.json"),
                config_dir=config_dir,
            )
        ),
        dense_index_path=str(
            _resolve_config_path(
                retrieval_data.get("dense_index_path", "./runs/lemma_dense.npy"),
                config_dir=config_dir,
            )
        ),
        dense_meta_path=str(
            _resolve_config_path(
                retrieval_data.get("dense_meta_path", "./runs/lemma_dense.meta.json"),
                config_dir=config_dir,
            )
        ),
        mathlib_root=_resolve_existing_root_path(
            retrieval_data.get("mathlib_root"),
            config_dir=config_dir,
        ),
        project_root=_resolve_existing_root_path(
            retrieval_data.get("project_root"),
            config_dir=config_dir,
        ),
        include_mathlib=_as_bool(
            retrieval_data.get("include_mathlib", True), default=True
        ),
        include_project=_as_bool(
            retrieval_data.get("include_project", True), default=True
        ),
        update_on_start=_as_bool(
            retrieval_data.get("update_on_start", False), default=False
        ),
        max_lemmas=int(retrieval_data.get("max_lemmas", 250000)),
        top_k=int(retrieval_data.get("top_k", 250)),
        max_prompt_lemmas=int(retrieval_data.get("max_prompt_lemmas", 30)),
        min_score=float(retrieval_data.get("min_score", 0.05)),
        bm25_k1=float(retrieval_data.get("bm25_k1", 1.2)),
        bm25_b=float(retrieval_data.get("bm25_b", 0.75)),
        weight_bm25=float(retrieval_data.get("weight_bm25", 1.0)),
        weight_symbol=float(retrieval_data.get("weight_symbol", 0.25)),
        weight_name=float(retrieval_data.get("weight_name", 0.35)),
        use_embeddings=_as_bool(
            retrieval_data.get("use_embeddings", True), default=True
        ),
        embedding_dim=int(retrieval_data.get("embedding_dim", 768)),
        embedding_seed=int(retrieval_data.get("embedding_seed", 1337)),
        weight_embed=float(retrieval_data.get("weight_embed", 0.35)),
        dense_retrieval_enabled=_as_bool(
            retrieval_data.get("dense_retrieval_enabled", False), default=False
        ),
        dense_build_on_start=_as_bool(
            retrieval_data.get("dense_build_on_start", False), default=False
        ),
        dense_top_k=int(retrieval_data.get("dense_top_k", 200)),
        hybrid_pool_multiplier=int(retrieval_data.get("hybrid_pool_multiplier", 5)),
        dense_search_mode=str(retrieval_data.get("dense_search_mode", "full")),
        embedding_backend=str(
            retrieval_data.get("embedding_backend", "sentence_transformers")
        ),
        embedding_model=str(
            retrieval_data.get("embedding_model", "BAAI/bge-base-en-v1.5")
        ),
        embedding_device=retrieval_data.get("embedding_device", None),
        embedding_normalize=_as_bool(
            retrieval_data.get("embedding_normalize", True), default=True
        ),
        embedding_prefer_local_files=_as_bool(
            retrieval_data.get("embedding_prefer_local_files", True),
            default=True,
        ),
        embedding_local_files_only=_as_bool(
            retrieval_data.get("embedding_local_files_only", True),
            default=True,
        ),
        embedding_allow_download=_as_bool(
            retrieval_data.get("embedding_allow_download", False),
            default=False,
        ),
        embedding_init_timeout_s=float(
            retrieval_data.get("embedding_init_timeout_s", 8.0)
        ),
        embedding_cache_size=int(retrieval_data.get("embedding_cache_size", 10000)),
        query_embedding_cache_size=int(
            retrieval_data.get("query_embedding_cache_size", 512)
        ),
        dense_build_batch_size=int(retrieval_data.get("dense_build_batch_size", 256)),
        boost_domain_prefix=float(retrieval_data.get("boost_domain_prefix", 1.2)),
        include_docstrings=_as_bool(
            retrieval_data.get("include_docstrings", False), default=False
        ),
        goal_conditioned=_as_bool(
            retrieval_data.get("goal_conditioned", True), default=True
        ),
        goal_query_weight=float(retrieval_data.get("goal_query_weight", 1.0)),
        rerank_mode=str(retrieval_data.get("rerank_mode", "none")),
        rerank_top_n=int(retrieval_data.get("rerank_top_n", 50)),
        rerank_llm_role=str(retrieval_data.get("rerank_llm_role", "planner")),
        cross_encoder_model=str(
            retrieval_data.get(
                "cross_encoder_model", "BAAI/bge-reranker-v2-minicpm-layerwise"
            )
        ),
        cross_encoder_fallback_model=str(
            retrieval_data.get(
                "cross_encoder_fallback_model", "BAAI/bge-reranker-large"
            )
        ),
        cross_encoder_force_sentence_transformers=_as_bool(
            retrieval_data.get("cross_encoder_force_sentence_transformers", False),
            default=False,
        ),
        cross_encoder_device=retrieval_data.get("cross_encoder_device", None),
        cross_encoder_cache_size=int(
            retrieval_data.get("cross_encoder_cache_size", 5000)
        ),
        cross_encoder_score_timeout_s=float(
            retrieval_data.get("cross_encoder_score_timeout_s", 20.0)
        ),
        cross_encoder_cutoff_layers=list(
            retrieval_data.get("cross_encoder_cutoff_layers", [28])
        ),
        cross_encoder_use_fp16=_as_bool(
            retrieval_data.get("cross_encoder_use_fp16", True), default=True
        ),
        cross_encoder_transient_cooldown_s=float(
            retrieval_data.get("cross_encoder_transient_cooldown_s", 120.0)
        ),
        cross_encoder_max_transient_failures=int(
            retrieval_data.get("cross_encoder_max_transient_failures", 3)
        ),
        cross_encoder_reset_on_problem_start=_as_bool(
            retrieval_data.get("cross_encoder_reset_on_problem_start", True),
            default=True,
        ),
        ltr_enabled=_as_bool(retrieval_data.get("ltr_enabled", False), default=False),
        ltr_weights_path=str(
            _resolve_config_path(
                retrieval_data.get(
                    "ltr_weights_path", "./runs/retrieval_ltr_weights.json"
                ),
                config_dir=config_dir,
            )
        ),
        ltr_learning_rate=float(retrieval_data.get("ltr_learning_rate", 0.05)),
        ltr_warmup_updates=int(retrieval_data.get("ltr_warmup_updates", 50)),
        ltr_min_updates=int(retrieval_data.get("ltr_min_updates", 10)),
        ltr_negative_samples=int(retrieval_data.get("ltr_negative_samples", 32)),
        ltr_positive_weight=float(retrieval_data.get("ltr_positive_weight", 2.0)),
        ltr_weight_decay=float(retrieval_data.get("ltr_weight_decay", 0.999)),
        prompt_budget_enabled=_as_bool(
            retrieval_data.get("prompt_budget_enabled", True), default=True
        ),
        prompt_budget_tokens=int(retrieval_data.get("prompt_budget_tokens", 1200)),
        prompt_budget_hard_cap_tokens=int(
            retrieval_data.get("prompt_budget_hard_cap_tokens", 20000)
        ),
        prompt_budget_dedup_jaccard=float(
            retrieval_data.get("prompt_budget_dedup_jaccard", 0.92)
        ),
        log_scores=_as_bool(retrieval_data.get("log_scores", False), default=False),
        log_top_k=int(retrieval_data.get("log_top_k", 10)),
    )
    tactic_tree = TacticTreeConfig(
        enabled=_as_bool(tactic_tree_data.get("enabled", True), default=True),
        mode=str(tactic_tree_data.get("mode", "beam")),
        beam_width=int(tactic_tree_data.get("beam_width", 3)),
        max_steps=int(tactic_tree_data.get("max_steps", 20)),
        max_candidates_per_node=int(tactic_tree_data.get("max_candidates_per_node", 5)),
        mcts_simulations=int(tactic_tree_data.get("mcts_simulations", 64)),
        mcts_c_puct=float(tactic_tree_data.get("mcts_c_puct", 1.4)),
        time_limit=float(tactic_tree_data.get("time_limit", 300.0)),
        max_depth=int(tactic_tree_data.get("max_depth", 25)),
        weight_progress=float(tactic_tree_data.get("weight_progress", 0.5)),
        weight_prior=float(tactic_tree_data.get("weight_prior", 0.2)),
        weight_ensemble=float(tactic_tree_data.get("weight_ensemble", 0.2)),
        depth_penalty_factor=float(tactic_tree_data.get("depth_penalty_factor", 0.02)),
        multi_tactic=_as_bool(tactic_tree_data.get("multi_tactic", True), default=True),
        num_tactic_candidates=int(tactic_tree_data.get("num_tactic_candidates", 5)),
        max_cache_entries=int(tactic_tree_data.get("max_cache_entries", 10000)),
        feedback_enabled=_as_bool(
            tactic_tree_data.get("feedback_enabled", True), default=True
        ),
        feedback_memory=_as_bool(
            tactic_tree_data.get("feedback_memory", False), default=False
        ),
        recursive_enabled=_as_bool(
            tactic_tree_data.get("recursive_enabled", False), default=False
        ),
        recursive_max_depth=int(tactic_tree_data.get("recursive_max_depth", 8)),
        recursive_max_nodes=int(tactic_tree_data.get("recursive_max_nodes", 160)),
        recursive_retrieval_rounds=int(
            tactic_tree_data.get("recursive_retrieval_rounds", 2)
        ),
        recursive_direct_rounds=int(tactic_tree_data.get("recursive_direct_rounds", 2)),
        recursive_assembly_rounds=int(
            tactic_tree_data.get("recursive_assembly_rounds", 4)
        ),
        recursive_decomposition_enabled=_as_bool(
            tactic_tree_data.get("recursive_decomposition_enabled", True),
            default=True,
        ),
        recursive_tactic_tree_time_limit=float(
            tactic_tree_data.get("recursive_tactic_tree_time_limit", 60.0)
        ),
    )
    proven_lemma = ProvenLemmaConfig(
        enabled=_as_bool(proven_lemma_data.get("enabled", True), default=True),
        path=str(proven_lemma_data.get("path", "./runs/proven_lemmas.jsonl")),
        max_entries=int(proven_lemma_data.get("max_entries", 50000)),
        top_k=int(proven_lemma_data.get("top_k", 20)),
        max_prompt_lemmas=int(proven_lemma_data.get("max_prompt_lemmas", 10)),
        bm25_k1=float(proven_lemma_data.get("bm25_k1", 1.2)),
        bm25_b=float(proven_lemma_data.get("bm25_b", 0.75)),
        weight_bm25=float(proven_lemma_data.get("weight_bm25", 0.6)),
        weight_embed=float(proven_lemma_data.get("weight_embed", 0.4)),
        pool_multiplier=int(proven_lemma_data.get("pool_multiplier", 5)),
        min_score=float(proven_lemma_data.get("min_score", 0.25)),
        embedding_backend=str(
            proven_lemma_data.get("embedding_backend", "sentence_transformers")
        ),
        embedding_model=str(
            proven_lemma_data.get("embedding_model", "BAAI/bge-base-en-v1.5")
        ),
        embedding_device=proven_lemma_data.get("embedding_device", None),
        embedding_normalize=_as_bool(
            proven_lemma_data.get("embedding_normalize", True), default=True
        ),
        embedding_prefer_local_files=_as_bool(
            proven_lemma_data.get("embedding_prefer_local_files", True),
            default=True,
        ),
        embedding_local_files_only=_as_bool(
            proven_lemma_data.get("embedding_local_files_only", True),
            default=True,
        ),
        embedding_allow_download=_as_bool(
            proven_lemma_data.get("embedding_allow_download", False),
            default=False,
        ),
        embedding_init_timeout_s=float(
            proven_lemma_data.get("embedding_init_timeout_s", 8.0)
        ),
        embedding_dim=int(
            proven_lemma_data.get("embedding_dim", ensemble.embedding_dim)
        ),
        embedding_seed=int(proven_lemma_data.get("embedding_seed", ensemble.seed)),
    )
    model_pool_data = {
        str(role_name).strip(): _as_bool(enabled, default=False)
        for role_name, enabled in _section_mapping(data, "model_pool").items()
        if str(role_name).strip()
    }
    tactic_oracle = TacticOracleConfig(
        enabled=_as_bool(tactic_oracle_data.get("enabled", True), default=True),
        timeout_s=int(tactic_oracle_data.get("timeout_s", 60)),
        max_heartbeats=int(tactic_oracle_data.get("max_heartbeats", 800000)),
        max_concurrent=int(tactic_oracle_data.get("max_concurrent", 2)),
        on_unknown_id=_as_bool(
            tactic_oracle_data.get("on_unknown_id", True), default=True
        ),
        on_compiled_slot=_as_bool(
            tactic_oracle_data.get("on_compiled_slot", True), default=True
        ),
        on_tactic_tree=_as_bool(
            tactic_oracle_data.get("on_tactic_tree", True), default=True
        ),
        on_goal_start=_as_bool(
            tactic_oracle_data.get("on_goal_start", True), default=True
        ),
        goal_start_timeout_s=int(tactic_oracle_data.get("goal_start_timeout_s", 30)),
        goal_start_max_heartbeats=int(
            tactic_oracle_data.get("goal_start_max_heartbeats", 400000)
        ),
        goal_start_max_suggestions=int(
            tactic_oracle_data.get("goal_start_max_suggestions", 3)
        ),
        goal_start_max_depth=int(tactic_oracle_data.get("goal_start_max_depth", 8)),
        commands=str(tactic_oracle_data.get("commands", "")),
        tier1_timeout_s=int(tactic_oracle_data.get("tier1_timeout_s", 5)),
        tier1_max_heartbeats=int(tactic_oracle_data.get("tier1_max_heartbeats", 50000)),
        tier2_timeout_s=int(tactic_oracle_data.get("tier2_timeout_s", 8)),
        tier2_max_heartbeats=int(
            tactic_oracle_data.get("tier2_max_heartbeats", 200000)
        ),
        tier3_timeout_s=int(tactic_oracle_data.get("tier3_timeout_s", 15)),
        tier3_max_heartbeats=int(
            tactic_oracle_data.get("tier3_max_heartbeats", 400000)
        ),
        include_decide=_as_bool(
            tactic_oracle_data.get("include_decide", True), default=True
        ),
        decide_timeout_s=int(tactic_oracle_data.get("decide_timeout_s", 10)),
        decide_max_heartbeats=int(
            tactic_oracle_data.get("decide_max_heartbeats", 150000)
        ),
        include_prop_complete=_as_bool(
            tactic_oracle_data.get("include_prop_complete", False), default=False
        ),
        prop_complete_timeout_s=int(
            tactic_oracle_data.get("prop_complete_timeout_s", 8)
        ),
        prop_complete_max_heartbeats=int(
            tactic_oracle_data.get("prop_complete_max_heartbeats", 200000)
        ),
        include_grind=_as_bool(
            tactic_oracle_data.get("include_grind", True), default=True
        ),
        grind_timeout_s=int(tactic_oracle_data.get("grind_timeout_s", 20)),
        grind_max_heartbeats=int(
            tactic_oracle_data.get("grind_max_heartbeats", 600000)
        ),
        include_polyrith=_as_bool(
            tactic_oracle_data.get("include_polyrith", False), default=False
        ),
        include_native_decide=_as_bool(
            tactic_oracle_data.get("include_native_decide", False), default=False
        ),
        retrieval_informed_enabled=_as_bool(
            tactic_oracle_data.get("retrieval_informed_enabled", True), default=True
        ),
        retrieval_informed_max_lemmas=int(
            tactic_oracle_data.get("retrieval_informed_max_lemmas", 5)
        ),
        retrieval_informed_timeout_s=_as_float(
            tactic_oracle_data.get("retrieval_informed_timeout_s", 3.0), 3.0
        ),
        retrieval_informed_max_heartbeats=int(
            tactic_oracle_data.get("retrieval_informed_max_heartbeats", 50000)
        ),
        repair_max_wall_s=_as_float(
            tactic_oracle_data.get("repair_max_wall_s", 20.0), 20.0
        ),
    )
    if tactic_oracle.include_prop_complete:
        lean.extra_imports.append("src.EnsembleProver.PropComplete")
    app = AppConfig(
        roles=roles,
        lean=lean,
        search=search,
        budgets=budgets,
        ensemble=ensemble,
        retrieval=retrieval,
        strategy=strategy,
        tactic_tree=tactic_tree,
        proven_lemma=proven_lemma,
        model_pool=model_pool_data,
        token_pricing=token_pricing,
        tactic_oracle=tactic_oracle,
    )
    # Enforce MEO core: master policy requires the ensemble engine.
    if app.ensemble.master_enabled and not app.ensemble.enabled:
        app.ensemble.enabled = True
        logger.warning(
            "ensemble.master_enabled is true but ensemble.enabled was false; auto-enabling ensemble"
        )
    validate_config(app)
    return app
