"""Pure, scoped reduction of trace rows into a bounded run state.

Rules that matter more than any single field:

* Root truth is scoped. Only rows whose ``session_scope`` is ``problem`` can
  change the problem's root status. A child session finalizing *its* root
  is a milestone, not completion of the problem.
* A Lean-accepted helper or child proof is scoped evidence. Typechecking is
  not proof. A rejected attempt does not falsify a claim.
* Deferrals and releases are keyed by activation and action identity. A
  release clears only its matching deferral; unmatched releases are counted
  and kept as history.
* Bulk rows (snapshots, transcripts) contribute compact counts and are then
  dropped. Missing evidence is unknown, never zero.
* ``summary.total_turns`` and trace row counts are recorder rows, not
  logical prove/refine turns.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from typing import Any

from .live_math import LiveMathState

PROBLEM_SCOPE = "problem"
MAX_TRANSCRIPT = 500
MAX_MILESTONES = 2000
MAX_HELPERS = 5000
MAX_DEFERRED = 2000
MAX_PHASES = 512
MAX_HELPER_MATH = 512
MAX_MATH_TEXT = 16 * 1024
MAX_MATH_TOTAL = 512 * 1024

_RELEASE_VERDICTS = frozenset(
    {
        "deferred_static_action_retry_released",
        "deferred_action_retry_released",
        "paired_frontier_static_guard_cleared",
    }
)
_LEAN_PHASES = frozenset(
    {
        "mini_recursive_claim_tactic",
        "mini_recursive_root_tactic",
        "mini_recursive_llm_root_close",
        "mini_recursive_root_close_speculative_tactic",
        "proof_state_child_tactic",
        "proof_state_root_assembly",
        "proof_state_child_falsification",
        "mini_recursive_root_falsification",
        "mini_recursive_claim_falsification",
    }
)
_ROLE_LANES = {"prove": "prover", "refine": "refiner", "planner": "planner"}


@dataclass
class Line:
    elapsed_s: float
    scope: str
    kind: str  # info | good | bad | warn | milestone
    text: str
    turn_index: int = 0


@dataclass
class Lane:
    name: str
    count: int = 0
    last_elapsed_s: float | None = None
    last_text: str = ""


@dataclass
class RunState:
    live_math: LiveMathState = field(default_factory=LiveMathState)
    rows: int = 0
    last_elapsed_s: float = 0.0
    last_turn_index: int = 0
    first_turn_index: int | None = None
    theorem: str = ""
    answer_visibility: str = ""
    config: dict[str, dict[str, Any]] = field(default_factory=dict)
    governors: dict[str, Any] = field(default_factory=dict)
    root_status: str = "unresolved"
    root_status_elapsed_s: float | None = None
    child_root_finalizations: int = 0
    recursive_status: str = ""
    recursive_status_detail: str = ""
    helpers_accepted: dict[str, float] = field(default_factory=dict)
    helpers_overflow: int = 0
    helper_supports: dict[str, list[str]] = field(default_factory=dict)
    helper_math: dict[str, dict[str, Any]] = field(default_factory=dict)
    helper_math_chars: int = 0
    root_helper_names: list[str] = field(default_factory=list)
    root_dependency_helper_names: list[str] = field(default_factory=list)
    milestones: deque[Line] = field(default_factory=lambda: deque(maxlen=MAX_MILESTONES))
    transcript: deque[Line] = field(default_factory=lambda: deque(maxlen=MAX_TRANSCRIPT))
    lanes: dict[str, Lane] = field(
        default_factory=lambda: {
            name: Lane(name) for name in ("prover", "refiner", "planner", "lean")
        }
    )
    deferred: dict[tuple[str, str], dict[str, Any]] = field(default_factory=dict)
    deferred_overflow: int = 0
    releases_unmatched: int = 0
    counters: dict[str, int] = field(default_factory=dict)
    phases: dict[str, int] = field(default_factory=dict)
    phases_overflow: int = 0
    cost_accounted_usd: float = 0.0
    cost_calls_priced: int = 0
    cost_calls_unpriced: int = 0
    snapshot: dict[str, Any] = field(default_factory=dict)
    iteration_by_scope: dict[str, int] = field(default_factory=dict)
    strong_progress_last_elapsed_s: float | None = None
    strong_progress_last_reason: str = ""
    invalid_rows: int = 0

    @property
    def generation_boundary(self) -> bool:
        return self.first_turn_index is not None and self.first_turn_index > 1


# -- small guards ---------------------------------------------------------------


def _str(value: Any, limit: int = 200) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    text = value if isinstance(value, str) else str(value)
    text = text.replace("\n", " ")
    return text if len(text) <= limit else text[: limit - 1] + "…"


def _num(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    if value != value or value in (float("inf"), float("-inf")):
        return None
    return float(value)


def _int(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, int):
        return None
    return value


def _dict(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def _bump(state: RunState, key: str, by: int = 1) -> None:
    state.counters[key] = state.counters.get(key, 0) + by


def _touch(state: RunState, lane: str, elapsed: float, text: str) -> None:
    entry = state.lanes.get(lane)
    if entry is None:
        return
    entry.count += 1
    entry.last_elapsed_s = elapsed
    entry.last_text = text


def _emit(state: RunState, rec: dict[str, Any], kind: str, text: str, *, milestone: bool = False) -> None:
    line = Line(
        elapsed_s=_num(rec.get("elapsed_s")) or 0.0,
        scope=_str(rec.get("session_scope"), 40),
        kind=kind,
        text=text,
        turn_index=_int(rec.get("turn_index")) or 0,
    )
    state.transcript.append(line)
    if milestone:
        state.milestones.append(line)


def _scope_tag(rec: dict[str, Any]) -> str:
    scope = _str(rec.get("session_scope"), 40)
    return scope or "unscoped"


# -- phase handlers ----------------------------------------------------------


def _role_config(block: dict[str, Any]) -> dict[str, Any]:
    preflight = _dict(block.get("reasoning_preflight"))
    return {
        "provider": _str(block.get("provider"), 60),
        "model": _str(block.get("model"), 120),
        "mode": _str(block.get("requested_mode"), 30),
        "effort": _str(block.get("requested_effort"), 30),
        "effective_effort": _str(preflight.get("effective_effort"), 30),
        "base_url": _str(preflight.get("base_url"), 120),
        "transport": _str(preflight.get("transport_mode"), 30),
    }


def _on_run_config(state: RunState, rec: dict[str, Any]) -> None:
    for role in ("prover", "refiner"):
        block = _dict(rec.get(f"{role}_reasoning"))
        if block:
            state.config[role] = _role_config(block)
    for key in (
        "llm_deadline_policy",
        "mini_run_wall_clock_budget_s",
        "mini_no_strong_progress_budget_s",
        "mini_worker_shutdown_timeout_s",
        "mini_worker_timeout_s",
    ):
        if key in rec:
            state.governors[key] = rec.get(key)
    parts = []
    for role, cfg in state.config.items():
        parts.append(f"{role}={cfg['provider']}:{cfg['model']} reasoning {cfg['mode'] or '?'}/{cfg['effort'] or cfg['effective_effort'] or 'unspecified'}")
    _emit(state, rec, "info", "run config recorded · " + "; ".join(parts) if parts else "run config recorded")


def _on_answer_visibility(state: RunState, rec: dict[str, Any]) -> None:
    state.answer_visibility = _str(rec.get("verdict"), 60)
    _emit(state, rec, "info", f"answer visibility: {state.answer_visibility} (opaque_mode={_str(rec.get('opaque_mode'))})")


def _on_snapshot(state: RunState, rec: dict[str, Any]) -> None:
    snapshot = _dict(rec.get("snapshot"))
    proof_state = _dict(snapshot.get("proof_state"))
    session_state = _dict(snapshot.get("session_state"))
    cost = _dict(snapshot.get("cost_budget"))
    compact: dict[str, Any] = {"elapsed_s": _num(rec.get("elapsed_s")), "scope": _scope_tag(rec)}
    for key in ("node_count", "open_nodes", "proved_nodes"):
        compact[key] = _int(proof_state.get(key))
    compact["work_frontier_status"] = _str(proof_state.get("work_frontier_status"), 80) or "unknown"
    frontier = proof_state.get("frontier")
    compact["frontier_sample"] = len(frontier) if isinstance(frontier, list) else None
    compact["root_node_id"] = _str(proof_state.get("root_node_id"), 80)
    compact["iteration"] = _int(session_state.get("iteration"))
    compact["root_finalized_in_scope"] = session_state.get("root_finalized") if isinstance(session_state.get("root_finalized"), bool) else None
    compact["governor_elapsed_s"] = _num(session_state.get("run_governor_elapsed_s"))
    compact["accounted_cost_usd"] = _num(cost.get("llm_budget_accounted_cost_usd"))
    compact["cost_accounting_incomplete"] = cost.get("cost_accounting_incomplete") if isinstance(cost.get("cost_accounting_incomplete"), bool) else None
    if _scope_tag(rec) == PROBLEM_SCOPE or not state.snapshot:
        state.snapshot = compact


def _on_iteration(state: RunState, rec: dict[str, Any]) -> None:
    iteration = _int(rec.get("iteration"))
    if iteration is not None:
        state.iteration_by_scope[_scope_tag(rec)] = iteration


def _on_outcome(state: RunState, rec: dict[str, Any]) -> None:
    _bump(state, "outcomes")
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    if rec.get("strong_progress") is True:
        state.strong_progress_last_elapsed_s = elapsed
        state.strong_progress_last_reason = _str(rec.get("action_id"), 60)
    exc = rec.get("exception")
    if exc:
        _emit(state, rec, "warn", f"action {_str(rec.get('action_id'), 60)} raised: {_str(exc, 160)}")


def _lean_error_type(rec: dict[str, Any]) -> str:
    analysis = rec.get("lean_failure_analysis")
    if isinstance(analysis, dict):
        return _str(analysis.get("error_type"), 60) or "unknown"
    return "unknown"


def _on_conversation(state: RunState, rec: dict[str, Any], phase: str) -> None:
    lane = _ROLE_LANES.get(phase, "prover")
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    verdict = _str(rec.get("verdict"), 80)
    _bump(state, f"{phase}_rows")
    turn = _int(rec.get("turn_in_phase"))
    label = f"{lane} turn {turn}" if turn is not None else lane
    _touch(state, lane, elapsed, f"{verdict}")
    if verdict == "llm_response":
        tools = _int(rec.get("tool_calls_used"))
        seconds = _num(rec.get("llm_elapsed_s"))
        _emit(
            state,
            rec,
            "info",
            f"{label}: model responded in {seconds:.0f}s, {tools or 0} tool calls, model {_str(rec.get('model'), 60)}"
            if seconds is not None
            else f"{label}: model responded, {tools or 0} tool calls",
        )
    elif verdict == "lean_rejected":
        _bump(state, "lean_checks")
        _bump(state, "lean_rejections")
        _touch(state, "lean", elapsed, "proof rejected")
        _emit(state, rec, "bad", f"{label}: Lean rejected the proof attempt ({_lean_error_type(rec)}); the claim itself is not refuted")
    elif verdict == "solved":
        _bump(state, "lean_checks")
        _touch(state, "lean", elapsed, "proof accepted")
        _emit(state, rec, "good", f"{label}: Lean accepted a proof in {_scope_tag(rec)} scope (scoped evidence, not export verification)", milestone=True)
    elif verdict == "llm_call_failed":
        _emit(state, rec, "warn", f"{label}: provider call failed ({_str(rec.get('llm_failure_kind') or rec.get('error'), 80)})")


def _on_llm_usage(state: RunState, rec: dict[str, Any]) -> None:
    _bump(state, "llm_calls")
    role = _str(rec.get("role"), 20)
    lane = _ROLE_LANES.get(role)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    if lane:
        _touch(state, lane, elapsed, f"usage {_str(rec.get('status'), 20)}")
    if _str(rec.get("status"), 20) != "success":
        return
    cost = _num(rec.get("cost_usd"))
    if rec.get("pricing_known") is True and cost is not None:
        state.cost_calls_priced += 1
        state.cost_accounted_usd += cost
    else:
        state.cost_calls_unpriced += 1


def _on_plan(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    _touch(state, "planner", elapsed, verdict)
    pass_index = _int(rec.get("pass_index"))
    prefix = f"planner pass {pass_index}" if pass_index is not None else "planner"
    if verdict == "plan_started":
        _bump(state, "planner_passes")
        _emit(state, rec, "info", f"{prefix}: started ({_str(rec.get('planner_model'), 60)})")
    elif verdict in {"plan_compiled", "plan_accepted_after_filters"}:
        _emit(state, rec, "info", f"{prefix}: {verdict.replace('_', ' ')}")
    elif "fail" in verdict or "degenerate" in verdict:
        _emit(state, rec, "warn", f"{prefix}: {verdict}")


def _on_planner_job(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    _touch(state, "planner", _num(rec.get("elapsed_s")) or 0.0, verdict)
    if verdict == "planner_job_launched":
        _emit(state, rec, "info", "planner job launched")


def _on_claim_typecheck(state: RunState, rec: dict[str, Any]) -> None:
    _bump(state, "claim_typechecks")
    _touch(state, "lean", _num(rec.get("elapsed_s")) or 0.0, "claim typecheck")
    name = _str(rec.get("claim_name") or rec.get("helper_name"), 80)
    if rec.get("ok") is True:
        _emit(state, rec, "info", f"claim {name}: statement typechecked (well-formed, not proved)")
    else:
        _emit(state, rec, "warn", f"claim {name}: statement did not typecheck ({_str(rec.get('verdict'), 60)})")


def _on_claim_llm(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    name = _str(rec.get("helper_name") or rec.get("claim_name"), 100)
    if verdict == "claim_llm_solved":
        _bump(state, "lean_checks")
        _touch(state, "lean", _num(rec.get("elapsed_s")) or 0.0, "helper proof accepted")
        _emit(state, rec, "good", f"helper {name}: proof accepted by Lean (helper scope)")
    else:
        _emit(state, rec, "info", f"helper {name}: {verdict}")


def _on_claim_deadline(state: RunState, rec: dict[str, Any]) -> None:
    name = _str(rec.get("helper_name") or rec.get("claim_name"), 100)
    verdict = _str(rec.get("verdict"), 80)
    detail = (
        "child proof attempt exhausted its time allowance"
        if verdict == "claim_elapsed_budget_exhausted"
        else verdict
    )
    _emit(state, rec, "info", f"helper {name}: {detail}")


def _on_helper_accept(state: RunState, rec: dict[str, Any]) -> None:
    name = _str(rec.get("helper_name"), 160)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    if name:
        if name in state.helpers_accepted or len(state.helpers_accepted) < MAX_HELPERS:
            state.helpers_accepted[name] = elapsed
            _record_helper_math(state, rec, name)
            supports = rec.get("support_names")
            if isinstance(supports, list):
                state.helper_supports[name] = [_str(s, 160) for s in supports if isinstance(s, str)][:50]
        else:
            state.helpers_overflow += 1
    _emit(state, rec, "good", f"helper accepted: {name} (source {_str(rec.get('source'), 40)})", milestone=True)


def _record_helper_math(state: RunState, rec: dict[str, Any], name: str) -> None:
    """Keep exact acceptance statements; merged names must fail closed."""
    if name not in state.helper_math and len(state.helper_math) >= MAX_HELPER_MATH:
        return
    keys = ("session_scope", "session_activation_id", "recursive_attempt_activation_id")
    scope = tuple(rec.get(key, "") for key in keys)
    identity = rec.get("statement_identity", "")
    environment = rec.get("verification_environment_hash", "")
    statement = rec.get("statement", "")
    valid_identity = all(isinstance(value, str) and len(value) <= 512 for value in (*scope, identity, environment))
    if valid_identity:
        try:
            "".join((*scope, identity, environment)).encode("utf-8")
        except UnicodeError:
            valid_identity = False
    valid_statement = isinstance(statement, str) and len(statement) <= MAX_MATH_TEXT and "\0" not in statement
    if valid_statement:
        try:
            statement.encode("utf-8")
        except UnicodeError:
            valid_statement = False
    reason = "" if valid_statement and statement.strip() else "The acceptance did not record a bounded Lean statement."
    previous = state.helper_math.get(name)
    if not valid_identity or rec.get("helper_name") != name:
        if previous:
            state.helper_math_chars -= len(previous["statement"])
        state.helper_math[name] = {"statement": "", "identity": (), "ambiguous": True,
                                   "reason": "The recorded helper identity is incomplete or exceeds the display limit."}
        return
    if previous and (previous.get("ambiguous") or previous["identity"] != (scope, identity, environment)
                     or (valid_statement and previous["statement"] and previous["statement"] != statement)):
        state.helper_math_chars -= len(previous["statement"])
        state.helper_math[name] = {"statement": "", "identity": (), "ambiguous": True,
                                   "reason": "This helper name has multiple recorded identities or scopes; its mathematics cannot be selected safely."}
        return
    text = statement if valid_statement and valid_identity and rec.get("helper_name") == name else ""
    old_chars = len(previous["statement"]) if previous else 0
    if state.helper_math_chars - old_chars + len(text) > MAX_MATH_TOTAL:
        text = ""
        reason = "The retained mathematics display limit was reached."
    state.helper_math_chars += len(text) - old_chars
    state.helper_math[name] = {"statement": text, "identity": (scope, identity, environment),
                               "ambiguous": False, "reason": reason}


def _on_accepted_proof(state: RunState, rec: dict[str, Any]) -> None:
    kind = _str(rec.get("acceptance_kind"), 30)
    name = _str(rec.get("helper_name"), 160)
    _emit(state, rec, "good", f"committed {kind or 'proof'} acceptance: {name or '(unnamed)'} in {_scope_tag(rec)} scope", milestone=True)


def _on_root_finalization(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    accepted = rec.get("accepted") is True or verdict == "root_finalization_accepted"
    scope = _scope_tag(rec)
    if scope == PROBLEM_SCOPE:
        if accepted:
            state.root_status = "root_finalization_accepted"
            state.root_status_elapsed_s = elapsed
            for key, attr in (("helper_names", "root_helper_names"), ("dependency_helper_names", "root_dependency_helper_names")):
                names = rec.get(key)
                if isinstance(names, list):
                    setattr(state, attr, [_str(n, 160) for n in names if isinstance(n, str)][:500])
            _emit(state, rec, "good", "ROOT finalization accepted for the problem (internal milestone; export not yet verified)", milestone=True)
        else:
            _emit(state, rec, "warn", f"root finalization: {verdict}", milestone=True)
    else:
        if accepted:
            state.child_root_finalizations += 1
            _emit(state, rec, "good", f"child root finalized in {scope} scope (does not finish the problem)", milestone=True)
        else:
            _emit(state, rec, "info", f"child root finalization in {scope} scope: {verdict}")


def _on_root_solved(state: RunState, rec: dict[str, Any]) -> None:
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    scope = _scope_tag(rec)
    if scope == PROBLEM_SCOPE and rec.get("accepted") is True:
        state.root_status = "root_solved_internal"
        state.root_status_elapsed_s = elapsed
        _emit(state, rec, "good", "ROOT solved internally for the problem; awaiting export verification in summary.json", milestone=True)
    elif rec.get("accepted") is True:
        _emit(state, rec, "info", f"child root solved in {scope} scope (scoped evidence)", milestone=True)


def _on_recursive_complete(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    state.recursive_status = verdict
    state.recursive_status_detail = _str(rec.get("failure_reason"), 100)
    kind = "info" if verdict == "mini_recursive_yielded" else ("good" if rec.get("ok") is True else "warn")
    _emit(state, rec, kind, f"recursive attempt: {verdict} ({state.recursive_status_detail or 'no failure reason'}); the run process may still be alive", milestone=True)


def _deferral_key(rec: dict[str, Any]) -> tuple[str, str]:
    return (_str(rec.get("session_activation_id"), 64), _str(rec.get("action_id"), 80))


def _on_deferral(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    key = _deferral_key(rec)
    if verdict in _RELEASE_VERDICTS:
        _bump(state, "releases")
        if key in state.deferred:
            del state.deferred[key]
            _emit(state, rec, "info", f"deferral released for {key[1]} ({verdict.replace('_', ' ')})")
        else:
            state.releases_unmatched += 1
            _emit(state, rec, "info", f"release without a matching deferral for {key[1]} (kept as history)")
        return
    if "deferred" in verdict:
        _bump(state, "deferrals")
        reason = _str(rec.get("llm_failure_kind") or rec.get("scoped_failure_reason") or rec.get("reason"), 80)
        if key in state.deferred or len(state.deferred) < MAX_DEFERRED:
            state.deferred[key] = {"reason": reason, "elapsed_s": elapsed, "scope": _scope_tag(rec), "verdict": verdict}
        else:
            state.deferred_overflow += 1
        _emit(state, rec, "warn", f"{key[1]} deferred in {_scope_tag(rec)} scope: {reason or verdict}")


def _on_no_applicable(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    if verdict == "terminal_no_applicable_action":
        _emit(state, rec, "warn", f"no applicable action in {_scope_tag(rec)} scope: {_str(rec.get('reason'), 80)} (terminal for this scope only)", milestone=True)


def _on_repair_ticket(state: RunState, rec: dict[str, Any]) -> None:
    if _str(rec.get("verdict"), 40) == "created":
        _bump(state, "repair_tickets")
        _emit(state, rec, "info", f"repair ticket for {_str(rec.get('target_id'), 60)}: {_str(rec.get('error_type'), 60)} ({_str(rec.get('work_type'), 40)})")


def _on_lean_phase(state: RunState, rec: dict[str, Any], phase: str) -> None:
    verdict = _str(rec.get("verdict"), 80)
    elapsed = _num(rec.get("elapsed_s")) or 0.0
    _touch(state, "lean", elapsed, f"{phase}: {verdict}")
    _bump(state, "lean_tactic_rows")
    successes = _int(rec.get("tactic_success_count"))
    if successes:
        _emit(state, rec, "good", f"{phase}: {successes} tactic candidate(s) closed a goal ({verdict})")
    elif phase in {"proof_state_root_assembly", "mini_recursive_llm_root_close", "mini_recursive_root_tactic"} and ("rejected" in verdict or "exhausted" in verdict):
        _emit(state, rec, "info", f"{phase}: {verdict.replace('_', ' ')}")


def _on_promotion_receipt(state: RunState, rec: dict[str, Any]) -> None:
    if _str(rec.get("verdict"), 60) == "helper_promotion_staged":
        _bump(state, "promotions_staged")
        _emit(state, rec, "info", f"helper staged for theory promotion: {_str(rec.get('helper_name'), 120)}")


def _on_governor(state: RunState, rec: dict[str, Any]) -> None:
    verdict = _str(rec.get("verdict"), 80)
    if verdict == "strong_progress_window_reset":
        state.strong_progress_last_elapsed_s = _num(rec.get("elapsed_s")) or 0.0
        state.strong_progress_last_reason = _str(rec.get("strong_progress_reason"), 60)
        _emit(state, rec, "info", f"strong progress recorded: {state.strong_progress_last_reason}")
    else:
        _emit(state, rec, "warn", f"run governor: {verdict}")


_HANDLERS = {
    "run_config": _on_run_config,
    "answer_visibility": _on_answer_visibility,
    "session_pre_select_snapshot": _on_snapshot,
    "session_iteration": _on_iteration,
    "session_action_outcome": _on_outcome,
    "llm_usage": _on_llm_usage,
    "mini_recursive_plan": _on_plan,
    "session_planner_job": _on_planner_job,
    "mini_recursive_claim_typecheck": _on_claim_typecheck,
    "mini_recursive_claim_llm": _on_claim_llm,
    "mini_recursive_claim_deadline": _on_claim_deadline,
    "mini_recursive_helper_accept": _on_helper_accept,
    "session_accepted_proof": _on_accepted_proof,
    "session_root_finalization": _on_root_finalization,
    "session_root_solved": _on_root_solved,
    "mini_recursive_complete": _on_recursive_complete,
    "session_model_call_deferred_frontier_action": _on_deferral,
    "session_model_call_deferred_static_action": _on_deferral,
    "session_no_applicable_recovery": _on_no_applicable,
    "session_repair_ticket": _on_repair_ticket,
    "domain_theory_promotion_receipt": _on_promotion_receipt,
    "session_run_governor": _on_governor,
}


def reduce(state: RunState, rec: Any) -> RunState:
    """Apply one trace row. Never raises on malformed rows; counts them."""
    if not isinstance(rec, dict):
        state.invalid_rows += 1
        return state
    state.live_math.consume(rec)
    state.rows += 1
    elapsed = _num(rec.get("elapsed_s"))
    if elapsed is not None:
        state.last_elapsed_s = max(state.last_elapsed_s, elapsed)
    turn_index = _int(rec.get("turn_index"))
    if turn_index is not None:
        if state.first_turn_index is None:
            state.first_turn_index = turn_index
        state.last_turn_index = turn_index
    phase = _str(rec.get("phase"), 80)
    if phase in state.phases or len(state.phases) < MAX_PHASES:
        state.phases[phase] = state.phases.get(phase, 0) + 1
    else:
        state.phases_overflow += 1
    if phase == "session_action_selected":
        _bump(state, "selections")
        return state
    if phase in ("prove", "refine"):
        _on_conversation(state, rec, phase)
        return state
    if phase in _LEAN_PHASES:
        _on_lean_phase(state, rec, phase)
        return state
    handler = _HANDLERS.get(phase)
    if handler is not None:
        handler(state, rec)
    else:
        _bump(state, "unhandled_rows")
    return state


def reduce_all(state: RunState, records: list[Any]) -> RunState:
    for rec in records:
        reduce(state, rec)
    return state
