"""Bounded live mathematical and operational observations, never proof authority."""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

COSTLY_ACTION_SECONDS = 20.0
MAX_ROLES = 16


def text(value: Any, limit: int = 240) -> str:
    return value[:limit] if isinstance(value, str) else ""


def obj(value: Any) -> dict:
    return value if isinstance(value, dict) else {}


def number(value: Any) -> float | None:
    import math
    if type(value) not in (int, float):
        return None
    try:
        return float(value) if math.isfinite(value) and value >= 0 else None
    except (OverflowError, ValueError):
        return None


def source_record(value: Any) -> dict:
    row = obj(value)
    commit = text(row.get("git_commit"), 65)
    fingerprint = text(row.get("source_state_sha256"), 65)
    available = row.get("available") is True and bool(re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", commit))
    return {
        "available": available,
        "commit": commit if re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", commit) else "",
        "dirty": row.get("worktree_dirty") if available and type(row.get("worktree_dirty")) is bool else None,
        "fingerprint": fingerprint if re.fullmatch(r"[0-9a-f]{64}", fingerprint) else "",
        "partial": row.get("content_hash_truncated") is True,
    }


def _put(mapping: dict, key: str, value: Any) -> None:
    mapping.pop(key, None)
    mapping[key] = value
    while len(mapping) > MAX_ROLES:
        del mapping[next(iter(mapping))]


@dataclass
class LiveMathState:
    selection: dict = field(default_factory=dict)
    activity: dict = field(default_factory=dict)
    last_costly: dict = field(default_factory=dict)
    source: dict = field(default_factory=lambda: source_record(None))
    settings: dict = field(default_factory=dict)
    provider_issues: dict = field(default_factory=dict)
    prepared_requests: dict = field(default_factory=dict)
    startup_seen: bool = False

    def consume(self, row: dict) -> None:
        phase = row.get("phase")
        scope = text(row.get("session_scope"), 120) or "not recorded"
        elapsed = number(row.get("elapsed_s"))
        if phase == "run_config" and scope in {"problem", "not recorded"}:
            self.startup_seen = True
            self.source = source_record(row.get("run_source_provenance"))
            for role in ("prover", "refiner"):
                cfg = obj(row.get(f"{role}_reasoning"))
                if not cfg:
                    continue
                preflight = obj(cfg.get("reasoning_preflight"))
                _put(self.settings, role, {
                    "role": role, "provider": text(cfg.get("provider"), 60),
                    "model": text(cfg.get("model"), 160),
                    "reasoning": text(preflight.get("effective_effort"), 40),
                    "requestedReasoning": text(cfg.get("requested_effort"), 40),
                    "reasoningMode": text(cfg.get("requested_mode"), 40),
                    "transport": text(preflight.get("transport_mode"), 80),
                    "outputTokens": number(cfg.get("configured_max_output_tokens")),
                    "source": "startup", "elapsedS": elapsed, "workType": "",
                })
        if phase == "session_action_selected":
            focus = obj(row.get("mathematical_focus"))
            work = obj(row.get("selected_work_item"))
            # Old traces keep their selected target, but never invent a route
            # or reconstruct a ranking explanation from today's scheduler.
            selection = {
                "action": text(row.get("action_id"), 120),
                "dispatchId": text(row.get("action_dispatch_id"), 120),
                "scope": scope, "elapsedS": elapsed, "status": "selected",
                "approach": text(focus.get("approach")),
                "approachId": text(focus.get("approach_id"), 160),
                "obligationId": text(focus.get("obligation_id") or work.get("node_id"), 160),
                "statement": text(focus.get("statement") or work.get("target_statement"), 4096),
                "statementTruncated": focus.get("statement_truncated") is True or len(text(focus.get("statement") or work.get("target_statement"), 4097)) > 4096,
                "reason": text(focus.get("reason"), 800),
                "connection": text(focus.get("connection"), 80),
                "workType": text(focus.get("work_type") or work.get("work_type"), 80),
                "openRequirements": number(focus.get("open_requirements")),
            }
            self.activity = selection
            if scope == "problem" or not self.selection:
                self.selection = dict(selection)
        if phase == "session_action_outcome":
            dispatch = text(row.get("action_dispatch_id"), 120)
            for selection in (self.selection, self.activity):
                if dispatch and dispatch == selection.get("dispatchId") and scope == selection.get("scope"):
                    selection["status"] = "completed"
            duration = number(row.get("cost_seconds"))
            if duration is not None and duration >= COSTLY_ACTION_SECONDS:
                helpers = number(row.get("helpers_added_count"))
                if row.get("solved") is True:
                    result = ("Original theorem finalized in this session; export verification is separate."
                              if scope == "problem" else
                              "Session finalized with scope not recorded; original theorem completion is not established."
                              if scope == "not recorded" else
                              "Child obligation finalized; this does not establish the original theorem.")
                elif helpers:
                    result = f"Accepted {int(helpers)} helper(s); root contribution is not established by this receipt."
                elif row.get("strong_progress") is True:
                    result = ("The scheduler recorded progress in the original theorem session; no completed root proof is established by this receipt."
                              if scope == "problem" else
                              "The scheduler recorded progress with scope not recorded; original theorem contribution is unknown."
                              if scope == "not recorded" else
                              "The scheduler recorded progress on this child obligation; contribution to the original theorem is not established.")
                elif row.get("unverified_decomposition_created") is True:
                    result = "Proposed new obligations; they remain unproved."
                else:
                    result = "No checked mathematical result was recorded for this action."
                self.last_costly = {"action": text(row.get("action_id"), 120), "dispatchId": dispatch,
                    "scope": scope, "elapsedS": elapsed, "durationS": duration, "result": result,
                    "leanStatus": text(row.get("lean_verdict") or row.get("lean_error_type"), 80)}
        # Late accounting receipts may arrive after a newer call has started.
        # They remain in the trace but must not become the displayed settings.
        if row.get("late_usage") is True:
            return
        role = text(row.get("role"), 80) or "llm"
        request_id = text(row.get("llm_request_id"), 160)
        if phase == "llm_request_prepared" and request_id:
            _put(self.prepared_requests, role, request_id)
        current_request = self.prepared_requests.get(role)
        current = not current_request or not request_id or request_id == current_request
        receipts = row.get("mini_request_envelopes")
        if current and isinstance(receipts, list) and receipts:
            role = text(row.get("role"), 80) or "llm"
            # A pool's admission estimates describe several possible leaves.
            # Use a unique matching observed model, or explicitly unknown.
            choices = [value for value in receipts[:32] if isinstance(value, dict) and text(value.get("model"), 160)]
            observations = row.get("provider_observations")
            observed = [obj(value) for value in observations[:32]] if isinstance(observations, list) else []
            candidates = [value for value in choices if any(
                text(value.get("model"), 160) == text(receipt.get("model"), 160)
                and (not receipt.get("base_url") or text(value.get("base_url"), 2048) == text(receipt.get("base_url"), 2048))
                for receipt in observed)] if observed else choices
            complete_observations = not isinstance(observations, list) or len(observations) <= 32
            if len(candidates) == 1 and observed:
                candidate = candidates[0]
                complete_observations = complete_observations and all(
                    text(item.get("model"), 160) == text(candidate.get("model"), 160)
                    and (not item.get("base_url") or text(item.get("base_url"), 2048) == text(candidate.get("base_url"), 2048))
                    for item in observed
                )
            receipt = candidates[0] if len(candidates) == 1 and complete_observations and row.get("envelopes_truncated") is not True and len(receipts) <= 32 else {}
            _put(self.settings, role, {
                "role": role, "model": text(receipt.get("model"), 160), "provider": "",
                "reasoning": text(receipt.get("effective_reasoning_effort"), 40),
                "reasoningMode": "", "requestedReasoning": "",
                "transport": text(receipt.get("reasoning_transport_mode"), 80),
                "outputTokens": number(receipt.get("max_output_tokens")),
                "source": ("prepared" if phase == "llm_request_prepared" else "request") if receipt else "ambiguous", "elapsedS": elapsed,
                "scope": scope, "requestId": request_id,
                "workType": text(receipt.get("work_type"), 80),
            })
        if phase == "llm_usage":
            role = text(row.get("role"), 80) or "llm"
            status = text(row.get("status"), 80)
            if status in {"exception", "cancelled", "cancelled_provider_inflight", "retryable_exception_no_charge", "pre_dispatch_failure"}:
                _put(self.provider_issues, role, {"role": role, "status": status, "elapsedS": elapsed, "scope": scope, "requestId": request_id})
            elif status in {"ok", "success", "completed"} and (current or request_id == obj(self.provider_issues.get(role)).get("requestId")):
                self.provider_issues.pop(role, None)
