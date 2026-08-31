"""Activation telemetry artifacts for mini-prover runs.

The mini prover already emits detailed ``turns.jsonl`` records.  This module
condenses those records into a stable per-run activation artifact so we can
ask direct questions such as "did the LLM root-close lane ever fire?" without
hand-building forensic scripts for each investigation.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import time
import uuid
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple


ACTIVATION_SCHEMA_VERSION = 1
ACTIVATION_CLASSIFIER_VERSION = 13
ACTIVATION_ARTIFACT_NAME = "activation_telemetry.json"


def _reject_nonfinite_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _validate_finite_json_numbers(value: Any) -> None:
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("non-finite JSON number")
        return
    if isinstance(value, Mapping):
        for item in value.values():
            _validate_finite_json_numbers(item)
        return
    if isinstance(value, (list, tuple)):
        for item in value:
            _validate_finite_json_numbers(item)


def _strict_json_loads(value: str | bytes) -> Any:
    parsed = json.loads(value, parse_constant=_reject_nonfinite_json_constant)
    _validate_finite_json_numbers(parsed)
    return parsed


def _finite_json_value(value: Any) -> Any:
    if isinstance(value, float) and not math.isfinite(value):
        return None
    if isinstance(value, Mapping):
        return {str(key): _finite_json_value(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_finite_json_value(item) for item in value]
    return value


def _json_values_identical(left: Any, right: Any) -> bool:
    """Compare JSON values without Python's bool/int equality coercion."""

    try:
        return json.dumps(
            left,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ) == json.dumps(
            right,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError, OverflowError):
        return False


ACTIVATION_LANES: Dict[str, Dict[str, str]] = {
    "root_close.mini_recursive_tactic": {
        "category": "root_close",
        "description": "Mechanical mini-recursive root tactic close attempted.",
    },
    "root_close.llm_attempt": {
        "category": "root_close",
        "description": "LLM root-close attempt started or completed.",
    },
    "root_close.llm_skip": {
        "category": "root_close_skip",
        "description": "LLM root-close candidate was present but skipped by a gate.",
    },
    "root_close.root_exact_helper": {
        "category": "root_close",
        "description": "Root-equivalent helper exact-close lane attempted.",
    },
    "root_close.proof_state_root_assembly": {
        "category": "root_close",
        "description": "Proof-state root assembly tactic attempted.",
    },
    "root_close.graph_route_assembly_tactic": {
        "category": "root_close",
        "description": "Graph route assembly root tactic attempted.",
    },
    "root_close.salvage_root_tactic": {
        "category": "root_close",
        "description": "Helper-salvage root tactic attempted.",
    },
    "finalization.root_solution": {
        "category": "finalization",
        "description": "Root finalization gate ran.",
    },
    "finalization.subgoal_solution": {
        "category": "finalization",
        "description": "A nested subgoal session finalization gate ran.",
    },
    "assembly.graph_route_selected": {
        "category": "assembly",
        "description": "Scheduler selected graph_route_assembly.",
    },
    "assembly.inter_turn_selected": {
        "category": "assembly",
        "description": "Scheduler selected inter_turn_assembly.",
    },
    "assembly.graph_route_execution": {
        "category": "assembly",
        "description": "Graph route assembly execution emitted telemetry.",
    },
    "assembly.proof_state_parent": {
        "category": "assembly",
        "description": "Proof-state parent assembly ran.",
    },
    "assembly.proof_state_root": {
        "category": "assembly",
        "description": "Proof-state root assembly ran.",
    },
    "assembly.static_fallback": {
        "category": "assembly",
        "description": "Static route-assembly fallback/suppression lane ran.",
    },
    "skeleton.try_tool": {
        "category": "skeleton",
        "description": "LLM try_skeleton route-constructor tool was invoked.",
    },
    "skeleton.route_banked": {
        "category": "skeleton",
        "description": "Lean-validated proof skeleton banked residual obligations.",
    },
    "compute.examples_tool": {
        "category": "compute",
        "description": "LLM compute_examples observation tool was invoked.",
    },
    "tool_protocol.malformed_arguments": {
        "category": "tool_protocol",
        "description": "A tool call was rejected before execution because its arguments were malformed.",
    },
    "cache.same_problem_seed": {
        "category": "cache",
        "description": "Same-problem verified-helper cache seeding ran.",
    },
    "cache.proof_state_lookup": {
        "category": "cache",
        "description": "Proof-state cache lookup examined a cached helper.",
    },
    "cache.proof_state_hit": {
        "category": "cache",
        "description": "Proof-state cache lookup accepted or reused a helper.",
    },
    "promotion.graph_obligation": {
        "category": "promotion",
        "description": "Trusted graph obligation was promoted or reused as proof-state work.",
    },
    "promotion.root_equivalent_helper": {
        "category": "promotion",
        "description": "Root-equivalent helper exact preflight promoted a helper to root proof.",
    },
    "salvage.helper_only": {
        "category": "salvage",
        "description": "Helper-only salvage lane ran.",
    },
    "salvage.post_failure": {
        "category": "salvage",
        "description": "Post-failure helper salvage lane ran.",
    },
    "salvage.proof_state_assembly": {
        "category": "salvage",
        "description": "Salvaged helpers were fed into proof-state assembly.",
    },
}


SUCCESS_VERDICTS = {
    "cache_seed_imported",
    "graph_obligation_promotion_applied",
    "helpers_accepted",
    "lemma_dag_helpers_accepted",
    "llm_root_close_solved",
    "root_finalization_accepted",
    "root_finalization_already_applied",
    "solved",
    "solved_after_helper_only_salvage",
    "solved_after_helper_salvage",
    "tactic_solved",
}

NO_ATTEMPT_VERDICTS = {
    "root_tactic_context_already_attempted",
    "root_tactic_context_deferred",
    "tactic_skipped",
    "tactic_skipped_duplicate_context",
}


def _clean(value: Any) -> str:
    return str(value or "").strip()


def _as_int(value: Any) -> int:
    try:
        return int(value or 0)
    except (TypeError, ValueError, OverflowError):
        return 0


def _skeleton_tool_calls(record: Mapping[str, Any]) -> List[Mapping[str, Any]]:
    tool_call_log = record.get("tool_call_log")
    if not isinstance(tool_call_log, Sequence) or isinstance(tool_call_log, (str, bytes)):
        return []
    return [
        item
        for item in tool_call_log
        if isinstance(item, Mapping) and _clean(item.get("name")) == "try_skeleton"
    ]


def _skeleton_tool_call_count(record: Mapping[str, Any]) -> int:
    return max(
        _as_int(record.get("try_skeleton_tool_calls")),
        len(_skeleton_tool_calls(record)),
        _as_int(record.get("try_skeleton_routes_banked")),
    )


def _skeleton_route_banked_count(record: Mapping[str, Any]) -> int:
    explicit = _as_int(record.get("try_skeleton_routes_banked"))
    logged = sum(
        1
        for item in _skeleton_tool_calls(record)
        if _clean(item.get("proof_state_update_status")) == "spawned_remaining_goals"
    )
    return max(explicit, logged)


def _skeleton_tool_invoked(record: Mapping[str, Any]) -> bool:
    return _skeleton_tool_call_count(record) > 0


def _skeleton_route_banked(record: Mapping[str, Any]) -> bool:
    return _skeleton_route_banked_count(record) > 0


def _compute_tool_calls(record: Mapping[str, Any]) -> List[Mapping[str, Any]]:
    tool_call_log = record.get("tool_call_log")
    if not isinstance(tool_call_log, Sequence) or isinstance(tool_call_log, (str, bytes)):
        return []
    return [
        item
        for item in tool_call_log
        if isinstance(item, Mapping)
        and _clean(item.get("name")) == "compute_examples"
        and _compute_tool_result_executed(item)
    ]


def _tool_call_logs(record: Mapping[str, Any]) -> List[Mapping[str, Any]]:
    value = record.get("tool_call_log")
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return []
    return [item for item in value if isinstance(item, Mapping)]


def _compute_tool_result_executed(item: Mapping[str, Any]) -> bool:
    # A durable runner receipt is authoritative even when the enclosing turn
    # timed out or was cancelled after dispatch. ``skipped_reason`` remains a
    # legacy field on some such records and must not erase actual execution.
    execution_status = _clean(item.get("execution_status"))
    if bool(item.get("args_parse_error")) or execution_status in {
        "not_dispatched",
        "protocol_rejected",
    }:
        return False
    if execution_status in {
        "runner_completed",
        "runner_error",
        "runner_timeout",
        "runner_cancelled",
    }:
        return bool(item.get("runner_invoked", True))
    if "runner_invoked" in item:
        return bool(item.get("runner_invoked"))
    if _clean(item.get("skipped_reason")):
        return False
    preview = _clean(item.get("result_preview"))
    return preview.startswith(
        (
            "compute_examples accepted",
            "compute_examples rejected",
            "compute_examples error:",
            "compute_examples infrastructure error:",
        )
    )


def _compute_tool_call_count(record: Mapping[str, Any]) -> int:
    if isinstance(record.get("tool_call_log"), (list, tuple)):
        return len(_compute_tool_calls(record))
    return _as_int(record.get("compute_examples_tool_calls"))


def _compute_tool_success_count(record: Mapping[str, Any]) -> int:
    logged = sum(
        1
        for item in _compute_tool_calls(record)
        if (
            "execution_status" not in item
            or _clean(item.get("execution_status")) == "runner_completed"
        )
        if _clean(item.get("result_preview")).startswith("compute_examples accepted")
    )
    if isinstance(record.get("tool_call_log"), (list, tuple)):
        return min(_compute_tool_call_count(record), logged)
    return min(
        _compute_tool_call_count(record),
        _as_int(record.get("compute_examples_successes")),
    )


def _compute_tool_invoked(record: Mapping[str, Any]) -> bool:
    return _compute_tool_call_count(record) > 0


def _malformed_tool_call_count(record: Mapping[str, Any]) -> int:
    protocol_logs = _tool_call_logs(record)
    logged = sum(
        1
        for item in protocol_logs
        if (
            bool(item.get("args_parse_error"))
            or _clean(item.get("skipped_reason")) == "malformed_arguments"
        )
    )
    if isinstance(record.get("tool_call_log"), (list, tuple)):
        return logged
    return _as_int(record.get("malformed_tool_call_count"))


def _is_success(record: Mapping[str, Any]) -> bool:
    verdict = _clean(record.get("verdict"))
    if verdict in SUCCESS_VERDICTS:
        return True
    if bool(record.get("solved")):
        return True
    if bool(record.get("accepted")):
        return True
    if _as_int(record.get("accepted_count")) > 0:
        return True
    if _as_int(record.get("promoted_count")) > 0:
        return True
    if _as_int(record.get("reused_count")) > 0:
        return True
    if _clean(record.get("tactic_exit_reason")) == "root_equivalent_helper_promoted":
        return True
    return False


def _label_success(
    label: str,
    record: Mapping[str, Any],
    record_success: bool,
) -> bool:
    if label in {"skeleton.try_tool", "skeleton.route_banked"}:
        return _skeleton_route_banked(record)
    if label == "compute.examples_tool":
        return _compute_tool_success_count(record) > 0
    return record_success


def _activation_count(label: str, record: Mapping[str, Any]) -> int:
    if label == "skeleton.try_tool":
        return max(1, _skeleton_tool_call_count(record))
    if label == "skeleton.route_banked":
        return max(1, _skeleton_route_banked_count(record))
    if label == "compute.examples_tool":
        return max(1, _compute_tool_call_count(record))
    if label == "tool_protocol.malformed_arguments":
        return max(1, _malformed_tool_call_count(record))
    return 1


def _activation_success_count(
    label: str,
    record: Mapping[str, Any],
    record_success: bool,
) -> int:
    if label in {"skeleton.try_tool", "skeleton.route_banked"}:
        return _skeleton_route_banked_count(record)
    if label == "compute.examples_tool":
        return _compute_tool_success_count(record)
    if label == "tool_protocol.malformed_arguments":
        return 0
    if label == "promotion.graph_obligation":
        return 1 if (
            _as_int(record.get("promoted_count"))
            + _as_int(record.get("reused_count"))
        ) > 0 else 0
    return 1 if _label_success(label, record, record_success) else 0


def _stable_list(value: Any) -> Tuple[str, ...]:
    if isinstance(value, (list, tuple, set)):
        return tuple(
            sorted(str(item or "").strip() for item in value if str(item or "").strip())
        )
    text = str(value or "").strip()
    return (text,) if text else ()


def _legacy_receipt_key(value: Mapping[str, Any]) -> str:
    """Stable content identity for receipts predating explicit call ids."""

    try:
        return json.dumps(
            dict(value),
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
            default=str,
        )
    except (TypeError, ValueError, OverflowError, RecursionError):
        return repr(sorted((str(key), repr(item)) for key, item in value.items()))


def _activation_key(
    label: str,
    record: Mapping[str, Any],
    event_index: int,
) -> Tuple[Any, ...]:
    """Identity for one lane activation.

    Some subsystems emit a lifecycle record pair such as ``started`` plus a
    terminal verdict.  Counts should answer "how many attempts/actions ran",
    while verdict buckets may still retain every record seen for that
    activation.
    """

    phase = _clean(record.get("phase"))
    action_id = _clean(record.get("action_id"))
    if label == "root_close.llm_attempt":
        return (
            label,
            _clean(record.get("recursive_attempt_activation_id")),
            _clean(record.get("session_scope")),
            _clean(record.get("action_dispatch_id")),
            _clean(record.get("conv_turn_absolute")),
            phase,
            _clean(record.get("root_close_mode")),
            _clean(record.get("pass_index")),
            _clean(record.get("after_helper")),
            _stable_list(record.get("certificate_names")),
            _stable_list(record.get("assembly_helper_names")),
            _clean(record.get("assembly_reason")),
        )
    if label == "compute.examples_tool" and record.get("tool_call_log"):
        tool_call_ids = tuple(
            _clean(item.get("tool_call_id"))
            for item in _compute_tool_calls(record)
            if _clean(item.get("tool_call_id"))
        )
        receipt_key = (
            label,
            "canonical_tool_log",
            _clean(record.get("session_activation_id")),
            _clean(record.get("session_scope")),
            _clean(record.get("action_dispatch_id")),
            _clean(record.get("conv_turn_absolute")),
            tool_call_ids,
            tuple(
                _clean(item.get("raw_arguments_sha256"))
                for item in _compute_tool_calls(record)
            ),
        )
        if tool_call_ids:
            return receipt_key
        if any(receipt_key[-1]):
            return receipt_key + (
                _clean(record.get("turn_index")),
                _clean(record.get("turn_in_phase")),
            )
        return receipt_key + (
            tuple(_legacy_receipt_key(item) for item in _compute_tool_calls(record)),
        )
    if label == "tool_protocol.malformed_arguments" and record.get("tool_call_log"):
        malformed_calls = [
            item
            for item in _tool_call_logs(record)
            if bool(item.get("args_parse_error"))
            or _clean(item.get("skipped_reason")) == "malformed_arguments"
        ]
        tool_call_ids = tuple(
            _clean(item.get("tool_call_id")) for item in malformed_calls
        )
        receipt_key = (
            label,
            "canonical_tool_log",
            _clean(record.get("session_activation_id")),
            _clean(record.get("session_scope")),
            _clean(record.get("action_dispatch_id")),
            _clean(record.get("conv_turn_absolute")),
            tool_call_ids,
            tuple(
                _clean(item.get("raw_arguments_sha256"))
                for item in malformed_calls
            ),
        )
        if any(tool_call_ids):
            return receipt_key
        if any(receipt_key[-1]):
            return receipt_key + (
                _clean(record.get("turn_index")),
                _clean(record.get("turn_in_phase")),
            )
        return receipt_key + (
            tuple(_legacy_receipt_key(item) for item in malformed_calls),
        )
    if label in {"skeleton.try_tool", "skeleton.route_banked", "compute.examples_tool"}:
        turn_key = (
            _clean(record.get("conv_turn_absolute"))
            or _clean(record.get("turn_in_phase"))
            or _clean(record.get("turn_index"))
            or event_index
        )
        return (
            label,
            _clean(record.get("session_scope")),
            _clean(record.get("action_dispatch_id")),
            turn_key,
        )
    if label in {"assembly.graph_route_selected", "assembly.inter_turn_selected"}:
        selected = record.get("selected_work_item")
        selected_key = ""
        if isinstance(selected, Mapping):
            selected_key = json.dumps(selected, sort_keys=True, default=str)
        return (
            label,
            action_id,
            _clean(record.get("iteration")),
            selected_key,
            _clean(record.get("turn_index")) or event_index,
        )
    if label in {"assembly.graph_route_execution", "salvage.helper_only"}:
        selected = record.get("selected_work_item")
        selected_key = ""
        if isinstance(selected, Mapping):
            selected_key = json.dumps(selected, sort_keys=True, default=str)
        return (
            label,
            action_id,
            _clean(record.get("iteration")),
            selected_key,
            _clean(record.get("turn_index")) or event_index,
        )
    return (label, _clean(record.get("turn_index")) or event_index)


def _tactic_attempt_record(record: Mapping[str, Any]) -> bool:
    verdict = _clean(record.get("verdict"))
    if verdict in NO_ATTEMPT_VERDICTS:
        return False
    if _clean(record.get("skip_reason")):
        return False
    attempts = record.get("tactic_attempts")
    attempts_empty = isinstance(attempts, (list, tuple)) and len(attempts) == 0
    if attempts_empty:
        return False
    attempts_absent_or_empty = "tactic_attempts" not in record or attempts_empty
    if (
        "tactic_attempt_count" in record
        and _as_int(record.get("tactic_attempt_count")) <= 0
    ):
        return False
    if (
        "tactic_candidate_count" in record
        and _as_int(record.get("tactic_candidate_count")) <= 0
        and attempts_absent_or_empty
    ):
        return False
    return True


def _event_labels(record: Mapping[str, Any]) -> List[str]:
    phase = _clean(record.get("phase"))
    verdict = _clean(record.get("verdict"))
    action_id = _clean(record.get("action_id"))
    labels: List[str] = []

    if phase == "mini_recursive_root_tactic" and _tactic_attempt_record(record):
        labels.append("root_close.mini_recursive_tactic")
    if phase == "mini_recursive_llm_root_close":
        if verdict == "llm_root_close_skipped":
            labels.append("root_close.llm_skip")
        else:
            labels.append("root_close.llm_attempt")
    if phase == "proof_state_root_exact_helper":
        labels.append("root_close.root_exact_helper")
    if phase == "proof_state_root_assembly":
        labels.append("assembly.proof_state_root")
        if _tactic_attempt_record(record):
            labels.append("root_close.proof_state_root_assembly")
    if phase == "graph_route_assembly_root_tactic" and _tactic_attempt_record(record):
        labels.append("root_close.graph_route_assembly_tactic")
    if (
        phase in {"helper_salvage_root_tactic", "helper_only_salvage_root_tactic"}
        and _tactic_attempt_record(record)
    ):
        labels.append("root_close.salvage_root_tactic")
    if phase == "session_root_finalization":
        scope = _clean(record.get("session_scope"))
        labels.append(
            "finalization.subgoal_solution"
            if scope and scope not in {"problem", "direct_root_author"}
            else "finalization.root_solution"
        )

    if phase == "session_action_selected" and action_id == "graph_route_assembly":
        labels.append("assembly.graph_route_selected")
    if phase == "session_action_selected" and action_id == "inter_turn_assembly":
        labels.append("assembly.inter_turn_selected")
    if phase == "session_action_outcome" and action_id == "graph_route_assembly":
        labels.append("assembly.graph_route_execution")
    if phase == "proof_state_parent_assembly":
        labels.append("assembly.proof_state_parent")
    if phase == "session_assemble_route_static_fallback":
        labels.append("assembly.static_fallback")
    if _skeleton_tool_invoked(record):
        labels.append("skeleton.try_tool")
    if _skeleton_route_banked(record):
        labels.append("skeleton.route_banked")
    session_scoped = bool(_clean(record.get("session_scope")))
    canonical_tool_record = bool(_tool_call_logs(record)) and (
        verdict in {
            "llm_response",
            "llm_response_cancelled",
            "llm_call_failed",
        }
        or (not session_scoped and phase != "session_action_outcome")
    )
    if _compute_tool_invoked(record) and (
        canonical_tool_record
        or (
            not record.get("tool_call_log")
            and phase != "session_action_outcome"
        )
    ):
        labels.append("compute.examples_tool")
    if _malformed_tool_call_count(record) > 0 and canonical_tool_record:
        labels.append("tool_protocol.malformed_arguments")
    if phase == "proof_state_cache_seed":
        labels.append("cache.same_problem_seed")
    if phase == "proof_state_cache_lookup":
        labels.append("cache.proof_state_lookup")
        if bool(record.get("accepted")) or bool(record.get("reused_existing_helper")):
            labels.append("cache.proof_state_hit")
    if phase == "proof_state_cache_hit":
        labels.append("cache.proof_state_hit")

    if phase == "graph_obligation_promotion":
        labels.append("promotion.graph_obligation")
    if _clean(record.get("tactic_exit_reason")) == "root_equivalent_helper_promoted":
        labels.append("promotion.root_equivalent_helper")

    if phase == "helper_only_salvage":
        labels.append("salvage.helper_only")
    if phase.endswith(":helper_salvage") or phase == "helper_salvage":
        labels.append("salvage.post_failure")
    if phase in {
        "helper_salvage_proof_state_assembly",
        "helper_only_salvage_proof_state_assembly",
    }:
        labels.append("salvage.proof_state_assembly")

    out: List[str] = []
    seen = set()
    for label in labels:
        if label in ACTIVATION_LANES and label not in seen:
            seen.add(label)
            out.append(label)
    return out


def _example(record: Mapping[str, Any]) -> Dict[str, Any]:
    keys = (
        "turn_index",
        "elapsed_s",
        "phase",
        "verdict",
        "action_id",
        "root_close_mode",
        "skip_reason",
        "candidate_count",
        "accepted_count",
        "promoted_count",
        "reused_count",
        "helper_name",
        "cached_helper",
        "tactic_exit_reason",
        "try_skeleton_tool_calls",
        "try_skeleton_routes_banked",
        "compute_examples_tool_calls",
        "compute_examples_successes",
        "compute_examples_protocol_attempts",
        "compute_examples_malformed_calls",
        "session_scope",
    )
    return {
        key: _finite_json_value(record.get(key))
        for key in keys
        if key in record
    }


def build_activation_telemetry(
    events: Sequence[Mapping[str, Any]],
    *,
    summary: Optional[Mapping[str, Any]] = None,
    run_dir: str | Path | None = None,
    generated_at: Optional[float] = None,
) -> Dict[str, Any]:
    """Build a stable activation summary from ``turns.jsonl`` records."""

    lane_records: Dict[str, Dict[str, Any]] = {
        lane: {
            "category": meta["category"],
            "description": meta["description"],
            "count": 0,
            "success_count": 0,
            "first_turn": None,
            "last_turn": None,
            "verdicts": {},
            "examples": [],
        }
        for lane, meta in ACTIVATION_LANES.items()
    }
    category_counts: Counter[str] = Counter()
    event_count = 0
    malformed_count = 0
    malformed_tool_call_count = 0
    seen_activation_keys: Dict[str, Dict[Tuple[Any, ...], int]] = defaultdict(dict)
    successful_activation_keys: Dict[str, Dict[Tuple[Any, ...], int]] = defaultdict(dict)
    for event_index, record in enumerate(events):
        if not isinstance(record, Mapping):
            malformed_count += 1
            continue
        event_count += 1
        try:
            labels = _event_labels(record)
        except (TypeError, ValueError, OverflowError, RecursionError):
            malformed_count += 1
            continue
        if not labels:
            continue
        turn = record.get("turn_index")
        record_success = _is_success(record)
        verdict = _clean(record.get("verdict")) or "(none)"
        for label in labels:
            entry = lane_records[label]
            activation_key = _activation_key(label, record, event_index)
            activation_count = max(0, _activation_count(label, record))
            prior_count = int(seen_activation_keys[label].get(activation_key, 0) or 0)
            count_delta = max(0, activation_count - prior_count)
            new_activation = prior_count <= 0 and activation_count > 0
            if count_delta > 0:
                seen_activation_keys[label][activation_key] = activation_count
                entry["count"] = int(entry["count"]) + count_delta
                category_counts[str(entry["category"])] += count_delta
                if label == "tool_protocol.malformed_arguments":
                    malformed_tool_call_count += count_delta
            success_count = max(
                0,
                _activation_success_count(label, record, record_success),
            )
            prior_success_count = int(
                successful_activation_keys[label].get(activation_key, 0) or 0
            )
            success_delta = max(0, success_count - prior_success_count)
            if success_delta > 0:
                successful_activation_keys[label][activation_key] = success_count
                entry["success_count"] = int(entry["success_count"]) + success_delta
            if new_activation and entry["first_turn"] is None:
                entry["first_turn"] = turn
            entry["last_turn"] = turn
            verdicts = dict(entry.get("verdicts") or {})
            verdicts[verdict] = int(verdicts.get(verdict, 0) or 0) + 1
            entry["verdicts"] = verdicts
            examples = list(entry.get("examples") or [])
            if len(examples) < 3:
                examples.append(_example(record))
                entry["examples"] = examples

    summary = dict(summary or {})
    active_lanes = [
        lane for lane, entry in lane_records.items() if int(entry["count"]) > 0
    ]
    zero_lanes = [
        lane for lane, entry in lane_records.items() if int(entry["count"]) <= 0
    ]
    return {
        "activation_schema_version": ACTIVATION_SCHEMA_VERSION,
        "activation_classifier_version": ACTIVATION_CLASSIFIER_VERSION,
        "generated_ts": generated_at if generated_at is not None else time.time(),
        "run_dir": str(run_dir or ""),
        "problem": _clean(summary.get("problem")),
        "theorem_name": _clean(summary.get("theorem_name") or summary.get("problem")),
        "solved": bool(summary.get("solved", False)),
        "event_count": event_count,
        "malformed_event_count": malformed_count,
        "malformed_tool_call_count": malformed_tool_call_count,
        "active_lane_count": len(active_lanes),
        "zero_lane_count": len(zero_lanes),
        "categories": dict(sorted(category_counts.items())),
        "active_lanes": active_lanes,
        "zero_activation_lanes": zero_lanes,
        "lanes": lane_records,
    }


def load_jsonl_events(path: str | Path) -> Tuple[List[Dict[str, Any]], int]:
    """Load trace events, tolerating malformed live-tail rows."""

    trace_path = Path(path)
    events: List[Dict[str, Any]] = []
    malformed = 0
    if not trace_path.exists():
        return events, 0
    for line in trace_path.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            record = _strict_json_loads(line)
        except (
            json.JSONDecodeError,
            RecursionError,
            ValueError,
            OverflowError,
            TypeError,
        ):
            malformed += 1
            continue
        if isinstance(record, dict):
            events.append(record)
        else:
            malformed += 1
    return events, malformed


def _read_json_with_validity(path: Path) -> Tuple[Dict[str, Any], bool]:
    try:
        value = _strict_json_loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}, False
    return (value, True) if isinstance(value, dict) else ({}, False)


def _read_json(path: Path) -> Dict[str, Any]:
    return _read_json_with_validity(path)[0]


def _file_fingerprint(path: Path, prefix: str) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        before = path.stat()
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        after = path.stat()
    except OSError:
        return {}
    if (
        before.st_ino,
        before.st_mtime_ns,
        before.st_size,
    ) != (
        after.st_ino,
        after.st_mtime_ns,
        after.st_size,
    ):
        return {}
    return {
        f"source_{prefix}_mtime_ns": int(after.st_mtime_ns),
        f"source_{prefix}_size_bytes": int(after.st_size),
        f"source_{prefix}_sha256": digest.hexdigest(),
    }


def _turns_fingerprint(path: Path) -> Dict[str, Any]:
    return _file_fingerprint(path, "turns")


def _summary_fingerprint(path: Path) -> Dict[str, Any]:
    return _file_fingerprint(path, "summary")


def _fingerprints_match(
    before: Mapping[str, Any],
    after: Mapping[str, Any],
) -> bool:
    return dict(before) == dict(after)


def _valid_activation_artifact(
    value: Mapping[str, Any],
    *,
    turns_path: Optional[Path] = None,
    summary_path: Optional[Path] = None,
) -> bool:
    if bool(
        value.get("activation_counts_are_lower_bound")
        or value.get("watchdog_recovery_scan_truncated")
    ):
        return False
    if _as_int(value.get("activation_schema_version")) != ACTIVATION_SCHEMA_VERSION:
        return False
    if (
        _as_int(value.get("activation_classifier_version"))
        != ACTIVATION_CLASSIFIER_VERSION
    ):
        return False
    if turns_path is not None:
        if not turns_path.exists():
            return False
        fingerprint = _turns_fingerprint(turns_path)
        if not fingerprint:
            return False
        if (
            _as_int(value.get("source_turns_mtime_ns"))
            != fingerprint["source_turns_mtime_ns"]
        ):
            return False
        if (
            _as_int(value.get("source_turns_size_bytes"))
                != fingerprint["source_turns_size_bytes"]
        ):
            return False
        if str(value.get("source_turns_sha256") or "") != str(
            fingerprint["source_turns_sha256"]
        ):
            return False
    if summary_path is not None:
        artifact_has_summary_fingerprint = (
            "source_summary_mtime_ns" in value
            or "source_summary_size_bytes" in value
            or "source_summary_sha256" in value
        )
        if summary_path.exists():
            fingerprint = _summary_fingerprint(summary_path)
            if not fingerprint:
                return False
            if (
                _as_int(value.get("source_summary_mtime_ns"))
                != fingerprint["source_summary_mtime_ns"]
            ):
                return False
            if (
                _as_int(value.get("source_summary_size_bytes"))
                != fingerprint["source_summary_size_bytes"]
            ):
                return False
            if str(value.get("source_summary_sha256") or "") != str(
                fingerprint["source_summary_sha256"]
            ):
                return False
        elif artifact_has_summary_fingerprint:
            return False
    lanes = value.get("lanes")
    if not isinstance(lanes, Mapping):
        return False
    for lane in ACTIVATION_LANES:
        meta = lanes.get(lane)
        if not isinstance(meta, Mapping):
            return False
        if "count" not in meta or "success_count" not in meta:
            return False
    if not isinstance(value.get("active_lanes"), list):
        return False
    if not isinstance(value.get("zero_activation_lanes"), list):
        return False
    return True


def build_activation_telemetry_for_run(
    run_dir: str | Path,
    *,
    summary: Optional[Mapping[str, Any]] = None,
    summary_source_path: str | Path | None = None,
) -> Dict[str, Any]:
    run_path = Path(run_dir)
    turns_path = run_path / "turns.jsonl"
    summary_path = (
        Path(summary_source_path)
        if summary_source_path is not None
        else run_path / "summary.json"
    )
    summary_override = dict(summary) if summary is not None else None
    for _attempt in range(3):
        turns_before = _turns_fingerprint(turns_path)
        summary_before = _summary_fingerprint(summary_path)
        events, malformed = load_jsonl_events(turns_path)
        disk_summary, disk_summary_valid = _read_json_with_validity(summary_path)
        summary_record = (
            dict(summary_override)
            if summary_override is not None
            else disk_summary
        )
        _validate_finite_json_numbers(summary_record)
        telemetry = build_activation_telemetry(
            events,
            summary=summary_record,
            run_dir=run_path,
        )
        if malformed:
            telemetry["malformed_event_count"] = (
                int(telemetry.get("malformed_event_count", 0) or 0) + malformed
            )
        turns_after = _turns_fingerprint(turns_path)
        summary_after = _summary_fingerprint(summary_path)
        if not _fingerprints_match(turns_before, turns_after):
            continue
        if not _fingerprints_match(summary_before, summary_after):
            continue
        telemetry.update(turns_before)
        if disk_summary_valid and (
            summary_override is None
            or _json_values_identical(disk_summary, summary_override)
        ):
            telemetry.update(summary_before)
        return telemetry
    raise RuntimeError("activation telemetry sources changed during classification")


def write_activation_telemetry_for_run(
    run_dir: str | Path,
    *,
    summary: Optional[Mapping[str, Any]] = None,
    summary_source_path: str | Path | None = None,
) -> Dict[str, Any]:
    run_path = Path(run_dir)
    telemetry = build_activation_telemetry_for_run(
        run_path,
        summary=summary,
        summary_source_path=summary_source_path,
    )
    summary_path = (
        Path(summary_source_path)
        if summary_source_path is not None
        else run_path / "summary.json"
    )
    if summary is not None and (
        not summary_path.exists() or "source_summary_sha256" not in telemetry
    ):
        raise RuntimeError(
            "activation telemetry summary override does not match summary.json"
        )
    destination = run_path / ACTIVATION_ARTIFACT_NAME
    temporary = run_path / f".{ACTIVATION_ARTIFACT_NAME}.{uuid.uuid4().hex}.tmp"
    temporary.write_text(
        json.dumps(
            telemetry,
            indent=2,
            ensure_ascii=False,
            sort_keys=True,
            allow_nan=False,
        ),
        encoding="utf-8",
    )
    os.replace(temporary, destination)
    return telemetry


def compact_activation_summary(telemetry: Mapping[str, Any]) -> Dict[str, Any]:
    lanes = telemetry.get("lanes")
    active_counts: Dict[str, int] = {}
    if isinstance(lanes, Mapping):
        for lane, raw in lanes.items():
            if not isinstance(raw, Mapping):
                continue
            count = _as_int(raw.get("count"))
            if count > 0:
                active_counts[str(lane)] = count
    return {
        "activation_schema_version": ACTIVATION_SCHEMA_VERSION,
        "activation_classifier_version": _as_int(
            telemetry.get("activation_classifier_version")
        ),
        "active_lane_count": _as_int(telemetry.get("active_lane_count")),
        "zero_lane_count": _as_int(telemetry.get("zero_lane_count")),
        "active_lanes": list(telemetry.get("active_lanes") or ()),
        "zero_activation_lanes": list(telemetry.get("zero_activation_lanes") or ()),
        "categories": dict(telemetry.get("categories") or {}),
        "lane_counts": dict(sorted(active_counts.items())),
        "watchdog_bounded_recovery": bool(
            telemetry.get("watchdog_bounded_recovery")
        ),
        "watchdog_recovery_scan_truncated": bool(
            telemetry.get("watchdog_recovery_scan_truncated")
        ),
        "activation_counts_are_lower_bound": bool(
            telemetry.get("activation_counts_are_lower_bound")
        ),
    }


def _run_dirs(root: str | Path) -> List[Path]:
    root_path = Path(root)
    if not root_path.exists():
        return []
    if (root_path / "turns.jsonl").exists():
        return [root_path]
    dirs = [
        path
        for path in root_path.iterdir()
        if path.is_dir() and (path / "turns.jsonl").exists()
    ]
    return sorted(dirs, key=lambda path: (path.stat().st_mtime, path.name))


def load_or_build_activation_telemetry(run_dir: str | Path) -> Dict[str, Any]:
    run_path = Path(run_dir)
    artifact = run_path / ACTIVATION_ARTIFACT_NAME
    turns = run_path / "turns.jsonl"
    summary = run_path / "summary.json"
    if artifact.exists():
        loaded = _read_json(artifact)
        source_mtimes = [
            path.stat().st_mtime_ns
            for path in (turns, summary)
            if path.exists()
        ]
        artifact_current = (
            not source_mtimes
            or artifact.stat().st_mtime_ns >= max(source_mtimes)
        )
        if (
            loaded
            and _valid_activation_artifact(
                loaded,
                turns_path=turns,
                summary_path=summary,
            )
            and artifact_current
        ):
            return loaded
    return build_activation_telemetry_for_run(run_path)


def sweep_activation_telemetry(
    roots: Sequence[str | Path],
    *,
    limit: int = 50,
) -> Dict[str, Any]:
    """Aggregate activation artifacts and flag zero-activation lanes."""

    all_dirs: List[Path] = []
    for root in roots:
        all_dirs.extend(_run_dirs(root))
    deduped: Dict[str, Path] = {str(path.resolve()): path for path in all_dirs}
    ordered = sorted(
        deduped.values(),
        key=lambda path: (path.stat().st_mtime, path.name),
        reverse=True,
    )
    if int(limit or 0) > 0:
        ordered = ordered[: int(limit)]

    lane_counts: Counter[str] = Counter()
    lane_success_counts: Counter[str] = Counter()
    lane_runs: Dict[str, set[str]] = defaultdict(set)
    category_counts: Counter[str] = Counter()
    run_records: List[Dict[str, Any]] = []

    for run_path in ordered:
        try:
            telemetry = load_or_build_activation_telemetry(run_path)
        except (
            OSError,
            RuntimeError,
            TypeError,
            ValueError,
            OverflowError,
            RecursionError,
        ) as exc:
            run_records.append({
                "run_dir": str(run_path),
                "run_name": run_path.name,
                "active_lanes": [],
                "zero_activation_lanes": list(ACTIVATION_LANES),
                "solved": False,
                "telemetry_error": f"{type(exc).__name__}: {exc}"[:500],
            })
            continue
        run_name = run_path.name
        run_records.append(
            {
                "run_dir": str(run_path),
                "run_name": run_name,
                "active_lanes": list(telemetry.get("active_lanes") or ()),
                "zero_activation_lanes": list(
                    telemetry.get("zero_activation_lanes") or ()
                ),
                "solved": bool(telemetry.get("solved", False)),
            }
        )
        lanes = telemetry.get("lanes")
        if not isinstance(lanes, Mapping):
            continue
        for lane, meta in lanes.items():
            if lane not in ACTIVATION_LANES or not isinstance(meta, Mapping):
                continue
            count = _as_int(meta.get("count"))
            success_count = _as_int(meta.get("success_count"))
            lane_counts[lane] += count
            lane_success_counts[lane] += success_count
            if count > 0:
                lane_runs[lane].add(run_name)
                category_counts[ACTIVATION_LANES[lane]["category"]] += count

    lanes_out: Dict[str, Dict[str, Any]] = {}
    for lane, meta in ACTIVATION_LANES.items():
        lanes_out[lane] = {
            "category": meta["category"],
            "description": meta["description"],
            "count": int(lane_counts.get(lane, 0)),
            "success_count": int(lane_success_counts.get(lane, 0)),
            "runs_activated": len(lane_runs.get(lane, set())),
        }
    zero = [
        lane
        for lane, meta in lanes_out.items()
        if int(meta.get("count", 0) or 0) <= 0
    ]
    return {
        "activation_schema_version": ACTIVATION_SCHEMA_VERSION,
        "activation_classifier_version": ACTIVATION_CLASSIFIER_VERSION,
        "run_count": len(ordered),
        "limit": int(limit or 0),
        "roots": [str(root) for root in roots],
        "zero_activation_lanes": zero,
        "active_lane_count": len(ACTIVATION_LANES) - len(zero),
        "zero_lane_count": len(zero),
        "categories": dict(sorted(category_counts.items())),
        "lanes": lanes_out,
        "runs": run_records,
    }
