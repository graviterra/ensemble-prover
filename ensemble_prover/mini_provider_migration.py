"""Explicit transport handoffs preserve mathematical state and cumulative limits."""

from __future__ import annotations

from copy import copy, deepcopy
import hashlib
import json
from typing import Any


PROVIDER_OPTIONS = frozenset({
    "prover", "prover_model", "refiner", "refiner_model",
    "research_provider", "research_model", "research_review_provider", "research_review_model",
    "codex_bin", "claude_code_bin", "cursor_bin",
})


def migratable_provider_failure(reason: str) -> bool:
    from .llm_error_policy import is_provider_infrastructure_failure

    return is_provider_infrastructure_failure(reason) or reason in {
        "llm_required_prompt_context_overflow", "provider_capability_conflict",
    }


def record_needs_migration(record: dict[str, Any], migration: dict[str, Any]) -> bool:
    if not migration:
        return False
    from .mini_session.durable_session_record import _decode

    conversation = _decode(record["conversation"])
    return conversation.get("_provider_migration_epoch") != migration["epoch"]


def provider_transition(saved: dict[str, Any], current: dict[str, Any], *,
                        predecessor_generation: str = "") -> dict[str, Any]:
    """Validate a transport-only change independently of the CLI parser."""
    if saved.get("cli_schema_version") != 1 or current.get("cli_schema_version") != 1:
        raise ValueError("Provider migration requires a public CLI checkpoint identity")
    old, new = saved.get("cli_config"), current.get("cli_config")
    if type(old) is not dict or type(new) is not dict:
        raise ValueError("Provider migration requires exact saved transport policy")
    old_fixed = {key: value for key, value in old.items() if key not in PROVIDER_OPTIONS}
    new_fixed = {key: value for key, value in new.items() if key not in PROVIDER_OPTIONS}
    if old_fixed != new_fixed:
        raise ValueError("Provider migration configuration override is incompatible")
    if bool(old.get("refiner")) != bool(new.get("refiner")):
        raise ValueError("Provider migration cannot change the action inventory")
    for role, model in (("prover", "prover_model"), ("refiner", "refiner_model"),
                        ("research_provider", "research_model"),
                        ("research_review_provider", "research_review_model")):
        if "local" in (old.get(role), new.get(role)) and (
                old.get(role) != new.get(role) or old.get(model) != new.get(model)):
            raise ValueError("Provider migration cannot replace a bound local deployment")
    from .mini_research_roles import validate_research_role_config
    from argparse import Namespace

    validate_research_role_config(Namespace(**new))
    if new.get("inference_policy") == "local-only" and any(
        new.get(role) not in (None, "", "local") for role in ("prover", "refiner")
    ):
        raise ValueError("hosted_upstream_forbidden")
    changes = {key: {"from": old.get(key), "to": new.get(key)}
               for key in sorted(PROVIDER_OPTIONS) if old.get(key) != new.get(key)}
    if not changes:
        return {}
    # A later A→B handoff is a new event even when a dormant lane last used B.
    # Ordinary resumes retain the committed receipt instead of regenerating it.
    epoch = hashlib.sha256(json.dumps({"previous": saved, "changes": changes,
                                     "predecessor_generation": predecessor_generation},
                                     sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"epoch": epoch, "changes": changes}


def resolve_provider_migration_args(args: Any, saved: dict[str, Any]) -> Any:
    """Use ordinary resume validation for every option outside the handoff."""
    from .mini_checkpoint_cli import public_cli_config, resolve_resume_args

    explicit = args._explicit_cli_destinations
    requested = {key: getattr(args, key) for key in explicit & PROVIDER_OPTIONS}
    inherited = copy(args)
    for key in PROVIDER_OPTIONS:
        setattr(inherited, key, saved.get(key))
    inherited.resume_migrate_providers = False
    inherited._explicit_cli_destinations = explicit - PROVIDER_OPTIONS - {"resume_migrate_providers"}
    resolved = resolve_resume_args(inherited)
    for key, value in requested.items():
        setattr(resolved, key, value)
    for provider, option, default in (("codex", "codex_bin", "codex"),
                                      ("claude-code", "claude_code_bin", "claude"),
                                      ("cursor", "cursor_bin", "agent")):
        if getattr(resolved, option, None) is None:
            setattr(resolved, option, default)
    new = public_cli_config(resolved)
    provider_transition({"cli_schema_version": 1, "cli_config": saved},
                        {"cli_schema_version": 1, "cli_config": new})
    resolved.resume_migrate_providers = True
    resolved._explicit_cli_destinations = explicit
    return resolved


def migrate_session_provider_state(session: Any, migration: dict[str, Any]) -> None:
    """Remove old provider envelopes while retaining owned tool replay and spend.

    The destination continues the same target-bound local tool receipts. Every
    invocation, cumulative clock, pending verification and graph obligation stays
    with its existing owner. Only opaque transport continuations are discarded.
    """
    if not migration or getattr(session.conv, "_provider_migration_epoch", "") == migration["epoch"]:
        return
    from .mini_policy import _PROVIDER_CONTINUATION_STATE_KEYS, _PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY
    from .reasoning_notebook import archive_reasoning, readable_reasoning_parts
    from .mini_session.provider_lane_bank import decode_provider_lane, encode_provider_lane

    def clean_history(history: list[dict[str, Any]]) -> list[dict[str, Any]]:
        archive = []
        has_readable_reasoning = False
        result = deepcopy(history)
        for message in result:
            has_readable_reasoning |= bool(readable_reasoning_parts(message))
            archive.append(deepcopy(message))
            for key in (*_PROVIDER_CONTINUATION_STATE_KEYS, _PROVIDER_CONTINUATION_POLICY_RECEIPT_KEY):
                message.pop(key, None)
            if isinstance(message.get("tool_calls"), list):
                message["tool_calls"] = [
                    {"id": call["id"], "type": "function", "function": {
                        "name": call["function"]["name"], "arguments": call["function"]["arguments"],
                    }} for call in message["tool_calls"]
                ]
        if has_readable_reasoning:
            archive_reasoning(session.conv, archive)
        return result

    session.conv.history = clean_history(session.conv.history)
    for action in session.actions:
        active = getattr(action, "_provider_quantum_checkpoint", None)
        if active:
            active["history"] = clean_history(active["history"])
            action._refresh_active_provider_digest()
        parked = getattr(action, "_provider_quantum_parked", {})
        for lane, envelope in list(parked.items()):
            body = decode_provider_lane(lane, envelope, action._validated_provider_quantum_checkpoint)
            body["checkpoint"]["history"] = clean_history(body["checkpoint"]["history"])
            parked[lane] = encode_provider_lane(body["checkpoint"], body["prompt_scope"], body["context_identity"])
    for owner, reason_field, kind_field in (
        (session, "terminal_failure_reason", "terminal_failure_kind"),
        (session.conv, "_last_llm_failure_reason", "_last_llm_failure_kind"),
        (session.dossier, "session_failure_reason", "session_failure_kind"),
    ):
        if migratable_provider_failure(getattr(owner, reason_field, "")):
            setattr(owner, reason_field, "")
            setattr(owner, kind_field, "")
    if migratable_provider_failure(getattr(session, "last_failure_reason", "")):
        session.last_failure_reason = ""
    for action in session.actions:
        held = getattr(action, "_answer_safe_recheck_held_terminal_provider_failure", {})
        if migratable_provider_failure(held.get("terminal_failure_reason", "")):
            action._answer_safe_recheck_held_terminal_provider_failure = {}
    session.conv._provider_migration_epoch = migration["epoch"]
