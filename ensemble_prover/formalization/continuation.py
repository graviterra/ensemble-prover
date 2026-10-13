"""Admit new campaign prerequisites into an existing mathematical attempt."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from .lean import ModuleArtifact


def _retire_context_receipts(session: Any) -> None:
    """Retain candidate mathematics, never replay old-context execution authority."""
    from ..reasoning_notebook import archive_pending_tool_candidates, archive_reasoning
    from ..mini_session.provider_lane_bank import decode_provider_lane

    def archive_pending_tools(state: dict[str, Any], target: str = "") -> None:
        archive_pending_tool_candidates(session.conv, state, target=target)

    def archive_candidate(record: dict[str, Any]) -> None:
        visible = {key: record[key] for key in (
            "content", "proof", "source", "code", "statement", "target_statement",
            "lean_output", "diagnostics",
        ) if isinstance(record.get(key), str)}
        for key in ("verification_check_lemmas", "verification_context_helpers", "verification_helpers"):
            if isinstance(record.get(key), list):
                visible[key] = [item if isinstance(item, str) else item["source"]
                    for item in record[key] if isinstance(item, str)
                    or isinstance(item, dict) and isinstance(item.get("source"), str)]
        if visible:
            archive_reasoning(session.conv, [{"role": "assistant", "content":
                "Candidate mathematics from the previous import context; recheck before use:\n"
                + json.dumps(visible, ensure_ascii=False, sort_keys=True)}])

    for action in session.actions:
        active = getattr(action, "_provider_quantum_checkpoint", {})
        if active:
            archive_reasoning(session.conv, active.get("history", ()))
            archive_pending_tools(active.get("state", {}), active.get("binding", {}).get("target", ""))
            action._clear_active_provider_lane()
        parked = getattr(action, "_provider_quantum_parked", {})
        for lane, envelope in parked.items():
            body = decode_provider_lane(lane, envelope, action._validated_provider_quantum_checkpoint)
            archive_reasoning(session.conv, body["checkpoint"]["history"])
            archive_pending_tools(body["checkpoint"]["state"], body["checkpoint"]["binding"].get("target", ""))
        if parked:
            action._provider_quantum_parked = {}
        for key in ("_answer_safe_recheck_pending", "_answer_safe_recheck_parked"):
            pending = getattr(action, key, {})
            if pending:
                for candidate in pending.values() if key.endswith("parked") else (pending,):
                    archive_candidate(candidate)
                setattr(action, key, {})
    live = session.conv.__dict__.pop("_provider_call_quantum_state", None)
    if live:
        archive_pending_tools(live, str(session.conv.goal_statement or ""))
    pending = getattr(session, "durable_progress_tool_continuation", {})
    if pending:
        payload = pending.get("replay_payload", {})
        archive_pending_tools(payload, payload.get("durable_progress_tool_continuation_target", ""))
        session.durable_progress_tool_continuation = {}


def checked_dependency_extension(records: list[dict[str, Any]], module_root: Path):
    """Create an owner-controlled admission callback, with no new provider budget."""
    artifacts = tuple(ModuleArtifact.from_dict(item) for item in records)

    def validate_files() -> None:
        for artifact in artifacts:
            for path, digest in ((artifact.source_path, artifact.source_sha256),
                                 (artifact.olean_path, artifact.olean_sha256)):
                if (not path.resolve().is_relative_to(module_root) or path.is_symlink()
                        or hashlib.sha256(path.read_bytes()).hexdigest() != digest):
                    raise ValueError("Campaign prerequisite artifact changed during continuation")

    validate_files()

    async def extend_context(session: Any) -> bool:
        from ..mini_session.source_imports import prepare_source_import, apply_source_import
        from ..mini_session.durable_session_record import (
            capture_session_record, restore_session_record, _fresh_check_options,
        )

        missing = [artifact for artifact in artifacts
                   if f"import {artifact.module_name}" not in session.conv.lean_preamble.splitlines()]
        if not missing:
            return False
        validate_files()
        for artifact in missing:
            pair = prepare_source_import(session, artifact.module_name)
            if not artifact.declarations:
                raise ValueError("Campaign prerequisite has no checked declarations")
            declaration = artifact.declarations[0]
            name, statement = declaration["name"], declaration["type"]
            result = await session.lean.check(statement, f"by exact @{name}", [],
                **_fresh_check_options(session.lean, pair.lean.render()))
            if not result.ok or getattr(result, "axiom_audit_ok", None) is not True:
                raise ValueError("Campaign prerequisite failed fresh Lean admission")
            validate_files()
            apply_source_import(session, pair, module=artifact.module_name,
                                declaration=name, statement=statement)
        _retire_context_receipts(session)
        # This session is still private to registry binding: no provider can run
        # and no saved lane changes until its full mathematical replay succeeds.
        record = capture_session_record(session)
        await restore_session_record(session, record, expected_identity=record["identity"])
        validate_files()
        session.conv.history.append({"role": "user", "content":
            "The campaign independently compiled these new prerequisites. They are now imported. "
            "Earlier unfinished work remains candidate reasoning and must be checked in this context.\n\n"
            + "\n\n".join(artifact.module_name + "\n" + artifact.source_path.read_text(encoding="utf-8")
                           for artifact in missing)})
        return True

    async def extend(session: Any) -> bool:
        from .prover import ProofContinuationError

        try:
            return await extend_context(session)
        except (ValueError, OSError, RuntimeError) as exc:
            raise ProofContinuationError(
                "Mini continuation prerequisite context could not be restored: " + str(exc)
            ) from exc

    return extend if artifacts else None
