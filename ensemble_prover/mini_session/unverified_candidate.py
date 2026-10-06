"""Unverified paid tool input retained across a settled child cancellation.

These records carry no proof authority. Their digest detects accidental changes;
fresh context matching and the ordinary verifier establish replay eligibility.
"""

from __future__ import annotations

import copy
import asyncio
import hashlib
import json
import math
import time
import threading
from pathlib import Path
from types import SimpleNamespace
from typing import Any


def _project_capture_view(session: Any) -> tuple[Any, tuple[Any, ...]]:
    """Freeze only immutable identity inputs; never send a dossier to a thread."""
    from .session import _dispatch_capability_identity

    lean = session.lean
    owner = _dispatch_capability_identity(lean)
    project = getattr(lean, "project_dir", None)
    config = getattr(lean, "cfg", None)
    values = {name: copy.deepcopy(getattr(config, name, default)) for name, default in (
        ("project_imports", []), ("project_import_sources", {}),
        ("support_project_builds", {}), ("extra_imports", []),
        ("module_search_paths", []), ("preamble_import", ""), ("preamble_tactics", ""),
    )}
    generation = getattr(lean, "_execution_environment_generation", 0)
    preamble = str(getattr(session.conv, "lean_preamble", "") or "")

    class VerifierIdentity:
        project_dir = Path(project) if project is not None else None
        cfg = SimpleNamespace(**values)
        _execution_environment_generation = generation

        def _dispatch_capability_identity_token(self):
            return owner

    view = SimpleNamespace(lean=VerifierIdentity(), conv=SimpleNamespace(lean_preamble=preamble), actions=[])
    binding = (id(owner), str(project), generation, preamble, candidate_digest(values))
    return view, binding


async def candidate_project_hash(session: Any, *, deadline_epoch_s: float) -> str:
    """Capture off-loop within the caller's lease; interrupted hashes never publish."""
    remaining = deadline_epoch_s - time.time()
    if remaining <= 0:
        return ""
    view, binding = _project_capture_view(session)
    cancelled = threading.Event()
    monotonic_deadline = time.monotonic() + remaining

    def check() -> None:
        if cancelled.is_set() or time.monotonic() >= monotonic_deadline:
            raise TimeoutError("Candidate environment capture deadline exhausted")

    def capture() -> str:
        check()
        from .durable_session_record import session_checkpoint_identity
        from ..formalization.environment import _CAPTURE_CHECK
        from ..mini_theory.environment import environment_fingerprint_scope

        token = _CAPTURE_CHECK.set(check)
        try:
            check()
            with environment_fingerprint_scope(
                cancellation_event=cancelled, deadline_monotonic=monotonic_deadline,
            ):
                project_hash = session_checkpoint_identity(view)["project_hash"]
            check()
            return project_hash
        finally:
            _CAPTURE_CHECK.reset(token)

    try:
        result = await asyncio.wait_for(asyncio.to_thread(capture), timeout=remaining)
        if _project_capture_view(session)[1] != binding:
            return ""
        return result
    except (OSError, ValueError, RuntimeError):
        # Optional retention cannot turn a missing/unreadable import into a
        # failed proving lane. No binding means replay is unavailable; caller
        # cancellation still propagates through its separate BaseException.
        return ""
    finally:
        cancelled.set()


async def validate_candidate_async(record: Any, session: Any, *, deadline_epoch_s: float = 0.0) -> bool:
    if type(record) is not dict:
        return False
    raw_deadline = record.get("verification_deadline_epoch_s")
    if type(raw_deadline) not in {int, float} or not math.isfinite(raw_deadline):
        return False
    deadline = min(raw_deadline, deadline_epoch_s) if deadline_epoch_s > 0 else raw_deadline
    project_hash = await candidate_project_hash(session, deadline_epoch_s=deadline)
    return bool(project_hash) and validate_candidate(record, session, project_hash=project_hash)


def candidate_digest(record: dict[str, Any]) -> str:
    return hashlib.sha256(json.dumps(
        record, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def capture_candidate(*, conv: Any, target: str, helpers: list[str], args: dict, lean: Any = None,
                      replay_mode: str = "try_lean") -> dict:
    if type(args) is not dict or type(args.get("code")) is not str or not args["code"].strip():
        return {}
    configured = float(getattr(getattr(lean, "cfg", None), "timeout_s", 300.0) or 300.0)
    allowance = configured if configured > 0.0 and math.isfinite(configured) else 300.0
    return {
        "schema_version": 1,
        "status": "unverified",
        "replay_mode": replay_mode,
        "target": str(target),
        "preamble": str(getattr(conv, "preamble", "") or ""),
        "lean_preamble": str(getattr(conv, "lean_preamble", "") or ""),
        "helpers": list(helpers),
        "args": copy.deepcopy(args),
        "verification_deadline_epoch_s": time.time() + allowance,
    }


def bind_candidate(record: Any, session: Any = None, *, project_hash: str = "") -> dict:
    keys = {
        "schema_version", "status", "replay_mode", "target", "preamble", "lean_preamble", "helpers", "args",
        "verification_deadline_epoch_s",
    }
    if type(record) is not dict or set(record) not in (keys, keys | {"project_hash"}):
        return {}
    bound = copy.deepcopy(record)
    if "project_hash" not in bound:
        bound["project_hash"] = project_hash
    bound["digest"] = candidate_digest(bound)
    # A scope change may prevent replay, but must not erase the paid input.
    # Validation is deliberately separate from retaining unverified data.
    return bound


def validate_candidate(record: Any, session: Any, *, project_hash: str = "") -> bool:
    if type(record) is not dict or set(record) != {
        "schema_version", "status", "replay_mode", "target", "preamble", "lean_preamble", "helpers", "args",
        "verification_deadline_epoch_s",
        "project_hash", "digest",
    }:
        return False
    if (type(record["schema_version"]) is not int or record["schema_version"] != 1
            or record["status"] != "unverified"
            or type(record["replay_mode"]) is not str
            or record["replay_mode"] not in {"try_lean", "final_response"}
            or type(record["args"]) is not dict
            or type(record["args"].get("code")) is not str
            or not record["args"]["code"].strip()
            or type(record["helpers"]) is not list
            or type(record["verification_deadline_epoch_s"]) not in {int, float}
            or not math.isfinite(record["verification_deadline_epoch_s"])
            or record["verification_deadline_epoch_s"] <= 0
            or any(type(block) is not str for block in record["helpers"])):
        return False
    conv = session.conv
    context = getattr(session.dossier, "execution_helper_blocks", session.dossier.verified_helper_blocks)
    if (record["target"] != str(getattr(conv, "goal_statement", "") or "")
            or record["preamble"] != str(getattr(conv, "preamble", "") or "")
            or record["lean_preamble"] != str(getattr(conv, "lean_preamble", "") or "")
            or record["helpers"] != list(context())
            or not project_hash or record["project_hash"] != project_hash):
        return False
    return record["digest"] == candidate_digest({
        key: value for key, value in record.items() if key != "digest"
    })


def replay_state(record: dict, conv: Any) -> dict:
    from .turn.tool_loop import _durable_progress_tool_continuation_identity

    calls = [{"id": "unverified_" + record["digest"][:24], "type": "function",
              "function": {"name": "try_lean", "arguments": json.dumps(record["args"])}}]
    role = str(conv.role)
    return {
        "schema_version": 4,
        "tool_calls_used": 0,
        "pending_tool_replay": calls,
        "pending_tool_replay_disposition": "durable_progress_cutpoint",
        "durable_progress_tool_continuation_role": role,
        "durable_progress_tool_continuation_target": record["target"],
        "durable_progress_tool_continuation_helper_receipts": [],
        "durable_progress_tool_continuation_identity": _durable_progress_tool_continuation_identity(
            role=role, target_statement=record["target"], pending_tool_replay=calls,
        ),
    }
