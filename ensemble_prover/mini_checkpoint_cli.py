"""Public CLI configuration and generation setup for durable Mini attempts."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any

from .state_data import clone_json_value
from .cost_policy import require_cost_budget_usd


_GENERATION_OPTIONS = frozenset({
    "output_dir", "resume_from", "terminal_trace", "mini_theory_startup_overlay_nonce",
    "resume_accept_source_hash",
})

_SUBSCRIPTION_BINARY_OPTIONS = {"codex": ("codex_bin", "codex"), "claude-code": ("claude_code_bin", "claude")}


class CheckpointArgumentParser(argparse.ArgumentParser):
    """Remember explicit overrides, including values equal to parser defaults."""

    def parse_args(self, args: Any = None, namespace: Any = None) -> argparse.Namespace:
        tokens = list(sys.argv[1:] if args is None else args)
        result = super().parse_args(tokens, namespace)
        explicit = set()
        for token in tokens:
            if token == "--":
                break
            if not token.startswith("--"):
                continue
            option = self._parse_optional(token)
            # argparse returns one tuple on 3.11, but a list of candidate
            # tuples on patched 3.12. Parsing above already rejects ambiguity.
            candidates = option if isinstance(option, list) else [option]
            for candidate in candidates:
                if candidate is not None and candidate[0] is not None:
                    explicit.add(candidate[0].dest)
        result._explicit_cli_destinations = explicit
        return result


def public_cli_config(args: argparse.Namespace) -> dict[str, Any]:
    """Persist public policy values, never clients, credentials, or callbacks."""

    config = {
        key: value for key, value in vars(args).items()
        if not key.startswith("_") and key not in _GENERATION_OPTIONS
    }
    for provider, (option, _) in _SUBSCRIPTION_BINARY_OPTIONS.items():
        if provider not in {config.get("prover"), config.get("refiner")}:
            # Preserve old policy shapes unless this transport is selected.
            config.pop(option, None)
    return clone_json_value(config, label="checkpoint CLI configuration")


def resolve_resume_args(args: argparse.Namespace) -> argparse.Namespace:
    """Inherit saved policy while rejecting explicitly conflicting overrides."""

    resume_from = getattr(args, "resume_from", None)
    if getattr(args, "resume_accept_source_hash", "") and not resume_from:
        raise ValueError("Source approval requires --resume-from")
    if not resume_from or getattr(args, "_checkpoint_config_resolved", False):
        return args
    from .mini_session.attempt_checkpoint import AttemptCheckpointRegistry

    manifest = AttemptCheckpointRegistry._load_manifest(Path(resume_from).resolve())
    identity = manifest["identity"]
    if (type(identity) is not dict or identity.get("cli_schema_version") != 1
            or type(identity.get("cli_config")) is not dict):
        raise ValueError("Checkpoint does not contain a compatible public CLI configuration")
    saved = clone_json_value(identity["cli_config"], label="saved CLI configuration")
    current = public_cli_config(args)
    for provider, (option, default) in _SUBSCRIPTION_BINARY_OPTIONS.items():
        if provider in {saved.get("prover"), saved.get("refiner")}:
            # Bare resume inherits the saved transport schema, but explicit
            # binary/provider overrides must still pass compatibility checks.
            current[option] = getattr(args, option, default)
    if set(saved) != set(current):
        raise ValueError("Checkpoint CLI configuration schema has changed")
    explicit = getattr(args, "_explicit_cli_destinations", None)
    if not isinstance(explicit, set):
        raise ValueError("Resume configuration requires parsed explicit CLI options")
    for name in explicit - _GENERATION_OPTIONS:
        if name not in saved or current[name] != saved[name]:
            raise ValueError(f"Resume configuration override is incompatible: {name}")
    if saved.get("checkpoint_enabled") is not True:
        raise ValueError("Resume requires durable checkpointing")
    for name, value in saved.items():
        setattr(args, name, value)
    args.resume_from = str(Path(resume_from).resolve())
    args._checkpoint_config_resolved = True
    return args


def cli_attempt_identity(args: argparse.Namespace, problem: Any) -> dict[str, Any]:
    """Bind public policy to the exact input bytes and declared target."""

    source = Path(problem.path).resolve()
    return {
        "cli_schema_version": 1,
        "cli_config": public_cli_config(args),
        "executor_source_hash": executor_source_fingerprint(),
        "input": {
            "source_path": str(source),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "theorem_name": str(problem.theorem_name),
            "statement_type": str(problem.statement_type),
        },
    }


def executor_source_fingerprint() -> str:
    """Bind executable package contents independently of commits or file times."""
    package = Path(__file__).resolve().parent
    sources = [(str(path.relative_to(package)), hashlib.sha256(path.read_bytes()).hexdigest())
               for path in sorted(package.rglob("*.py"))]
    if not sources:
        raise ValueError("Executor source identity is unavailable")
    return hashlib.sha256(json.dumps(sources, separators=(",", ":")).encode()).hexdigest()


class WorkerBudgetExhausted(RuntimeError):
    """The prior committed generations consumed the whole worker allowance."""


def remaining_worker_timeout_s(args: argparse.Namespace) -> float:
    """Read the current committed attempt head before granting a worker lease."""
    cap = float(getattr(args, "mini_worker_timeout_s", 0.0) or 0.0)
    if not math.isfinite(cap) or cap < 0:
        raise ValueError("Invalid worker timeout")
    resume_from = getattr(args, "resume_from", None)
    if not resume_from or cap == 0:
        return cap
    from .mini_session.attempt_checkpoint import (
        AttemptCheckpointRegistry, _digest, _read, worker_elapsed_for_resume,
    )

    predecessor = Path(resume_from).resolve()
    manifest = AttemptCheckpointRegistry._load_manifest(predecessor)
    owner = Path(manifest["registry_root"])
    with (owner / "writer.lock").open("rb") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("Attempt checkpoint already has an active writer") from error
        manifest = AttemptCheckpointRegistry._load_manifest(predecessor)
        head = _read(owner / "head.json")
        if (head.get("generation_id") != manifest["head"]["generation_id"]
                or Path(head.get("snapshot_path", "")).parent != predecessor / "checkpoints"):
            raise ValueError("Stale checkpoint generation; resume the latest attempt head")
        snapshot = _read(Path(head["snapshot_path"]))
        if (_digest(snapshot) != head.get("snapshot_hash")
                or snapshot.get("attempt_id") != manifest["attempt_id"]
                or snapshot.get("identity") != manifest["identity"]):
            raise ValueError("Attempt checkpoint snapshot identity or hash mismatch")
        elapsed = worker_elapsed_for_resume(snapshot)
    remaining = cap - elapsed
    if remaining <= 0:
        raise WorkerBudgetExhausted("The cumulative Mini worker execution budget is exhausted")
    return remaining


async def checkpoint_cost_controller(registry: Any, recorder: Any, args: Any) -> Any:
    """Recover financial exposure before the generation can admit transport."""

    from .llm_usage import CostBudgetController

    max_cost_usd = require_cost_budget_usd(getattr(args, "cost_budget_usd", 0.0))

    saved = registry.cost_resume_state if registry is not None else None
    sink = registry.durable_cost_event if registry is not None else None
    if saved is None:
        if registry is not None and registry.is_resume:
            registry.validated_journal_records()
        controller = CostBudgetController(
            max_cost_usd=max_cost_usd,
            reserve_output_tokens=max(0, int(getattr(args, "cost_budget_reserve_output_tokens", 1024) or 0)),
            event_sink=recorder.record_turn,
            durable_event_sink=sink,
        )
    else:
        controller = CostBudgetController.from_execution_record(
            saved, event_sink=recorder.record_turn, durable_event_sink=sink,
        )
        suffix = registry.validated_journal_records()
        for entry in suffix:
            await controller.apply_durable_journal_record(entry)
        head = suffix[-1] if suffix else None
        await controller.resume_after_journal_recovery(
            journal_sequence=head["sequence"] if head else saved["journal_sequence"],
            journal_hash=head["record_hash"] if head else saved["journal_hash"],
        )
    if registry is not None:
        registry.cost_controller = controller
        await registry.write_snapshot()
    return controller
