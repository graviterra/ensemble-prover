"""Start, resume, inspect and export a mathematical formalization campaign."""

from __future__ import annotations

import argparse
import asyncio
import json
import math
import sys
from contextlib import AsyncExitStack
from dataclasses import asdict
from pathlib import Path
from typing import Any, Sequence

from ..mini_prover import _make_role_cfg
from ..models import OpenAICompatClient
from .campaign import Campaign, initialize_project
from .environment import EnvironmentSnapshot
from .lean import ModuleCompiler
from .prover import MiniProver
from .store import ProjectStore


def _positive_int(value: str) -> int:
    try:
        result = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("must be a positive integer") from exc
    if result < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return result


def _positive_seconds(value: str) -> float:
    try:
        result = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("must be finite positive seconds") from exc
    if not math.isfinite(result) or result <= 0:
        raise argparse.ArgumentTypeError("must be finite positive seconds")
    return result


def _nonempty(value: str) -> str:
    if not value.strip():
        raise argparse.ArgumentTypeError("must be nonempty text")
    return value


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    commands = parser.add_subparsers(dest="command", required=True)
    initialize = commands.add_parser(
        "init", help="Save original sources and a new root task", allow_abbrev=False
    )
    initialize.add_argument("--project-path", type=Path, required=True)
    initialize.add_argument(
        "--source",
        action="append",
        type=Path,
        required=True,
        help="Complete UTF-8 source file (repeatable)",
    )
    initialize.add_argument(
        "--goal", type=_nonempty, required=True, help="Complete mathematical objective"
    )
    initialize.add_argument(
        "--output", type=Path, required=True, help="New campaign directory"
    )
    initialize.add_argument(
        "--import",
        dest="imports",
        action="append",
        default=[],
        help="Trusted project import (repeatable)",
    )

    run = commands.add_parser(
        "run", help="Run a bounded quantum; repeat to resume", allow_abbrev=False
    )
    run.add_argument("directory", type=Path)
    run.add_argument(
        "--max-steps",
        type=_positive_int,
        default=100,
        help="Controller steps this invocation (default: 100)",
    )
    run.add_argument(
        "--max-model-calls",
        type=_positive_int,
        default=300,
        help=(
            "Formalizer/reviewer requests this invocation (default: 300); "
            "Mini proof attempts use their separate turn budgets"
        ),
    )
    run.add_argument(
        "--formalizer-model",
        type=_nonempty,
        default="gpt-5.6-terra",
        help="OpenAI API model name",
    )
    run.add_argument(
        "--reviewer-model",
        type=_nonempty,
        default="gpt-5.6-terra",
        help="OpenAI API model name",
    )
    run.add_argument(
        "--prover-model",
        type=_nonempty,
        default="gpt-5.6-luna",
        help="OpenAI API model name",
    )
    for role in ("formalizer", "reviewer", "prover"):
        run.add_argument(
            f"--{role}-provider",
            choices=("openai", "deepseek", "openrouter", "codex", "claude-code", "cursor", "local"),
            default=None,
            help="Explicit provider. local-only does not assume OpenAI and does not mean offline.",
        )
        run.add_argument(f"--{role}-deployment", default=None)
    run.add_argument("--local-inference-config", type=Path, default=None)
    run.add_argument(
        "--inference-policy", choices=("mixed", "local-only"), default="mixed",
        help="local-only requires every role to be an explicit local deployment.",
    )
    from ..local_inference.network_policy import add_network_policy_argument
    add_network_policy_argument(run)
    run.add_argument("--coordinator-root", type=Path, default=None)
    run.add_argument("--cursor-bin", default="agent")
    run.add_argument("--claude-code-bin", default="claude")
    run.add_argument("--codex-bin", default="codex")
    run.add_argument(
        "--model-timeout-s",
        type=_positive_seconds,
        help="Seconds per model operation; omitted uses shared model defaults",
    )
    run.add_argument("--lean-timeout-s", type=_positive_seconds, default=300)
    run.add_argument("--lease-s", type=_positive_seconds, default=300)

    status = commands.add_parser(
        "status",
        help="Validate artifacts and report campaign progress",
        allow_abbrev=False,
    )
    status.add_argument("directory", type=Path)
    task = commands.add_parser(
        "task", help="Print a complete task record", allow_abbrev=False
    )
    task.add_argument("directory", type=Path)
    task.add_argument("task_id")
    revise = commands.add_parser(
        "revise",
        help="Revise a task and invalidate its dependent tasks",
        allow_abbrev=False,
    )
    revise.add_argument("directory", type=Path)
    revise.add_argument("task_id")
    revise.add_argument("--description", type=_nonempty, required=True)
    export = commands.add_parser(
        "export", help="Export a verified Lean development", allow_abbrev=False
    )
    export.add_argument("directory", type=Path)
    export.add_argument("--output", type=Path, required=True)
    return parser


def _compiler(directory: Path, timeout_s: float) -> tuple[ModuleCompiler, Path]:
    with ProjectStore(directory) as store:
        metadata = store.get_metadata()
    if metadata.get("campaign_schema") != 1 or not metadata.get("initialized"):
        raise ValueError("unsupported or incomplete campaign initialization")
    project = Path(metadata["project_path"]).expanduser().resolve(strict=True)
    imports = metadata.get("imports", [])
    # A missing snapshot cannot be replaced with today's environment: that
    # would silently change the campaign's original mathematical foundation.
    environment = EnvironmentSnapshot.from_dict(metadata.get("environment"))
    compiler = ModuleCompiler(
        project,
        directory / "modules",
        timeout_s=timeout_s,
        trusted_imports=imports,
        environment=environment,
    )
    return compiler, project


def _campaign_provider(args: argparse.Namespace, role: str) -> str:
    value = getattr(args, f"{role}_provider")
    if value:
        return str(value)
    if getattr(args, "inference_policy", "mixed") == "local-only":
        raise ValueError(
            f"{role} has no explicit provider. local-only cannot assume OpenAI. "
            "local-only does not mean offline and does not by itself stop downloads."
        )
    return "openai"


def _inherit_local_campaign(args: argparse.Namespace, directory: Path) -> None:
    """Resume saved local roles before cloud defaults can take effect."""
    if not (directory / "local_inference").exists():
        return
    from ..local_inference.config import load_private_worker_snapshot
    from ..local_inference.roles import load_run_bundle
    from ..local_inference.errors import LocalInferenceError

    saved = load_run_bundle(directory)
    explicit = set(getattr(args, "explicit_options", ()))
    if "--inference-policy" in explicit and args.inference_policy != saved.inference_policy:
        raise LocalInferenceError("profile_conflict")
    args.inference_policy = saved.inference_policy
    if "--coordinator-root" in explicit and str(args.coordinator_root.expanduser().resolve()) != saved.coordinator_root:
        raise LocalInferenceError("profile_conflict")
    resolved = load_private_worker_snapshot(saved.snapshot)
    for role, selected in resolved.roles.items():
        for suffix, expected in (("provider", "local"), ("deployment", selected.deployment_id), ("model", selected.model)):
            if f"--{role}-{suffix}" in explicit and getattr(args, f"{role}_{suffix}") != expected:
                raise LocalInferenceError("profile_conflict")
            setattr(args, f"{role}_{suffix}", expected)


def _validate_campaign_providers(args: argparse.Namespace) -> None:
    providers = [_campaign_provider(args, role) for role in ("formalizer", "reviewer", "prover")]
    if args.inference_policy == "local-only" and any(item != "local" for item in providers):
        raise ValueError(
            "local-only requires explicit local formalizer, reviewer, and prover roles. "
            "local-only does not mean offline and does not by itself stop downloads."
        )
    explicit = set(getattr(args, "explicit_options", ()))
    for role, provider in zip(("formalizer", "reviewer", "prover"), providers):
        if provider != "cursor":
            continue
        model = getattr(args, f"{role}_model")
        if f"--{role}-model" not in explicit or not model or str(model).casefold() == "auto":
            raise ValueError("cursor requires an exact model id; auto is not substituted")


def _open_local_campaign(args: argparse.Namespace, directory: Path) -> None:
    from ..local_inference.config import load_profile_path
    from ..local_inference.errors import LocalInferenceError
    from ..workflow_roles import (
        deployment_of,
        prepare_auxiliary,
        resume_workflow,
        start_workflow,
    )
    from ..local_inference.roles import load_run_bundle

    roles = [
        role for role in ("formalizer", "reviewer", "prover")
        if _campaign_provider(args, role) == "local"
    ]
    explicit = set(getattr(args, "explicit_options", ()))
    binding = directory / "local_inference" / "run_binding.json"
    if binding.is_file():
        bundle = load_run_bundle(directory)
        if "--local-inference-config" in explicit and args.local_inference_config is not None:
            if load_profile_path(args.local_inference_config).profile_hash != bundle.profile_hash:
                raise LocalInferenceError("profile_conflict")
        for role in roles:
            if f"--{role}-deployment" in explicit:
                if deployment_of(bundle, role) != getattr(args, f"{role}_deployment"):
                    raise LocalInferenceError("profile_conflict")
        from ..local_inference.network_policy import admit_network_policy
        admit_network_policy(args, bundle, directory, directory=directory)
        resume_workflow(directory)
        return
    specs = []
    for role in roles:
        deployment = getattr(args, f"{role}_deployment")
        if not deployment or args.local_inference_config is None:
            raise ValueError(
                f"{role} requires --{role}-deployment and --local-inference-config"
            )
        requested = getattr(args, f"{role}_model") if f"--{role}-model" in explicit else None
        specs.append((role, deployment, requested))
    preparation = prepare_auxiliary(
        specs,
        inference_policy=args.inference_policy,
        coordinator=args.coordinator_root,
        config_path=args.local_inference_config,
    )
    from ..local_inference.network_policy import admit_network_policy
    admit_network_policy(args, preparation, directory, directory=directory)
    start_workflow(directory, preparation)


async def _run(args: argparse.Namespace) -> dict[str, Any]:
    from dotenv import load_dotenv
    from ..workflow_roles import resume_role_client, workflow_client

    load_dotenv()
    directory = args.directory.expanduser().resolve(strict=True)
    _inherit_local_campaign(args, directory)
    _validate_campaign_providers(args)
    # Inference-policy local-only is not Campaign.run(local_only=True): that
    # switch skips model calls and replays saved recovery.
    if any(_campaign_provider(args, role) == "local" for role in ("formalizer", "reviewer", "prover")):
        _open_local_campaign(args, directory)
    else:
        from ..local_inference.network_policy import admit_network_policy
        admit_network_policy(args, None, directory, directory=directory)
    async with AsyncExitStack() as stack:
        compiler, project = _compiler(directory, args.lean_timeout_s)
        stack.push_async_callback(compiler.close)
        clients = []
        for role in ("formalizer", "reviewer", "prover"):
            provider = _campaign_provider(args, role)
            model = getattr(args, f"{role}_model")
            if provider == "local":
                client = resume_role_client(directory, role, timeout_s=args.model_timeout_s or 300.0)
                stack.push_async_callback(client.close)
                clients.append(client)
                continue
            try:
                config = _make_role_cfg(
                    provider,
                    model,
                    role_name=role,
                    llm_deadline_policy="hard",
                    timeout_s=args.model_timeout_s,
                )
            except SystemExit as exc:
                raise ValueError(str(exc)) from exc
            # Preserve the shared model-capability maximum. This transport
            # requires an integer envelope; None is not an unlimited sentinel.
            # Do not replace it with a smaller campaign-specific output cap.
            if args.model_timeout_s is not None:
                config.operation_timeout_s = args.model_timeout_s
            if provider == "cursor":
                config.cursor_binary = args.cursor_bin
            elif provider == "claude-code":
                config.claude_code_binary = args.claude_code_bin
            elif provider == "codex":
                config.codex_binary = args.codex_bin
            client = (
                workflow_client(config)
                if provider in {"codex", "claude-code", "cursor"}
                else OpenAICompatClient(config)
            )
            stack.push_async_callback(client.close)
            clients.append(client)
        prover = MiniProver(
            project,
            directory / "modules",
            clients[2],
            options={"lean_timeout_s": args.lean_timeout_s},
        )
        stack.push_async_callback(prover.close)
        campaign = stack.enter_context(
            Campaign(
                directory,
                formalizer=clients[0],
                reviewer=clients[1],
                compiler=compiler,
                prover=prover,
                lease_s=args.lease_s,
            )
        )
        result = await campaign.run(
            max_steps=args.max_steps, max_model_calls=args.max_model_calls
        )
        return {
            **result,
            "max_steps": args.max_steps,
            "max_model_calls": args.max_model_calls,
        }


async def _status(directory: Path) -> dict[str, Any]:
    async with AsyncExitStack() as stack:
        compiler, _ = _compiler(directory, 300)
        stack.push_async_callback(compiler.close)
        campaign = stack.enter_context(
            Campaign(
                directory,
                formalizer=None,
                reviewer=None,
                compiler=compiler,
                prover=None,
            )
        )
        return campaign.status()


async def _export(directory: Path, output: Path) -> dict[str, Any]:
    from .export import export_project

    return await export_project(directory, output)


def main(argv: Sequence[str] | None = None) -> int:
    raw = list(sys.argv[1:] if argv is None else argv)
    args = _parser().parse_args(argv)
    args.explicit_options = {item.split("=", 1)[0] for item in raw if item.startswith("--")}
    try:
        if args.command == "init":
            documents = {}
            for source in args.source:
                path = source.expanduser().resolve(strict=True)
                documents[str(path)] = path.read_bytes().decode("utf-8")
            directory = args.output.expanduser().resolve()
            initialize_project(
                directory,
                project_path=args.project_path,
                documents=documents,
                goal=args.goal,
                imports=args.imports,
            )
            report = {
                "status": "initialized",
                "directory": str(directory),
                "sources": len(documents),
            }
        else:
            directory = args.directory.expanduser().resolve(strict=True)
            if args.command == "run":
                report = asyncio.run(_run(args))
            elif args.command == "status":
                report = asyncio.run(_status(directory))
            elif args.command == "export":
                report = asyncio.run(
                    _export(directory, args.output.expanduser().resolve())
                )
            else:
                with ProjectStore(directory) as store:
                    if args.command == "task":
                        report = asdict(store.get_task(args.task_id))
                    else:
                        revised = store.revise(
                            args.task_id, description=args.description
                        )
                        report = {
                            "task": asdict(revised),
                            "dependent_tasks_invalidated": True,
                        }
        print(json.dumps(report, ensure_ascii=False, allow_nan=False, indent=2))
        return (
            2
            if report.get("status")
            in {"invalid", "blocked", "needs_clarification", "failed"}
            or report.get("stop_reason") in {"provider_error", "context_overflow"}
            else 0
        )
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as exc:
        print(f"Campaign failed: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print(
            "Campaign interrupted; saved work remains available for resume.",
            file=sys.stderr,
        )
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
