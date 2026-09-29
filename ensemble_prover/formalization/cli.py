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


async def _run(args: argparse.Namespace) -> dict[str, Any]:
    from dotenv import load_dotenv

    load_dotenv()
    directory = args.directory.expanduser().resolve(strict=True)
    async with AsyncExitStack() as stack:
        compiler, project = _compiler(directory, args.lean_timeout_s)
        stack.push_async_callback(compiler.close)
        clients = []
        for role, model in (
            ("formalizer", args.formalizer_model),
            ("reviewer", args.reviewer_model),
            ("prover", args.prover_model),
        ):
            try:
                config = _make_role_cfg(
                    "openai",
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
            client = OpenAICompatClient(config)
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
    args = _parser().parse_args(argv)
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
