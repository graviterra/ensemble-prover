"""CLI wiring for experimental autonomous mathematical research."""

from __future__ import annotations

import argparse
import asyncio
import json
import sys
from contextlib import AsyncExitStack
from pathlib import Path
from typing import Any


def register(commands: Any) -> None:
    discovery = commands.add_parser(
        "discovery",
        help="Execute a resumable mathematical research portfolio",
        allow_abbrev=False,
    )
    actions = discovery.add_subparsers(dest="discovery_command", required=True)
    init = actions.add_parser(
        "init",
        help="Save a problem and spending limits; no model calls",
        allow_abbrev=False,
    )
    init.add_argument("directory", type=Path)
    init.add_argument(
        "--problem",
        type=Path,
        required=True,
        help="Complete UTF-8 mathematical problem",
    )
    init.add_argument(
        "--source",
        type=Path,
        action="append",
        default=[],
        help="Additional complete source document",
    )
    init.add_argument("--domain", default="As specified in the original problem")
    init.add_argument("--model", required=True, help="OpenAI API research model name")
    init.add_argument(
        "--review-model", required=True, help="OpenAI API reviewer model name"
    )
    init.add_argument(
        "--max-requests",
        type=int,
        required=True,
        help="Total HTTP dispatch intents, including retries and resumes",
    )
    init.add_argument(
        "--max-seconds",
        type=float,
        required=True,
        help="Wall-clock authorization from first execution, including downtime",
    )
    init.add_argument(
        "--concurrency",
        type=int,
        default=4,
        help="Maximum active worker operations; not a model-count limit",
    )
    init.add_argument("--request-timeout-s", type=float, default=300)
    init.add_argument(
        "--experiments",
        action="store_true",
        help="Allow ephemeral namespace-isolated Python experiments",
    )
    for name, help_text in (
        ("run", "Execute or explicitly resume within the original limits"),
        ("status", "Show budget, programs, and separate mathematical assessment"),
    ):
        command = actions.add_parser(name, help=help_text, allow_abbrev=False)
        command.add_argument("directory", type=Path)
    handoff = actions.add_parser(
        "formalize",
        help="Initialize the existing formalizer from an exact saved handoff; no calls",
        allow_abbrev=False,
    )
    handoff.add_argument("directory", type=Path)
    handoff.add_argument("artifact_id")
    handoff.add_argument("--project-path", type=Path, required=True)
    handoff.add_argument("--output", type=Path, required=True)
    handoff.add_argument("--import", dest="imports", action="append", default=[])


async def _run(directory: Path) -> dict[str, Any]:
    from ..mini_prover import _make_role_cfg
    from ..models import OpenAICompatClient
    from .discovery import DiscoveryLoop
    from .discovery_store import DiscoveryStore

    from dotenv import load_dotenv

    load_dotenv()
    with DiscoveryStore(directory) as store:
        run = store.run_record()
        # Construct distinct clients per worker: provider response metadata is
        # mutable, and concurrent operations must not share that state.
        async with AsyncExitStack() as cleanup:

            def factory(role: str):
                def make(_worker: str):
                    try:
                        cfg = _make_role_cfg(
                            "openai",
                            run["review_model"] if role == "review" else run["model"],
                            role_name=role,
                            llm_deadline_policy="hard",
                            timeout_s=run["request_timeout_s"],
                        )
                    except SystemExit as exc:
                        # The legacy config helper is CLI-oriented. Never let
                        # its SystemExit escape an asynchronous worker task.
                        raise ValueError(str(exc)) from exc
                    # This optional shared-client setting predates a declared
                    # RoleConfig field and is read dynamically by the transport.
                    setattr(cfg, "operation_timeout_s", run["request_timeout_s"])
                    client = OpenAICompatClient(cfg)
                    cleanup.push_async_callback(client.close)
                    return client

                return make

            def progress(event: dict[str, Any]) -> None:
                print(
                    json.dumps(event, ensure_ascii=False), file=sys.stderr, flush=True
                )

            return await DiscoveryLoop(
                store, factory("research"), factory("review"), on_event=progress
            ).run()


def dispatch(args: argparse.Namespace) -> Any:
    from .discovery import create_formalization_handoff, initialize
    from .discovery_store import DiscoveryStore
    from .model import ClaimSpec, MathematicalContract

    if args.discovery_command == "init":
        # Numbered labels prevent duplicate basenames from overwriting sources;
        # the exact bytes, not an LLM-generated instruction file, are ingested.
        problem = args.problem.read_bytes().decode("utf-8")
        sources = {"original-problem.txt": problem}
        sources.update(
            {
                f"source-{index}-{path.name}": path.read_bytes().decode("utf-8")
                for index, path in enumerate(args.source)
            }
        )
        initialize(
            args.directory,
            target=ClaimSpec(
                "root", MathematicalContract(problem, args.domain), "user"
            ),
            sources=sources,
            model=args.model,
            review_model=args.review_model,
            max_requests=args.max_requests,
            max_seconds=args.max_seconds,
            concurrency=args.concurrency,
            request_timeout_s=args.request_timeout_s,
            experiments=args.experiments,
        )
        return {
            "status": "ready",
            "directory": str(args.directory.resolve()),
            "model_calls": 0,
        }
    if args.discovery_command == "run":
        return asyncio.run(_run(args.directory))
    if args.discovery_command == "status":
        with DiscoveryStore(args.directory) as store:
            return store.status()
    if args.discovery_command == "formalize":
        create_formalization_handoff(
            args.directory,
            args.artifact_id,
            output=args.output,
            project_path=args.project_path,
            imports=tuple(args.imports),
        )
        return {
            "status": "formalization_initialized",
            "directory": str(args.output),
            "model_calls": 0,
        }
    raise ValueError("unknown discovery command")
