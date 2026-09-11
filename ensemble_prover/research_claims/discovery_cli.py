"""CLI wiring for experimental autonomous mathematical research."""

from __future__ import annotations

import argparse
import asyncio
import json
import sys
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
    init.add_argument(
        "--provider",
        choices=("openai", "codex"),
        default="openai",
        help="Research transport: OpenAI API or Codex ChatGPT subscription",
    )
    init.add_argument(
        "--review-provider",
        choices=("openai", "codex"),
        help="Review transport (defaults to --provider; no automatic API fallback)",
    )
    init.add_argument(
        "--model",
        required=True,
        help="Research/formalizer/prover/refiner model name for the selected provider",
    )
    init.add_argument(
        "--review-model",
        required=True,
        help="Argument and semantic statement reviewer model name for its provider",
    )
    init.add_argument(
        "--codex-bin",
        default="codex",
        help="Codex CLI executable; saved at initialization for resume",
    )
    init.add_argument(
        "--max-requests",
        type=int,
        required=True,
        help="Total dispatch intents across roles and resumes: API requests or codex exec invocations",
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
        "--project-path",
        type=Path,
        help="Enable automatic formalization, Mini proof search and feedback in this existing Lake project",
    )
    init.add_argument(
        "--import",
        dest="imports",
        action="append",
        default=[],
        help="Trusted Lean project import (repeatable; requires --project-path)",
    )
    init.add_argument(
        "--proof-quantum-s",
        type=float,
        default=600,
        help="Seconds before proof work returns feedback to research; shares the overall deadline",
    )
    init.add_argument(
        "--formalization-steps",
        type=int,
        default=8,
        help="Campaign controller steps per proof quantum",
    )
    init.add_argument("--lean-timeout-s", type=float, default=300)
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
    from ..codex_subscription import CodexSubscriptionClient
    from ..mini_prover import _make_role_cfg
    from ..models import OpenAICompatClient
    from .discovery import DiscoveryLoop
    from .discovery_store import DiscoveryStore, provider_routes
    from .proof_bridge import ProofBridge, configuration

    from dotenv import load_dotenv

    load_dotenv()
    with DiscoveryStore(directory) as store:
        run = store.run_record()
        research_provider, review_provider = provider_routes(run)
        closed_loop = configuration(run)
        # Construct distinct clients per worker: provider response metadata is
        # mutable, and concurrent operations must not share that state.
        def factory(role: str):
            def make(_worker: str):
                try:
                    cfg = _make_role_cfg(
                        review_provider if role == "review" else research_provider,
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
                client: Any
                if (
                    review_provider if role == "review" else research_provider
                ) == "codex":
                    cfg.codex_binary = run.get("codex_binary", "codex")
                    client = CodexSubscriptionClient(cfg)
                else:
                    client = OpenAICompatClient(cfg)
                return client

            return make

        def progress(event: dict[str, Any]) -> None:
            print(
                json.dumps(event, ensure_ascii=False), file=sys.stderr, flush=True
            )

        def proof_client(role: str, worker: str):
            return factory(
                "review" if role == "semantic_reviewer" else "research"
            )(worker)

        return await DiscoveryLoop(
            store,
            factory("research"),
            factory("review"),
            on_event=progress,
            owns_clients=True,
            proof_runner=ProofBridge(store, proof_client, owns_clients=True)
            if closed_loop is not None
            else None,
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
            provider=args.provider,
            review_provider=args.review_provider,
            codex_binary=args.codex_bin,
            project_path=args.project_path,
            imports=tuple(args.imports),
            proof_quantum_s=args.proof_quantum_s,
            formalization_steps=args.formalization_steps,
            lean_timeout_s=args.lean_timeout_s,
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
