"""CLI wiring for experimental autonomous mathematical research."""

from __future__ import annotations

import argparse
import asyncio
import json
import sys
from pathlib import Path
from typing import Any


_STRATEGY_SHUTDOWN_SECONDS = 0.5


async def _drain_strategy_tasks() -> None:
    """Give fenced CLI tails a bounded chance to release their async resources."""
    loop = asyncio.get_running_loop()
    deadline = loop.time() + _STRATEGY_SHUTDOWN_SECONDS
    current = asyncio.current_task()
    pending = {task for task in asyncio.all_tasks() if task is not current}
    for task in pending:
        task.cancel()
    # Async-generator finalizers may also suppress cancellation. They share
    # the same drain deadline as worker and transport cleanup.
    pending.add(asyncio.create_task(loop.shutdown_asyncgens()))
    while pending and loop.time() < deadline:
        done, _ = await asyncio.wait(pending, timeout=max(0, deadline - loop.time()))
        for task in done:
            if not task.cancelled():
                error = task.exception()
                if error is not None:
                    _shutdown_diagnostic("strategy_shutdown_error", exception_type=type(error).__name__)
        # A retired transport may finish by starting its owned-client close.
        # Those children receive only the remainder of this same deadline.
        pending = {task for task in asyncio.all_tasks() if task is not current}
    # Cleanup may have started children. Fence them too, without another fresh
    # timeout; the CLI-owned loop is closed immediately after this coroutine.
    remaining = {task for task in asyncio.all_tasks() if task is not current}
    for task in remaining:
        task.cancel()
    if remaining:
        _shutdown_diagnostic("strategy_shutdown_incomplete", pending_tasks=len(remaining))


def _shutdown_diagnostic(event: str, **details: Any) -> None:
    try:
        print(json.dumps({"event": event, **details}), file=sys.stderr, flush=True)
    except (OSError, ValueError):
        pass  # Broken diagnostic output must not prevent releasing the loop.


def _run_strategy_cli(directory: Path) -> dict[str, Any]:
    """Own and close the CLI loop without unbounded asyncio.run tail joining."""
    # Keep Runner's normal main-task/SIGINT behavior. Its default close() joins
    # every task indefinitely, so this strategy-only boundary drains and closes
    # its loop explicitly. Library users continue to own their own event loop.
    runner = asyncio.Runner()
    try:
        return runner.run(_run(directory))
    finally:
        loop = runner.get_loop()
        try:
            loop.run_until_complete(_drain_strategy_tasks())
        finally:
            asyncio.set_event_loop(None)
            loop.close()


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
        help="Complete UTF-8 mathematical problem",
    )
    init.add_argument("--lean-file", type=Path, help="Pin this original Lean theorem before candidate code is loaded")
    init.add_argument("--theorem", help="Qualified original theorem name; requires --lean-file")
    init.add_argument("--adopt-mini-run", type=Path, help="Import a stopped Mini attempt into a new research ledger; leaves the old run intact")
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
    init.add_argument("--strategy-recovery", action=argparse.BooleanOptionalAction, default=True,
                      help="Continuously research and reconsider stalled routes (default on)")
    init.add_argument("--strategy-interval-requests", type=int, default=10)
    init.add_argument("--strategy-interval-seconds", type=float, default=600)
    init.add_argument("--strategy-reserve-requests", type=int, default=4)
    init.add_argument("--strategy-reserve-seconds", type=float, default=60)
    init.add_argument("--strategy-max-no-progress", type=int, default=2)
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
    subjects = actions.add_parser("subjects", help="Inspect exact strategy handles, objections and allocation history")
    subjects.add_argument("directory", type=Path)
    evidence = actions.add_parser("evidence", help="Submit a complete finding for independent review during execution; no model calls")
    evidence.add_argument("directory", type=Path)
    evidence.add_argument("--subject", required=True, help="Exact issued subject handle from discovery subjects")
    evidence.add_argument("--scope", required=True, choices=("claim_contradiction", "method_barrier", "unsupported_bridge", "allocation_exhausted"))
    evidence.add_argument("--method", default="", help="Exact method handle for a method or bridge objection")
    evidence.add_argument("--argument", type=Path, required=True, help="Complete applicability argument and remaining uncertainty")
    evidence.add_argument("--source", type=Path, action="append", default=[], help="Exact source bytes; text or PDF")
    evidence.add_argument("--supersedes", action="append", default=[], help="Explicit review ID to appeal")
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
        adoption = None
        original = None
        pin = None
        if args.adopt_mini_run:
            from .adoption import read_mini_run
            if args.lean_file or args.theorem:
                raise ValueError("choose --adopt-mini-run or --lean-file with --theorem")
            adoption = read_mini_run(args.adopt_mini_run)
            original = adoption["problem"]
            if args.project_path and args.project_path.resolve() != original.project_path:
                raise ValueError("adoption project differs from the original Mini project")
            args.project_path = original.project_path
            if args.imports and tuple(args.imports) != original.imports:
                raise ValueError("adoption imports differ from the saved Mini context")
            args.imports = list(original.imports)
            if original.source_dirs:
                raise ValueError("adoption with supporting source directories requires a Lake project containing those modules; saved source directories cannot be silently dropped")
        elif args.lean_file or args.theorem:
            from ..theorem_project import TheoremProjectRequest, resolve_theorem_project
            if not args.lean_file or not args.theorem or not args.project_path:
                raise ValueError("pinning requires --lean-file, --theorem and --project-path")
            original = resolve_theorem_project(TheoremProjectRequest(args.lean_file, args.theorem, args.project_path, imports=tuple(args.imports)))
        if original:
            if not args.strategy_recovery:
                raise ValueError("an original Lean target requires strategy recovery")
            from ..formalization.lean import ModuleCompiler
            from .pinned_target import capture_target
            async def capture():
                compiler = ModuleCompiler(args.project_path, args.directory / "original-modules",
                    trusted_imports=tuple(args.imports), timeout_s=args.lean_timeout_s)
                try:
                    return await capture_target(original, compiler)
                finally:
                    await compiler.close()
            pin = asyncio.run(capture())
        if not args.problem and not original:
            raise ValueError("supply --problem, --lean-file/--theorem or --adopt-mini-run")
        # Numbered labels prevent duplicate basenames from overwriting sources;
        # the exact bytes, not an LLM-generated instruction file, are ingested.
        problem = args.problem.read_bytes().decode("utf-8") if args.problem else original.statement_type
        sources = {"original-problem.txt": problem}
        if original:
            sources["original-target-source.lean"] = original.raw_text
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
            strategy_recovery=args.strategy_recovery,
            original_lean=pin,
            strategy_policy={"interval_requests": args.strategy_interval_requests,
                             "interval_seconds": args.strategy_interval_seconds,
                             "reserve_requests": args.strategy_reserve_requests,
                             "reserve_seconds": args.strategy_reserve_seconds,
                             "max_no_progress": args.strategy_max_no_progress},
        )
        if adoption:
            from .adoption import import_artifacts
            with DiscoveryStore(args.directory) as store:
                import_artifacts(store, adoption)
        return {
            "status": "ready",
            "directory": str(args.directory.resolve()),
            "model_calls": 0,
        }
    if args.discovery_command == "run":
        with DiscoveryStore(args.directory) as store:
            strategy_enabled = store.run_record().get("strategy_review") is not None
        if strategy_enabled:
            return _run_strategy_cli(args.directory)
        return asyncio.run(_run(args.directory))
    if args.discovery_command == "status":
        with DiscoveryStore(args.directory) as store:
            return store.status()
    if args.discovery_command in {"subjects", "evidence"}:
        from .strategy import StrategyController

        with DiscoveryStore(args.directory) as store:
            controller = StrategyController(store)
            if args.discovery_command == "subjects":
                return controller.snapshot()
            argument = args.argument.read_text(encoding="utf-8")
            sources = [(path.name, path.read_bytes()) for path in args.source]
            if any(len(content) > 16 * 1024 * 1024 for _, content in sources):
                raise ValueError("source exceeds 16 MiB")
            with store.atomic():
                artifacts = [store.put_artifact(content, name=name) for name, content in sources]
                return controller.request_review(args.subject, scope=args.scope, method=args.method,
                    argument=argument, artifact_ids=artifacts, author="external-operator",
                    supersedes=args.supersedes)
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
