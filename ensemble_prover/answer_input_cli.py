"""Answer discovery frontend for the ordinary Mini CLI, with bounded handoff."""

from __future__ import annotations

import argparse
import asyncio
import dataclasses
import hashlib
import json
import math
import os
import sys
import time
from pathlib import Path
from typing import TYPE_CHECKING, Any, Sequence

from .answer_input import (
    AnswerCandidate,
    AnswerTemplate,
    AnswerValidationError,
    discover_answer,
    find_answer_template,
    load_candidate,
)
from .config import LeanConfig
from .lean_runner import LeanRunner
from .lean_parser import has_infra_failure, has_timeout
from .llm_usage import CostBudgetController, metered_or_plain_call
from .nl_input import _completion_error
from .nl_lean import _GUARD, _lean_string
from .subprocess_environment import trusted_provider_worker_environment
from .theorem_project import (
    TheoremProjectRequest,
    _active_command_scope_closers,
    merge_imports,
    resolve_theorem_project,
    scan_lean_theorems,
    select_lean_theorem,
    theorem_artifact_slug,
    theorem_reusable_preamble,
    theorem_type_probe_source,
)

if TYPE_CHECKING:
    from .mini_theory import MiniTheoryLibrary


def should_discover(args: argparse.Namespace) -> bool:
    if getattr(args, "resume_from", None) or getattr(args, "putnam_file", None):
        return False
    name = str(getattr(args, "theorem_name", "") or "")
    path = str(getattr(args, "lean_file", "") or "")
    return bool(
        path
        and name
        and find_answer_template(
            Path(path).expanduser().read_bytes().decode("utf-8"), name
        )
    )


def _request(args: argparse.Namespace) -> TheoremProjectRequest:
    if getattr(args, "allow_official_answer_visibility", False):
        raise ValueError("official-answer visibility controls require --putnam-file")
    description = getattr(args, "theorem_project_description", None)
    if getattr(args, "theorem_project_description_file", None):
        description = (
            Path(args.theorem_project_description_file)
            .expanduser()
            .read_bytes()
            .decode("utf-8")
        )
    return TheoremProjectRequest(
        lean_file=Path(args.lean_file),
        theorem_name=args.theorem_name,
        project_path=Path(args.lean_project_dir),
        imports=tuple(getattr(args, "theorem_project_imports", ()) or ()),
        source_dirs=tuple(
            Path(p) for p in getattr(args, "theorem_project_source_dirs", ()) or ()
        ),
        description=description,
    ).normalized()


def _runner(
    request: TheoremProjectRequest,
    path: Path,
    *,
    timeout_s: float,
    scratch_dir: Path,
    theory_library: MiniTheoryLibrary | None = None,
):
    problem = resolve_theorem_project(dataclasses.replace(request, lean_file=path))
    cfg = LeanConfig(
        project_dir=str(request.project_path),
        scratch_dir=str(scratch_dir),
        timeout_s=timeout_s,
        backend_mode="auto",
        module_search_paths=[str(p) for p in problem.module_search_paths],
        project_imports=list(problem.project_imports),
        project_import_sources=dict(problem.project_import_sources),
        support_project_builds={
            str(p): list(targets)
            for p, targets in problem.support_project_builds.items()
        },
    )
    runner = LeanRunner(cfg)
    if theory_library is not None:
        # Match ordinary Mini preflight before the first REPL/process starts.
        theory_library.activate_lean_runner(runner)
    return runner, problem


async def validate_environment(
    request: TheoremProjectRequest,
    template: AnswerTemplate,
    *,
    timeout_s: float,
    scratch_dir: Path,
    theory_library: MiniTheoryLibrary | None = None,
) -> None:
    """Reject broken trusted inputs before spending a provider request."""
    prefix, _ = theorem_reusable_preamble(
        template.source, template.declaration, request.imports
    )
    name = ".".join(
        (*template.declaration.namespace, "_answerDiscoveryEnvironmentChecked")
    )
    source = (
        prefix
        + "\ntheorem _answerDiscoveryEnvironmentChecked : True := by trivial\n"
        + "\n".join(
            _active_command_scope_closers(
                template.source, template.declaration.declaration_start
            )
        )
        + "\n"
    )
    scratch_dir.mkdir(parents=True, exist_ok=True)
    path = scratch_dir / "Environment.lean"
    path.write_text(source, encoding="utf-8")
    runner, _ = _runner(
        dataclasses.replace(request, theorem_name=name),
        path,
        timeout_s=timeout_s,
        scratch_dir=scratch_dir,
        theory_library=theory_library,
    )
    try:
        await runner.revalidate_theorem_project_environment()
        ok, _, output = await runner.check_source_declaration_type(
            source, name, timeout_s=timeout_s
        )
        if not ok:
            raise RuntimeError(
                "original question environment validation failed:\n" + output
            )
    finally:
        await runner.aclose()


async def validate_answers(
    request: TheoremProjectRequest,
    template: AnswerTemplate,
    path: Path,
    answers: list[str],
    *,
    timeout_s: float,
    scratch_dir: Path,
    theory_library: MiniTheoryLibrary | None = None,
) -> None:
    """Parse untrusted terms before elaborating the exact substituted theorem."""
    from .mini_prover import _preflight_theorem_project_input

    # The project was checked independently before any proposal. A term can
    # still unbalance the candidate's source syntax; that is repairable model
    # output, whereas metadata/import failures from _runner remain terminal.
    try:
        select_lean_theorem(
            scan_lean_theorems(path.read_text(encoding="utf-8")), request.theorem_name
        )
    except ValueError as exc:
        raise AnswerValidationError("invalid candidate source: " + str(exc)) from exc
    runner, problem = _runner(
        request,
        path,
        timeout_s=timeout_s,
        scratch_dir=scratch_dir,
        theory_library=theory_library,
    )
    try:
        prefix, scope = theorem_reusable_preamble(
            template.source, template.declaration, request.imports
        )
        commands = "\n".join(
            "  let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term "
            + _lean_string(term)
            + " with\n"
            + "    | .ok stx => pure stx\n    | .error error => Lean.throwError error\n"
            + "  unless _nlAdmissionGuard stx do\n"
            + '    Lean.throwError "answer contains prohibited syntax"\n'
            for term in answers
        )
        check_name = ".".join(
            (*template.declaration.namespace, "_answerDiscoverySyntaxChecked")
        )
        source = (
            merge_imports(prefix, ("Lean",))
            + "\n"
            + _GUARD
            + "\n"
            + scope
            + "\nrun_cmd do\n"
            + commands
            + "\ndef _answerDiscoverySyntaxChecked : Prop := True\n"
            + "\n".join(
                _active_command_scope_closers(
                    template.source, template.declaration.declaration_start
                )
            )
            + "\n"
        )
        ok, _, diagnostic = await runner.check_source_declaration_type(
            source, check_name, timeout_s=timeout_s
        )
        if not ok:
            if has_infra_failure(diagnostic) or has_timeout(diagnostic):
                raise RuntimeError("answer syntax checker unavailable:\n" + diagnostic)
            raise AnswerValidationError(
                "answer term syntax validation failed:\n" + diagnostic
            )
        # Admission-only probe: generated names must already exist in the
        # original statement context. Otherwise Lean's autoImplicit can turn
        # an undeclared answer name into a new hypothesis (even h : False).
        # Disable it inside each generated term, not for original binders.
        strict_source = template.fill(answers, name_scope_probe=True)
        strict_declaration = select_lean_theorem(
            scan_lean_theorems(strict_source), request.theorem_name
        )
        ok, _, diagnostic = await runner.check_source_declaration_type(
            theorem_type_probe_source(
                strict_source, strict_declaration, request.imports
            ),
            strict_declaration.canonical_name,
            timeout_s=timeout_s,
        )
        if not ok:
            if has_infra_failure(diagnostic) or has_timeout(diagnostic):
                raise RuntimeError(
                    "answer name-scope checker unavailable:\n" + diagnostic
                )
            raise AnswerValidationError(
                "answer name-scope validation failed:\n" + diagnostic
            )
        try:
            await _preflight_theorem_project_input(runner, problem, timeout_s=timeout_s)
        except ValueError as exc:
            detail = str(exc)
            if (
                has_infra_failure(detail)
                or has_timeout(detail)
                or "transient infrastructure" in detail
            ):
                raise RuntimeError(detail) from exc
            if detail.startswith(
                (
                    "theorem-project source declaration elaboration failed",
                    "theorem-project target elaboration failed",
                )
            ):
                raise AnswerValidationError(detail) from exc
            raise
    finally:
        await runner.aclose()


def proof_arguments(
    argv: Sequence[str],
    *,
    lean_file: Path,
    description: Path,
    output_dir: Path,
    spent_usd: float,
    elapsed_s: float,
) -> list[str]:
    """Preserve normal provider/search flags; never reset spent global limits."""
    from .mini_prover import _build_argparser

    if any(not math.isfinite(x) or x < 0 for x in (spent_usd, elapsed_s)):
        raise ValueError("invalid consumed answer-discovery budget")
    parser = _build_argparser()
    args = parser.parse_args(list(argv))
    replacements = {
        "--lean-file": str(lean_file),
        "--description-file": str(description),
        "--output-dir": str(output_dir),
    }
    for dest, flag in (
        ("cost_budget_usd", "--cost-budget-usd"),
        ("mini_worker_timeout_s", "--mini-worker-timeout-s"),
        ("mini_run_wall_clock_budget_s", "--mini-run-wall-clock-budget-s"),
        ("mini_no_strong_progress_budget_s", "--mini-no-strong-progress-budget-s"),
    ):
        limit = float(getattr(args, dest, 0) or 0)
        if limit > 0:
            remaining = limit - (spent_usd if dest == "cost_budget_usd" else elapsed_s)
            if remaining <= 0:
                raise ValueError(f"{flag} budget exhausted during answer discovery")
            replacements[flag] = str(remaining)
    owned = {
        "lean_file",
        "output_dir",
        "theorem_project_description",
        "theorem_project_description_file",
        "answer_attempts",
    }
    owned.update(
        a.dest
        for a in parser._actions
        if any(s in replacements for s in a.option_strings)
    )
    options = {s for a in parser._actions if a.dest in owned for s in a.option_strings}
    result: list[str] = []
    index = 0
    while index < len(argv):
        arg = argv[index]
        if arg.split("=", 1)[0] in options:
            index += 1 if "=" in arg else 2
        else:
            result.append(arg)
            index += 1
    for flag, value in replacements.items():
        result.extend((flag, value))
    return result


async def _prepare(
    args: argparse.Namespace,
    request: TheoremProjectRequest,
    template: AnswerTemplate,
    directory: Path,
    *,
    started: float,
) -> tuple[AnswerCandidate, float]:
    from .mini_prover import (
        _apply_reasoning_cli_override,
        _effective_mini_theory_mode,
        _make_mini_role_client,
        _make_role_cfg,
        _reasoning_role_cli_settings,
        _resolve_llm_request_timeout_setting,
        _validate_cost_budget_pricing,
    )

    request_timeout, disabled = _resolve_llm_request_timeout_setting(
        (
            args.prover_request_timeout_s
            if args.prover_request_timeout_s is not None
            else args.llm_request_timeout_s
        ),
        role_name="prover",
    )
    cfg = _make_role_cfg(
        args.prover,
        args.prover_model,
        role_name="answer_discovery",
        timeout_s=(
            args.prover_timeout_s
            if args.prover_timeout_s is not None
            else args.llm_timeout_s
        ),
        llm_deadline_policy=args.llm_deadline_policy,
        request_timeout_s=request_timeout,
        request_timeout_disabled=disabled,
    )
    mode, effort = _reasoning_role_cli_settings(args, "prover")
    _apply_reasoning_cli_override(cfg, mode=mode, effort=effort)
    cfg.codex_binary = args.codex_bin
    cfg.claude_code_binary = args.claude_code_bin
    client = _make_mini_role_client(cfg)
    events = directory / "usage.jsonl"

    def usage(event: dict[str, Any]) -> None:
        with events.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(event, ensure_ascii=False) + "\n")

    meter = CostBudgetController(
        max_cost_usd=args.cost_budget_usd,
        reserve_output_tokens=args.cost_budget_reserve_output_tokens,
        event_sink=usage,
    )
    limits = [
        float(getattr(args, key, 0) or 0)
        for key in (
            "mini_worker_timeout_s",
            "mini_run_wall_clock_budget_s",
            "mini_no_strong_progress_budget_s",
        )
    ]
    limit = min((value for value in limits if value > 0), default=0)
    theory_library = None

    async def ask(messages: list[dict[str, Any]], phase: str) -> str:
        response = await metered_or_plain_call(
            cost_controller=meter,
            client=client,
            messages=messages,
            role="answer_discovery",
            scope="answer_input",
            call_kind="chat_raw_json_answer",
            invoke=lambda callback: client.chat_raw(
                messages, response_format="json", usage_callback=callback
            ),
        )
        text, raw = response
        error = _completion_error(raw)
        if error or bool(getattr(client, "last_truncated", False)):
            # Preserve the incomplete response as evidence, never parse a
            # partial object or quietly accept a clipped plan.
            with (directory / "incomplete_responses.jsonl").open(
                "a", encoding="utf-8"
            ) as handle:
                handle.write(
                    json.dumps(
                        {"phase": phase, "text": text, "response": raw},
                        ensure_ascii=False,
                    )
                    + "\n"
                )
            raise RuntimeError(error or "answer response was truncated")
        return text

    async def validate(path: Path, answers: list[str]) -> None:
        await validate_answers(
            request,
            template,
            path,
            answers,
            timeout_s=float(args.lean_timeout_s),
            scratch_dir=directory / ".lean_tmp",
            theory_library=theory_library,
        )

    try:
        theory_mode = _effective_mini_theory_mode(args)
        if theory_mode != "off":
            from .mini_theory import MiniTheoryLibrary

            theory_library = MiniTheoryLibrary(
                root=Path(args.mini_theory_root).expanduser(),
                lean_project_dir=request.project_path,
                mode=theory_mode,
                attempt_scope_id="run_"
                + hashlib.sha256(str(directory).encode()).hexdigest()[:16],
                verifier_timeout_s=max(1.0, float(args.mini_theory_verifier_timeout_s)),
            )
        await validate_environment(
            request,
            template,
            timeout_s=float(args.lean_timeout_s),
            scratch_dir=directory / ".lean_environment",
            theory_library=theory_library,
        )
        if callable(getattr(client, "preflight", None)):
            await client.preflight()
        await _validate_cost_budget_pricing(
            max_cost_usd=float(args.cost_budget_usd),
            role_clients=(("answer_discovery", client),),
        )
        from .mini_session.process_watchdog import signal_worker_ready

        # Startup covers environment, verified imports, provider and pricing
        # setup. Once ready, proposal/review use the ordinary run deadlines.
        signal_worker_ready()
        remaining = max(0, started + limit - time.monotonic()) if limit else None
        async with asyncio.timeout(remaining):
            candidate = await discover_answer(
                template,
                request,
                directory=directory / "answers",
                ask=ask,
                validate=validate,
                max_attempts=args.answer_attempts,
            )
    finally:
        _arm_shutdown_deadline(args)
        try:
            await client.close()
        finally:
            try:
                await meter.drain_late_usage()
                (directory / "answer_usage.json").write_text(
                    json.dumps(meter.summary(), ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                )
            finally:
                if theory_library is not None:
                    theory_library.close()
    return candidate, meter.committed_cost_usd


def run_cli(args: argparse.Namespace, argv: Sequence[str]) -> int:
    from .mini_prover import _allocate_default_mini_run_dir
    from .mini_session.process_watchdog import run_cli_worker_under_watchdog

    started = time.monotonic()
    directory: Path | None = None
    try:
        request = _request(args)
        source = request.lean_file.read_bytes().decode("utf-8")
        template = find_answer_template(source, request.theorem_name)
        if template is None:
            raise ValueError("selected theorem has no answer(sorry) slots")
        if args.output_dir:
            directory = Path(args.output_dir).expanduser().resolve()
            directory.mkdir(parents=True, exist_ok=False)
        else:
            directory = _allocate_default_mini_run_dir(
                theorem_artifact_slug(request.theorem_name) + "_answer"
            )
        print(
            f"Answer discovery: {request.theorem_name}; artifacts: {directory}",
            flush=True,
        )
        if type(args.answer_attempts) is not int or args.answer_attempts < 1:
            raise ValueError("answer attempts must be a positive integer")
        limits = [
            float(getattr(args, key, 0) or 0)
            for key in (
                "mini_worker_timeout_s",
                "mini_run_wall_clock_budget_s",
                "mini_no_strong_progress_budget_s",
            )
        ]
        limit = min((value for value in limits if value > 0), default=0)
        remaining = limit - (time.monotonic() - started) if limit else 0
        if limit and remaining <= 0:
            raise ValueError("run budget exhausted before answer preparation")
        worker_args = [*argv, "--output-dir", str(directory)]
        worker_code = run_cli_worker_under_watchdog(
            worker_args,
            worker_command=[
                sys.executable,
                "-m",
                "ensemble_prover.answer_input_cli",
                *worker_args,
            ],
            output_dir=directory,
            theorem_name=request.theorem_name,
            overall_timeout_s=remaining,
            startup_timeout_s=float(args.mini_worker_startup_timeout_s or 0),
            shutdown_timeout_s=float(args.mini_worker_shutdown_timeout_s or 0),
            hard_operation_deadlines=bool(args.mini_hard_operation_watchdog),
        )
        if worker_code != 0:
            return worker_code
        candidate = load_candidate(directory / "answers", template, request)
        accounting = json.loads((directory / "answer_usage.json").read_bytes())
        if not isinstance(accounting, dict):
            raise ValueError("invalid answer-discovery cost receipt")
        spent = accounting.get("llm_budget_committed_cost_usd")
        if type(spent) not in (int, float) or not math.isfinite(spent) or spent < 0:
            raise ValueError("invalid answer-discovery cost receipt")
        if args.cost_budget_usd and accounting.get(
            "llm_unpriced_provider_exposure_count", 0
        ):
            raise ValueError("answer-discovery budget has unpriced provider exposure")
        if (
            hashlib.sha256(candidate.lean_file.read_bytes()).hexdigest()
            != candidate.source_sha256
        ):
            raise ValueError("checked answer file changed before proof dispatch")
        child_dir = directory / "proof"
        child_args = proof_arguments(
            argv,
            lean_file=candidate.lean_file,
            description=candidate.description_path,
            output_dir=child_dir,
            spent_usd=spent,
            elapsed_s=time.monotonic() - started,
        )
        command = [sys.executable, "-m", "ensemble_prover.mini_prover", *child_args]
        (directory / "prover_command.json").write_text(
            json.dumps(command, indent=2) + "\n", encoding="utf-8"
        )
        print(
            "Candidate answer admitted, NOT proved. Starting ordinary Mini proof search.",
            flush=True,
        )
        print(
            f"If interrupted after checkpoint creation, resume with --resume-from {child_dir}",
            flush=True,
        )
        # Preserve the launched PID as Mini's actual watchdog owner. An extra
        # subprocess parent would survive cancellation of the original CLI.
        os.execve(sys.executable, command, trusted_provider_worker_environment())
    except KeyboardInterrupt:
        print(
            "Answer discovery interrupted; saved candidates and proof checkpoints are retained.",
            file=sys.stderr,
        )
        return 130
    except (OSError, ValueError, RuntimeError, TimeoutError) as exc:
        print(f"Answer discovery stopped before proof dispatch: {exc}", file=sys.stderr)
        if directory is not None:
            print(f"Artifacts: {directory}", file=sys.stderr)
        return 2


def _arm_shutdown_deadline(args: argparse.Namespace) -> None:
    """Leave the normal supervisor lease armed through asyncio teardown."""
    from .mini_session.process_watchdog import (
        begin_process_deadline,
        worker_shutdown_timeout_s,
    )

    if getattr(args, "_answer_shutdown_lease", None) is None:
        timeout = worker_shutdown_timeout_s()
        args._answer_shutdown_lease = begin_process_deadline(
            deadline_monotonic=time.monotonic() + timeout if timeout > 0 else 0,
            label="mini_session_asyncio_shutdown",
            supervisor_enforced=True,
        )


def preparation_worker_main(argv: Sequence[str] | None = None) -> int:
    """Only the existing process supervisor may own paid answer preparation."""
    from .mini_prover import _build_argparser, _install_cooperative_stop_signal_handlers
    from .mini_session.process_watchdog import is_watchdog_worker

    if not is_watchdog_worker():
        raise RuntimeError("answer preparation requires the Mini process supervisor")
    args = _build_argparser().parse_args(argv)
    request = _request(args)
    template = find_answer_template(
        request.lean_file.read_bytes().decode("utf-8"), request.theorem_name
    )
    if template is None:
        raise ValueError("answer preparation has no selected answer slots")
    directory = Path(args.output_dir).resolve()
    directory.mkdir(parents=True, exist_ok=True)

    async def prepare() -> None:
        uninstall = _install_cooperative_stop_signal_handlers([])
        try:
            await _prepare(args, request, template, directory, started=time.monotonic())
        finally:
            _arm_shutdown_deadline(args)
            uninstall()

    try:
        asyncio.run(prepare())
        return 0
    except (KeyboardInterrupt, asyncio.CancelledError):
        return 130
    except Exception as exc:
        print(f"Answer preparation failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(preparation_worker_main())
