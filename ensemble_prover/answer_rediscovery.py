"""Explicit, source-bound answer correction after a certified candidate refutation.

Recovery starts a fresh supervised generation when the operator passes
``--rediscover-from``. It never reruns a failed proof automatically or restores
proof-search state belonging to the disproved candidate.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import math
import re
import shlex
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Sequence

from .answer_input import (
    AnswerCandidate, AnswerTemplate, find_answer_template, load_candidate,
)
from .mini_falsification.model import authoritative_certificate_record_is_valid
from .theorem_project import TheoremProjectRequest, resolve_theorem_project


@dataclass(frozen=True)
class RefutedAnswer:
    run_dir: Path
    request: TheoremProjectRequest
    template: AnswerTemplate
    candidate: AnswerCandidate
    certificate: dict[str, Any]
    helpers: tuple[str, ...]
    summary: dict[str, Any]
    proof_argv: tuple[str, ...]
    putnam: bool
    worker_elapsed_s: float | None


def _object(path: Path) -> dict[str, Any]:
    from .mini_session.durable_checkpoint import read_checkpoint_record

    return read_checkpoint_record(path)


def _saved_arguments(parser: argparse.ArgumentParser, argv: Sequence[str]) -> argparse.Namespace:
    # A malformed receipt must not terminate an otherwise ordinary supervisor
    # through argparse's SystemExit, or print its contents in an advisory path.
    try:
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return parser.parse_args(list(argv))
    except SystemExit as exc:
        raise ValueError("invalid saved proof command arguments") from exc


def _checkpoint(directory: Path, *, current: bool) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Read one immutable checkpoint without taking over its attempt registry."""
    from .mini_session.attempt_checkpoint import AttemptCheckpointRegistry, _digest, _read

    if not (directory / "attempt_checkpoint.json").exists():
        return None
    manifest = AttemptCheckpointRegistry._load_manifest(directory)
    head = manifest["head"]
    if (
        not isinstance(manifest["identity"], dict)
        or not isinstance(head["generation_id"], str)
        or not re.fullmatch(r"[0-9a-f]{32}", head["generation_id"])
        or not isinstance(head["snapshot_hash"], str)
        or not re.fullmatch(r"[0-9a-f]{64}", head["snapshot_hash"])
        or (current and _read(Path(manifest["registry_root"]) / "head.json") != head)
    ):
        raise ValueError("rediscovery requires the latest committed attempt generation")
    snapshot = _read(Path(head["snapshot_path"]))
    if (
        _digest(snapshot) != head["snapshot_hash"]
        or snapshot.get("identity") != manifest["identity"]
        or snapshot.get("attempt_id") != manifest["attempt_id"]
        or type(snapshot.get("schema_version")) is not int
        or snapshot["schema_version"] not in (1, 2)
    ):
        raise ValueError("invalid candidate generation checkpoint binding")
    return manifest, snapshot


def _generation_clock(run_dir: Path, original_run: Path, candidate: AnswerCandidate,
                      request: TheoremProjectRequest, source_statement: str) -> float | None:
    checkpoint = _checkpoint(run_dir, current=True)
    if checkpoint is None:
        if run_dir != original_run:
            raise ValueError("resumed candidate has no authenticated generation lineage")
        return None
    manifest, snapshot = checkpoint
    if snapshot.get("worker_generation_completed") is not True:
        raise ValueError("candidate worker has no completed clock receipt")
    elapsed = _nonnegative(snapshot.get("worker_active_elapsed_s"), "worker-clock")
    _nonnegative(snapshot.get("worker_observed_epoch_s"), "worker-observation")
    expected_input = {
        "source_path": str(candidate.lean_file.resolve()),
        "source_sha256": candidate.source_sha256,
        "theorem_name": request.theorem_name,
        "statement_type": source_statement,
    }
    identity = dict(manifest["identity"])
    identity.pop("executor_source_hash", None)
    visited: set[Path] = set()
    directory = run_dir
    while True:
        generation_identity = dict(manifest["identity"])
        generation_identity.pop("executor_source_hash", None)
        if generation_identity != identity or generation_identity.get("input") != expected_input:
            raise ValueError("candidate checkpoint identity differs from the admitted question")
        if directory == original_run:
            return elapsed
        predecessor = snapshot.get("predecessor")
        if not isinstance(predecessor, str) or not Path(predecessor).is_absolute():
            raise ValueError("candidate checkpoint does not descend from its proof command")
        visited.add(directory)
        directory = Path(predecessor).resolve()
        if directory in visited:
            raise ValueError("invalid candidate checkpoint predecessor chain")
        previous = _checkpoint(directory, current=False)
        if previous is None:
            raise ValueError("candidate checkpoint predecessor is missing")
        previous_manifest, snapshot = previous
        if any(previous_manifest[key] != manifest[key] for key in ("attempt_id", "registry_root")):
            raise ValueError("candidate checkpoint predecessor belongs to another attempt")
        manifest = previous_manifest


def load_refuted_answer(run_dir: Path) -> RefutedAnswer:
    """Validate persisted provenance; Lean authority is replayed in the worker."""
    from .answer_input_cli import _request
    from .mini_prover import _build_argparser
    from .putnam_answer_input import find_putnam_answer_template

    run_dir = Path(run_dir).expanduser().resolve()
    summary = _object(run_dir / "summary.json")
    certificate = summary.get("root_disproof_certificate")
    dossier = summary.get("proof_dossier")
    barrier = summary.get("cancellation_barrier") or {}
    abandoned = barrier.get("abandoned_tasks") if isinstance(barrier, dict) else None
    if (
        summary.get("solved") is not False
        or summary.get("disproved") is not True
        or summary.get("failure_reason") != "root_disproved_by_audited_lean_certificate"
        or not isinstance(dossier, dict)
        or not isinstance(certificate, dict)
        or not authoritative_certificate_record_is_valid(certificate)
        or dossier.get("root_disproof_certificate") != certificate
        or dossier.get("root_statement") != certificate.get("statement")
        or not isinstance(barrier, dict)
        or not all(barrier.get(key) is True for key in (
            "barrier_ran", "lean_closed", "lean_quiesced", "theory_closed",
        ))
        or not isinstance(abandoned, dict) or type(abandoned.get("still_pending")) is not int
        or abandoned["still_pending"] != 0
        or summary.get("llm_transport_quiescent_before_summary") is not True
    ):
        raise ValueError("rediscovery requires a settled, certified root refutation")
    project = summary.get("theorem_project")
    if not isinstance(project, dict) or not isinstance(project.get("lean_file"), str):
        raise ValueError("refuted candidate has no source provenance")
    candidate_path = Path(project["lean_file"]).expanduser().resolve()
    directory = candidate_path.parent
    record = _object(directory / "answer_discovery.json")
    origin = record.get("input_request")
    if (
        not isinstance(origin, dict)
        or any(not isinstance(origin.get(key), str) or not origin[key]
               for key in ("lean_file", "theorem_name", "project_path"))
        or any(not isinstance(origin.get(key), list)
               or any(not isinstance(item, str) for item in origin[key])
               for key in ("imports", "source_dirs"))
        or "description" not in origin
        or (origin["description"] is not None and not isinstance(origin["description"], str))
    ):
        raise ValueError("refuted candidate has no original question")
    try:
        request = TheoremProjectRequest(
            lean_file=Path(origin["lean_file"]), theorem_name=origin["theorem_name"],
            project_path=Path(origin["project_path"]), imports=tuple(origin["imports"]),
            source_dirs=tuple(Path(p) for p in origin["source_dirs"]),
            description=origin["description"],
        ).normalized()
    except (KeyError, TypeError) as exc:
        raise ValueError("invalid original question receipt") from exc
    try:
        command = json.loads((directory.parent / "prover_command.json").read_bytes())
    except (UnicodeError, RecursionError) as exc:
        raise ValueError("invalid original proof command receipt") from exc
    if (
        not isinstance(command, list) or len(command) < 4
        or not all(isinstance(item, str) for item in command)
        or command[1:3] != ["-m", "ensemble_prover.mini_prover"]
    ):
        raise ValueError("missing original proof command")
    proof_argv = tuple(command[3:])
    args = _saved_arguments(_build_argparser(), proof_argv)
    if args.resume_from or args.rediscover_from or not args.output_dir:
        raise ValueError("proof command does not own this candidate generation")
    original_run = Path(args.output_dir).resolve()
    putnam = bool(args.putnam_file)
    source = request.lean_file.read_text(encoding="utf-8")
    template = (
        find_putnam_answer_template(source, request.theorem_name)
        if putnam else find_answer_template(source, request.theorem_name)
    )
    if template is None:
        raise ValueError("original question no longer has supported answer slots")
    candidate = load_candidate(directory, template, request)
    proof_request = _request(args)
    if (
        candidate.lean_file.resolve() != candidate_path
        or project.get("source_sha256") != candidate.source_sha256
        or project.get("theorem_name") != request.theorem_name
        or project.get("elaborated_statement_type") != certificate.get("statement")
        or proof_request.lean_file != candidate_path
        or proof_request.theorem_name != request.theorem_name
        or proof_request.project_path != request.project_path
        or proof_request.imports != request.imports
        or proof_request.source_dirs != request.source_dirs
    ):
        raise ValueError("refutation source differs from the admitted candidate")
    current_project = resolve_theorem_project(
        replace(request, lean_file=candidate_path)
    ).theorem_project_record()
    environment_fields = (
        "project_path", "project_input_hash", "project_source_input_hash", "imports",
        "module_search_paths", "project_imports", "project_import_sources",
        "support_project_builds", "source_dirs",
    )
    if any(key not in project or project[key] != current_project[key] for key in environment_fields):
        raise ValueError("refuted candidate project or supporting source environment changed")
    helpers = dossier.get("verified_helpers")
    if not isinstance(helpers, list) or any(not isinstance(item, dict) for item in helpers):
        raise ValueError("invalid refutation helper receipt")
    # Checkpoints bind the source form before preflight canonicalizes the
    # target. Certificate authority is independently bound to the elaborated
    # form above and checked again by fresh Lean replay in the worker.
    worker_elapsed = _generation_clock(
        run_dir, original_run, candidate, request, current_project["source_statement_type"],
    )
    return RefutedAnswer(
        run_dir, request, template, candidate, dict(certificate),
        tuple(str(item.get("source") or "") for item in helpers),
        summary, proof_argv, putnam, worker_elapsed,
    )


def _nonnegative(value: Any, label: str) -> float:
    if type(value) not in (int, float):
        raise ValueError(f"invalid prior {label} accounting")
    try:
        number = float(value)
    except (ValueError, OverflowError) as exc:
        raise ValueError(f"invalid prior {label} accounting") from exc
    if not math.isfinite(number) or number < 0:
        raise ValueError(f"invalid prior {label} accounting")
    return number


def _without_options(argv: Sequence[str], parser: argparse.ArgumentParser,
                     destinations: set[str]) -> list[str]:
    result: list[str] = []
    retain = True
    for token in argv:
        parsed = parser._parse_optional(token)
        if parsed is not None and parsed[0] is not None:
            retain = parsed[0].dest not in destinations
        if retain:
            result.append(token)
    return result


def rediscovery_arguments(prior: RefutedAnswer, argv: Sequence[str]) -> list[str]:
    """Restore search settings while conserving already debited global limits."""
    from .mini_prover import _build_argparser

    parser = _build_argparser()
    old = _saved_arguments(parser, prior.proof_argv)
    explicit_parser = _build_argparser()
    explicit_parser._defaults.clear()
    for action in explicit_parser._actions:
        action.default = argparse.SUPPRESS
    explicit = vars(explicit_parser.parse_args(list(argv)))
    frozen = {
        "lean_file", "putnam_file", "theorem_name", "lean_project_dir",
        "theorem_project_imports", "theorem_project_source_dirs",
        "theorem_project_description", "theorem_project_description_file",
        "resume_from", "opaque_mode", "allow_official_answer_visibility",
        "answer_refutation_from", "resume_accept_source_hash", "mini_theory_startup_overlay_nonce",
    }
    if frozen.intersection(explicit):
        raise ValueError("rediscovery cannot override the bound question or answer visibility")
    wall = _nonnegative(prior.summary.get("wall_clock_s"), "wall-clock")
    if prior.worker_elapsed_s is not None:
        wall = max(wall, prior.worker_elapsed_s)
    cost = _nonnegative(prior.summary.get("llm_budget_committed_cost_usd"), "cost")
    limits = {
        "cost_budget_usd": "--cost-budget-usd",
        "mini_worker_timeout_s": "--mini-worker-timeout-s",
        "mini_run_wall_clock_budget_s": "--mini-run-wall-clock-budget-s",
        "mini_no_strong_progress_budget_s": "--mini-no-strong-progress-budget-s",
    }
    replacements: list[str] = []
    for dest, flag in limits.items():
        previous_limit = _nonnegative(float(getattr(old, dest, 0) or 0), dest)
        operator_limit = _nonnegative(float(explicit.get(dest, 0) or 0), dest)
        inactivity_window = dest == "mini_no_strong_progress_budget_s"
        if (
            dest != "cost_budget_usd" and not inactivity_window
            and (previous_limit or operator_limit) and prior.worker_elapsed_s is None
        ):
            raise ValueError("time-bounded rediscovery requires a completed worker clock receipt")
        if dest == "cost_budget_usd" and (previous_limit or operator_limit) and (
            prior.summary.get("llm_cost_accounting_incomplete") is not False
            or prior.summary.get("llm_unpriced_provider_exposure_count") != 0
        ):
            raise ValueError("prior provider exposure is not fully priced; cost-bounded rediscovery unavailable")
        # A certified root refutation is progress. Productive proof search can
        # exceed this inactivity window many times without exhausting it.
        consumed = 0.0 if inactivity_window else (cost if dest == "cost_budget_usd" else wall)
        remaining = previous_limit - consumed
        if previous_limit and remaining <= 0:
            raise ValueError(f"{flag} exhausted by the refuted candidate")
        effective = min(remaining, operator_limit) if previous_limit and operator_limit else (
            remaining if previous_limit else operator_limit
        )
        if effective:
            replacements.extend((flag, str(effective)))
    owned = (frozen - {"opaque_mode", "allow_official_answer_visibility"}) | set(limits) | set(explicit) | {
        "output_dir", "answer_attempts", "rediscover_from", "answer_refutation_from",
    }
    base = _without_options(prior.proof_argv, parser, owned)
    overrides = _without_options(argv, parser, set(limits) | {"rediscover_from"})
    question = ["--putnam-file" if prior.putnam else "--lean-file", str(prior.request.lean_file),
                "--theorem-name", prior.request.theorem_name,
                "--project-path", str(prior.request.project_path)]
    for value in prior.request.imports:
        question.extend(("--import", value))
    for value in prior.request.source_dirs:
        question.extend(("--source-dir", str(value)))
    # An explicitly empty description is a distinct, normalized request value
    # ("" vs None) and must survive the round trip to the rediscovery worker.
    if prior.request.description is not None:
        question.extend(("--description", prior.request.description))
    return [*base, *overrides, *question, *replacements,
            "--answer-refutation-from", str(prior.run_dir)]


async def verify_refutation(prior: RefutedAnswer, *, timeout_s: float, scratch_dir: Path,
                            theory_library: Any = None) -> str:
    """Freshly replay against the exact candidate in the answer-safe context."""
    from .answer_input_cli import _runner
    from .mini_falsification import CounterexampleCandidate, FalsificationPolicy
    from .mini_falsification.certificate import certify_negation_proof_result
    from .mini_prover import _preflight_theorem_project_input

    runner, problem = _runner(prior.request, prior.candidate.lean_file,
                              timeout_s=timeout_s, scratch_dir=scratch_dir,
                              theory_library=theory_library)
    try:
        problem = await _preflight_theorem_project_input(runner, problem, timeout_s=timeout_s)
        if problem.statement_type != prior.certificate["statement"]:
            raise ValueError("refutation target differs from the freshly elaborated candidate")
        result = await certify_negation_proof_result(
            runner, statement=problem.statement_type,
            proof=prior.certificate["proof_code"],
            candidate=CounterexampleCandidate(engine="answer_rediscovery", explanation="prior candidate refutation"),
            preamble=problem.lean_preamble, helpers=prior.helpers,
            policy=FalsificationPolicy(operation_timeout_s=timeout_s, engine_timeout_s=timeout_s),
        )
        if not result.authoritative:
            raise ValueError("prior candidate refutation failed fresh Lean replay and axiom audit: " + result.reason)
    finally:
        await runner.aclose()
    def display(value: str, limit: int) -> str:
        return value if len(value) <= limit else value[:limit] + "\n[Display truncated; exact artifact retained in prior run.]"

    return (
        "The following previous candidate for this exact original question was refuted "
        "by fresh Lean replay and independent axiom audit. Investigate a different answer.\n"
        + "Previous answers: " + display(json.dumps(prior.candidate.answers, ensure_ascii=False), 2000)
        + "\nRefuted target: " + display(problem.statement_type, 2000)
        + "\nChecked negation proof:\n" + display(prior.certificate["proof_code"], 4000)
    )


def run_rediscovery(argv: Sequence[str]) -> int:
    from .answer_input_cli import run_cli
    from .mini_prover import _build_argparser

    try:
        parser = _build_argparser()
        supplied = parser.parse_args(list(argv))
        prior = load_refuted_answer(Path(supplied.rediscover_from))
        rebound = rediscovery_arguments(prior, argv)
        args = parser.parse_args(rebound)
        args._answer_rediscovery_rebound = True
        return run_cli(args, rebound)
    except (OSError, ValueError, TypeError) as exc:
        print(f"Answer rediscovery rejected: {exc}", file=sys.stderr, flush=True)
        return 2


def recovery_command(run_dir: Path) -> str:
    """Return an explicit action only for a source-bound refuted candidate."""
    try:
        load_refuted_answer(run_dir)
    except (OSError, ValueError, TypeError):
        return ""
    return shlex.join([sys.executable, "-m", "ensemble_prover.mini_prover",
                       "--rediscover-from", str(Path(run_dir).resolve())])
