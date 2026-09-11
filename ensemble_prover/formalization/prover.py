"""Run Mini on one frozen campaign target and retain its finalized Lean source."""

from __future__ import annotations

import asyncio
import copy
import hashlib
import json
import math
import os
from pathlib import Path
from typing import Any

from ..config import LeanConfig
from ..lean_runner import LeanRunner
from ..llm_error_policy import is_terminal_llm_failure_reason
from ..mini_prover import prove_theorem_project
from ..mini_run_recorder import RunRecorder
from ..proof_dossier import ProofDossier
from ..theorem_project import (
    TheoremProblem,
    TheoremProjectRequest,
    is_valid_lean_qualified_name,
    resolve_theorem_project,
)


_CONTEXT_MARKER = "-- ensemble-nl-input: preserve-context"


class MiniProverFailure(RuntimeError):
    """A trusted Mini terminal LLM outcome, not mathematical incompleteness."""

    def __init__(self, *, reason: str, kind: str) -> None:
        self.reason = reason
        self.kind = kind
        self.stop_reason = (
            "context_overflow"
            if reason == "llm_required_prompt_context_overflow"
            else "provider_error"
        )
        super().__init__(f"Mini proof search stopped: {reason} ({kind})")


class ProofAttemptFeedbackError(RuntimeError):
    """Attempt evidence could not be preserved; not a mathematical failure."""

    def __init__(self, *, stage: str, error_type: str) -> None:
        self.stage = stage
        self.error_type = error_type
        super().__init__(f"Proof attempt feedback unavailable: {stage} ({error_type})")


def _description(task: Any, proof_plan: str, context: dict[str, Any]) -> str:
    """Keep mathematical prose verbatim, with the structured citations alongside."""

    parts = [
        "Campaign task:\n" + str(task.description),
        "Full proof plan:\n" + proof_plan,
    ]
    required_context = context.get("required_context")
    if isinstance(required_context, dict):
        research_plan = required_context.get("proof_plan")
        if isinstance(research_plan, str):
            parts.append("Original research proof plan (verbatim):\n" + research_plan)
    seen: set[tuple[str, Any, Any, str]] = set()
    for key in ("original_source", "task_source"):
        for source in context.get(key, ()):
            text = source.get("text", "")
            citation = (
                str(source.get("document_id", "")),
                source.get("start"),
                source.get("end"),
                text,
            )
            if citation in seen:
                continue
            seen.add(citation)
            parts.append(
                f"Original mathematical source [{citation[0]}:{citation[1]}:{citation[2]}]:\n"
                + text
            )
    parts.append(
        "Campaign context and citation metadata:\n"
        + json.dumps(context, ensure_ascii=False, indent=2)
    )
    return "\n\n".join(parts)


class MiniProver:
    """Own per-attempt Mini resources; module admission belongs to the compiler.

    Campaign dependencies are already compiled and enter Lean through imports
    and a module search root. They are never copied into the theorem's prefix
    or registered as a recursively scanned supporting-source directory.
    """

    def __init__(
        self,
        project_path: Path,
        module_root: Path,
        prover_client: Any,
        refiner_client: Any = None,
        *,
        options: dict[str, Any] | None = None,
    ) -> None:
        self.project_path = Path(project_path).expanduser().resolve(strict=True)
        self.module_root = Path(module_root).expanduser().resolve()
        self.prover_client = prover_client
        self.refiner_client = refiner_client
        self.options = dict(options or {})
        self._lock = asyncio.Lock()
        self._closed = False
        self._attempt_run_dir: Path | None = None
        self._last_attempt: dict[str, Any] | None = None
        self._capture_errors: list[dict[str, str]] = []

    def read_attempt_feedback(self) -> dict[str, Any] | None:
        """Return exact private attempt evidence, never proof-admission authority.

        Text is decoded from the original bytes without newline normalization.
        The snapshot is taken after recorder/Lean cleanup, including unsuccessful
        and interrupted attempts. Missing/unreadable artifacts are explicit;
        symlinks are never followed. No mathematical text is shortened.
        """
        return copy.deepcopy(self._last_attempt)

    def _capture_attempt_feedback(self, *, task_id: str, status: str) -> None:
        directory = self._attempt_run_dir
        if directory is None:
            return
        artifacts: list[dict[str, Any]] = []
        unavailable: list[dict[str, str]] = []

        def walk_error(exc: OSError) -> None:
            unavailable.append({"path": ".", "error_type": type(exc).__name__})

        for parent, directories, names in os.walk(
            directory, followlinks=False, onerror=walk_error
        ):
            for name in list(directories):
                path = Path(parent) / name
                if path.is_symlink():
                    directories.remove(name)
                    unavailable.append(
                        {"path": str(path.relative_to(directory)),
                         "error_type": "symlink_not_followed"}
                    )
            for name in sorted(names):
                path = Path(parent) / name
                if path.suffix not in {".json", ".jsonl", ".lean"}:
                    continue
                relative = str(path.relative_to(directory))
                if path.is_symlink():
                    unavailable.append(
                        {"path": relative, "error_type": "symlink_not_followed"}
                    )
                    continue
                try:
                    content = path.read_bytes()
                    text = content.decode("utf-8")
                except (OSError, UnicodeError) as exc:
                    unavailable.append(
                        {"path": relative, "error_type": type(exc).__name__}
                    )
                    continue
                artifacts.append(
                    {"path": relative, "sha256": hashlib.sha256(content).hexdigest(),
                     "text": text}
                )
        self._last_attempt = {
            "schema": 1,
            "task_id": task_id,
            "run_dir": str(directory),
            "status": status,
            "complete": not unavailable and not self._capture_errors,
            "artifacts": artifacts,
            "unavailable": unavailable,
            "capture_errors": list(self._capture_errors),
        }

    async def close(self) -> None:
        """Wait for the current attempt's cleanup, without closing shared clients."""

        async with self._lock:
            self._closed = True

    async def prove(
        self,
        *,
        task: Any,
        name: str,
        statement: str,
        proof_plan: str,
        preamble: str,
        context: dict[str, Any],
        run_dir: Path,
    ) -> str | None:
        async with self._lock:
            if self._closed:
                raise RuntimeError("MiniProver is closed")
            self._attempt_run_dir = None
            self._last_attempt = None
            self._capture_errors = []
            status = "error"
            primary_failure = False
            try:
                source = await self._prove(
                    task=task,
                    name=name,
                    statement=statement,
                    proof_plan=proof_plan,
                    preamble=preamble,
                    context=context,
                    run_dir=run_dir,
                )
                status = "solved" if source is not None else "unsolved"
                return source
            except BaseException as exc:
                primary_failure = True
                if isinstance(exc, MiniProverFailure):
                    status = "terminal"
                elif isinstance(exc, asyncio.CancelledError):
                    status = "cancelled"
                raise
            finally:
                try:
                    self._capture_attempt_feedback(task_id=task.id, status=status)
                except BaseException as exc:
                    self._capture_errors.append(
                        {"stage": "snapshot", "error_type": type(exc).__name__}
                    )
                    self._last_attempt = {
                        "schema": 1, "task_id": task.id,
                        "run_dir": str(self._attempt_run_dir or run_dir),
                        "status": status, "complete": False, "artifacts": [],
                        "unavailable": [], "capture_errors": list(self._capture_errors),
                    }
                    if not primary_failure:
                        if not isinstance(exc, Exception):
                            raise
                        raise ProofAttemptFeedbackError(
                            stage="snapshot", error_type=type(exc).__name__
                        ) from exc

    async def _prove(
        self,
        *,
        task: Any,
        name: str,
        statement: str,
        proof_plan: str,
        preamble: str,
        context: dict[str, Any],
        run_dir: Path,
    ) -> str | None:
        if not is_valid_lean_qualified_name(name):
            raise ValueError("invalid theorem name")
        timeout_s = float(self.options.get("lean_timeout_s", 300))
        if not math.isfinite(timeout_s) or timeout_s <= 0:
            raise ValueError("Mini Lean timeout must be finite and positive")
        run_dir = Path(run_dir).expanduser().resolve()
        # Every claim token owns a new directory. Reusing one would truncate
        # its recorder and replace the previous attempt's immutable evidence.
        run_dir.mkdir(parents=True, exist_ok=False)
        self._attempt_run_dir = run_dir
        self.module_root.mkdir(parents=True, exist_ok=True)
        if _CONTEXT_MARKER not in {line.strip() for line in preamble.splitlines()}:
            preamble = preamble.rstrip() + "\n" + _CONTEXT_MARKER + "\n"
        description = _description(task, proof_plan, context)
        lean_file = run_dir / "Target.lean"
        lean_file.write_text(
            preamble.rstrip() + f"\n\ntheorem {name} : ({statement}) := by\n  sorry\n",
            encoding="utf-8",
        )
        request = TheoremProjectRequest(
            lean_file=lean_file,
            theorem_name=name,
            project_path=self.project_path,
            description=description,
        )
        # Match the public API's local-project import provenance requirements.
        # The campaign module root deliberately is not request.source_dirs.
        problem = resolve_theorem_project(request)
        runner = LeanRunner(
            LeanConfig(
                project_dir=str(self.project_path),
                scratch_dir=str(run_dir / "checks"),
                timeout_s=math.ceil(timeout_s),
                max_parallel=1,
                backend_mode="lake",
                module_search_paths=[
                    str(self.module_root),
                    *(str(path) for path in problem.module_search_paths),
                ],
                project_imports=list(problem.project_imports),
                project_import_sources=dict(problem.project_import_sources),
                support_project_builds={
                    str(project): list(targets)
                    for project, targets in problem.support_project_builds.items()
                },
            )
        )
        dossier: ProofDossier | None = None
        recorder: RunRecorder | None = None
        finalized = False
        terminal_failure: MiniProverFailure | None = None
        primary_failure = False

        def make_dossier(prepared: TheoremProblem) -> ProofDossier:
            nonlocal dossier, problem
            problem = prepared
            dossier = ProofDossier(
                theorem_name=prepared.theorem_name,
                root_statement=prepared.statement_type,
                problem_text=prepared.docstring,
                suppress_solution_placeholders=False,
            )
            return dossier

        try:
            recorder = RunRecorder(run_dir, task_local_console=True)
            ok, _reply = await prove_theorem_project(
                request=request,
                prover_client=self.prover_client,
                refiner_client=self.refiner_client,
                lean=runner,
                recorder=recorder,
                dossier_factory=make_dossier,
                **self.options,
            )
            finalized = bool(
                ok
                and dossier is not None
                and dossier.theorem_name == problem.theorem_name
                and dossier.root_statement == problem.statement_type
                and dossier.has_root_proof_finalization_receipt()
            )
            if not finalized or dossier is None:
                # Session/factory code carries these structured fields across
                # dossier clones. Neither assistant prose nor failed Lean
                # proofs are provider-failure authority. A finalized proof
                # above takes precedence over any earlier failed attempt.
                reason = str(getattr(dossier, "session_failure_reason", "") or "")
                if is_terminal_llm_failure_reason(reason):
                    terminal_failure = MiniProverFailure(
                        reason=reason,
                        kind=str(getattr(dossier, "session_failure_kind", "") or ""),
                    )
                    raise terminal_failure
                return None
            # Mini's finalized replay list already contains the required local
            # helper closure in dependency order. Raw provider text has no
            # role here. The campaign independently compiles the whole source
            # and checks this exact requested target before admitting it.
            source = "\n\n".join(
                [
                    preamble.rstrip(),
                    *dossier.final_replay_helpers,
                    f"theorem {name} : ({statement}) := {dossier.final_proof}",
                ]
            ) + "\n"
            (run_dir / "Proof.lean").write_text(source, encoding="utf-8")
            return source
        except BaseException:
            primary_failure = True
            raise
        finally:
            secondary_failure: BaseException | None = None

            def record_secondary(stage: str, exc: BaseException) -> None:
                nonlocal secondary_failure
                if secondary_failure is None:
                    secondary_failure = exc
                self._capture_errors.append(
                    {"stage": stage, "error_type": type(exc).__name__}
                )

            try:
                if dossier is not None:
                    (run_dir / "dossier.json").write_text(
                        json.dumps(dossier.to_record(), ensure_ascii=False, indent=2)
                        + "\n",
                        encoding="utf-8",
                    )
                if recorder is not None:
                    recorder.write_summary(
                        {
                            "task_id": task.id,
                            "theorem_name": name,
                            "theorem_project": problem.theorem_project_record(),
                            "session_root_finalized": finalized,
                            "mini_terminal_failure": (
                                {
                                    "reason": terminal_failure.reason,
                                    "kind": terminal_failure.kind,
                                }
                                if terminal_failure is not None
                                else None
                            ),
                            "campaign_module_verification_pending": finalized,
                            "final_proof": dossier.final_proof if finalized else None,
                            "final_replay_helpers": (
                                dossier.final_replay_helpers if finalized else []
                            ),
                        }
                    )
            except BaseException as exc:
                record_secondary("attempt_records", exc)
            try:
                if recorder is not None:
                    recorder.close()
            except BaseException as exc:
                record_secondary("recorder_close", exc)
            try:
                await runner.aclose()
            except BaseException as exc:
                record_secondary("lean_close", exc)
            if secondary_failure is not None and not primary_failure:
                if not isinstance(secondary_failure, Exception):
                    raise secondary_failure
                raise ProofAttemptFeedbackError(
                    stage=self._capture_errors[0]["stage"],
                    error_type=type(secondary_failure).__name__,
                ) from secondary_failure
