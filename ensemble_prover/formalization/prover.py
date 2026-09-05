"""Run Mini on one frozen campaign target and retain its finalized Lean source."""

from __future__ import annotations

import asyncio
import json
import math
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


def _description(task: Any, proof_plan: str, context: dict[str, Any]) -> str:
    """Keep mathematical prose verbatim, with the structured citations alongside."""

    parts = [
        "Campaign task:\n" + str(task.description),
        "Full proof plan:\n" + proof_plan,
    ]
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
            return await self._prove(
                task=task,
                name=name,
                statement=statement,
                proof_plan=proof_plan,
                preamble=preamble,
                context=context,
                run_dir=run_dir,
            )

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
            recorder = RunRecorder(run_dir)
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
        finally:
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
            finally:
                try:
                    if recorder is not None:
                        recorder.close()
                finally:
                    await runner.aclose()
