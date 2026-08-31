"""Orchestration and trust enforcement for all falsification engines."""

from __future__ import annotations

from functools import lru_cache
import hashlib
import importlib
import importlib.metadata
import inspect
import time
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any, Callable, Sequence

from ..deadline_guard import await_with_strict_deadline
from ..falsification_cursor_identity import (
    RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS,
    make_right_pi_oversized_recipe_repair_disposition,
    make_right_pi_recipe_repair_disposition,
    right_pi_candidate_record_is_persistable,
    right_pi_recipe_repair_disposition_is_valid,
)
from .certificate import certify_candidate_result
from .engine import FalsificationContext, FalsificationEngine
from .generators import leading_forall_binders
from .lean_check import safe_helper_sources
from .lane_planner import advance_lane_cursor, plan_falsification_lanes
from .model import (
    FalsificationFinding,
    FalsificationOutcome,
    FalsificationReport,
    TargetKind,
    candidate_from_record,
    content_hash,
)
from .policy import FalsificationPolicy
from .registry import select_engines


FALSIFICATION_ENGINE_SCHEMA_VERSION = 10


def _exhausted_right_pi_recipe_finding(
    *,
    statement: str,
    environment_hash: str,
    cursor: dict[str, Any],
) -> FalsificationFinding | None:
    """Return preserved evidence without replaying a known-broken recipe."""

    disposition = cursor.get("recipe_repair_disposition")
    if (
        not right_pi_recipe_repair_disposition_is_valid(
            disposition,
            statement=statement,
            environment_hash=environment_hash,
            cursor=cursor,
        )
        or dict(disposition).get("status") != "exhausted"
    ):
        return None
    candidate_record = dict(dict(disposition).get("candidate") or {})
    candidate = candidate_from_record(candidate_record)
    return FalsificationFinding(
        engine="function",
        outcome=FalsificationOutcome.REFUTED,
        reason=(
            "preserved Lean-checked right-Pi candidate; identical generated "
            "full-negation recipe repair is durably exhausted"
        ),
        candidates=(candidate,),
        checks_run=0,
        cursor=dict(cursor),
        error_kind="certificate_recipe_exhausted",
    )


def _file_identity(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {"path": "", "sha256": ""}
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError:
        return {"path": str(path), "sha256": "unreadable"}
    return {"path": str(path), "sha256": digest.hexdigest()}


@lru_cache(maxsize=1)
def _runtime_dependency_identities() -> dict[str, Any]:
    """Capture optional solver/catalog identities without requiring them."""

    packages: dict[str, str] = {}
    for name in ("z3-solver", "cvc5", "networkx"):
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = "unavailable"
    binaries: dict[str, dict[str, Any]] = {}
    for name in ("z3", "cvc5"):
        path = Path(sys.executable).resolve().parent / name
        binaries[name] = _file_identity(path)
    runtimes: dict[str, str] = {}
    native_modules: dict[str, dict[str, str]] = {}
    for name in ("z3", "cvc5", "networkx"):
        try:
            module = importlib.import_module(name)
            if name == "z3":
                runtimes[name] = str(module.get_version_string())
                module_path = Path(str(module.__file__ or "")).parent
                artifacts = sorted((module_path / "lib").glob("libz3.*"))
                artifact = artifacts[0] if artifacts else Path()
            elif name == "cvc5":
                runtimes[name] = str(module.Solver().getVersion())
                artifact = Path(str(module.__file__ or ""))
            else:
                runtimes[name] = str(module.__version__)
                artifact = Path(str(module.__file__ or ""))
            native_modules[name] = _file_identity(artifact)
        except Exception as exc:
            runtimes[name] = f"unavailable:{type(exc).__name__}"
            native_modules[name] = {"path": "", "sha256": ""}
    return {
        "packages": packages,
        "runtimes": runtimes,
        "binaries": binaries,
        "native_modules": native_modules,
    }


def build_local_sequent(statement: str, hypotheses: Sequence[str]) -> str:
    target = str(statement or "").strip()
    premises = tuple(str(item).strip() for item in hypotheses if str(item).strip())
    if not premises:
        return target
    implication = " → ".join(f"({item})" for item in premises)
    binders, body = leading_forall_binders(target)
    if binders:
        binder_text = " ".join(
            f"({binder.name} : {binder.type_text})" for binder in binders
        )
        return f"∀ {binder_text}, {implication} → ({body})"
    return f"{implication} → ({target})"


def falsification_environment_hash(
    *,
    preamble: str,
    helpers: Sequence[Any],
    policy: FalsificationPolicy,
    lean: Any = None,
) -> str:
    cfg = getattr(lean, "cfg", None)
    project_dir = str(getattr(cfg, "project_dir", "") or "").strip()
    version_files: dict[str, str] = {}
    if project_dir:
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean"):
            try:
                version_files[name] = (Path(project_dir) / name).read_text(
                    encoding="utf-8"
                )
            except OSError:
                version_files[name] = ""
    return content_hash(
        {
            "preamble": str(preamble or ""),
            "helpers": safe_helper_sources(helpers),
            "policy_hash": policy.policy_hash,
            "lean_config": {
                "project_dir": project_dir,
                "preamble_import": str(getattr(cfg, "preamble_import", "") or ""),
                "extra_imports": tuple(getattr(cfg, "extra_imports", ()) or ()),
                "module_search_paths": tuple(
                    getattr(cfg, "module_search_paths", ()) or ()
                ),
                "resolved_lean_path": str(getattr(cfg, "resolved_lean_path", "") or ""),
                "resolved_lean_executable": str(
                    getattr(cfg, "resolved_lean_executable", "") or ""
                ),
            },
            "version_files": version_files,
            "python_version": sys.version,
            "runtime_dependencies": _runtime_dependency_identities(),
            "engine_schema_version": FALSIFICATION_ENGINE_SCHEMA_VERSION,
        }
    )


class FalsificationService:
    def __init__(
        self,
        *,
        policy: FalsificationPolicy | None = None,
        engines: Sequence[FalsificationEngine] | None = None,
    ) -> None:
        self.policy = policy or FalsificationPolicy()
        self.engines = (
            tuple(engines)
            if engines is not None
            else select_engines(self.policy.engines)
        )

    async def falsify(
        self,
        lean: Any,
        *,
        statement: str,
        target_kind: TargetKind = TargetKind.HELPER,
        preamble: str = "",
        helpers: Sequence[Any] = (),
        local_hypotheses: Sequence[str] = (),
        cursors: dict[str, dict[str, Any]] | None = None,
        _aggregate_deadline_monotonic: float = 0.0,
    ) -> FalsificationReport:
        invocation_started = time.monotonic()
        effective_statement = str(statement or "").strip()
        if local_hypotheses:
            effective_statement = build_local_sequent(
                effective_statement, local_hypotheses
            )
            if effective_statement:
                target_kind = TargetKind.LOCAL_SEQUENT
        environment_hash = falsification_environment_hash(
            preamble=preamble,
            helpers=helpers,
            policy=self.policy,
            lean=lean,
        )
        if not self.policy.enabled or not effective_statement:
            return FalsificationReport(
                effective_statement,
                target_kind,
                (),
                policy_hash=self.policy.policy_hash,
                environment_hash=environment_hash,
            )
        findings: list[FalsificationFinding] = []
        invocation_deadline = invocation_started + self.policy.aggregate_timeout_s
        if _aggregate_deadline_monotonic > 0.0:
            invocation_deadline = min(
                invocation_deadline,
                float(_aggregate_deadline_monotonic),
            )
        lanes = plan_falsification_lanes(
            self.engines,
            statement=effective_statement,
            preamble=preamble,
            cursors=cursors,
        )
        lane_outcomes: dict[str, FalsificationOutcome] = {}
        for lane in lanes:
            engine = lane.engine
            if lane.fallback_for and lane_outcomes.get(lane.fallback_for) not in {
                FalsificationOutcome.UNSUPPORTED,
                FalsificationOutcome.TRANSIENT_FAILURE,
            }:
                continue
            if time.monotonic() >= invocation_deadline:
                deferred_cursor = dict((cursors or {}).get(engine.name) or {})
                if lane.rotating:
                    deferred_cursor = advance_lane_cursor(
                        deferred_cursor,
                        prior_cursor=(cursors or {}).get(engine.name),
                        scheduler_quanta=lane.scheduler_quanta,
                    )
                findings.append(
                    FalsificationFinding(
                        engine=engine.name,
                        outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                        reason=(
                            "aggregate falsification quantum expired before "
                            "this applicable lane could start"
                        ),
                        cursor=deferred_cursor,
                        error_kind="aggregate_timeout",
                    )
                )
                break
            started = time.monotonic()
            engine_deadline = min(
                invocation_deadline,
                started + float(self.policy.engine_timeout_s),
            )
            context = FalsificationContext(
                statement=effective_statement,
                target_kind=target_kind,
                preamble=preamble,
                helpers=helpers,
                local_hypotheses=tuple(local_hypotheses),
                cursor=dict((cursors or {}).get(engine.name) or {}),
                policy=self.policy,
                deadline_monotonic=engine_deadline,
            )
            if engine.name == "function":
                exhausted = _exhausted_right_pi_recipe_finding(
                    statement=effective_statement,
                    environment_hash=environment_hash,
                    cursor=dict(context.cursor),
                )
                if exhausted is not None:
                    findings.append(exhausted)
                    continue
            try:
                finding = await await_with_strict_deadline(
                    engine.search(context, lean),
                    timeout_s=self.policy.engine_timeout_s,
                    deadline_monotonic=invocation_deadline,
                    operation_label=f"mini_falsification_{engine.name}",
                    operation_ownership="result_only",
                )
            except TimeoutError:
                # Preserve the completed prefix (external review: partial
                # progress was replaced by checks_run=0 / no cursor, so the
                # same witnesses were re-checked from zero — observed six
                # restarts of one statement in a single run).
                # A bounded search quantum expiry is a miss, not a backend
                # crash: prove-mode must spend its skip latch and yield to
                # proving. Real adapter failures use error_kind=infrastructure.
                progress = dict(getattr(context, "progress", {}) or {})
                progress_cursor = dict(progress.get("cursor") or {})
                finding = FalsificationFinding(
                    engine=engine.name,
                    outcome=FalsificationOutcome.INCONCLUSIVE,
                    reason="engine watchdog expired",
                    checks_run=max(0, int(progress.get("checks_run") or 0)),
                    elapsed_s=time.monotonic() - started,
                    cursor=progress_cursor,
                    error_kind="timeout",
                )
            except Exception as exc:
                finding = FalsificationFinding(
                    engine=engine.name,
                    outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                    reason=f"{type(exc).__name__}: {exc}"[:500],
                    elapsed_s=time.monotonic() - started,
                    error_kind="infrastructure",
                )
            if finding.certificate is not None:
                # Engines are candidate generators, never certificate
                # authorities.  Even a dependency-injected engine cannot
                # bypass the service's independent full-negation replay and
                # axiom audit by returning a pre-populated certificate.
                finding = replace(finding, certificate=None)
            if lane.rotating:
                finding = replace(
                    finding,
                    cursor=advance_lane_cursor(
                        finding.cursor,
                        prior_cursor=(cursors or {}).get(engine.name),
                        scheduler_quanta=lane.scheduler_quanta,
                    ),
                )
            if finding.outcome is FalsificationOutcome.REFUTED and finding.candidates:
                candidate_metadata = dict(finding.candidates[0].metadata)
                try:
                    certification = await await_with_strict_deadline(
                        certify_candidate_result(
                            lean,
                            statement=effective_statement,
                            candidate=finding.candidates[0],
                            preamble=preamble,
                            helpers=helpers,
                            policy=self.policy,
                            environment_hash=environment_hash,
                        ),
                        deadline_monotonic=invocation_deadline,
                        operation_label=(
                            f"mini_falsification_{engine.name}_certification"
                        ),
                        operation_ownership="result_only",
                    )
                except TimeoutError:
                    retry_cursor = dict(finding.cursor)
                    pending_index = candidate_metadata.get("right_pi_candidate_index")
                    next_index = retry_cursor.get("next_index", 0)
                    retry_cursor["next_index"] = (
                        pending_index
                        if isinstance(pending_index, int)
                        and not isinstance(pending_index, bool)
                        and pending_index >= 0
                        else max(
                            0,
                            int(next_index or 0) - 1
                            if isinstance(next_index, int)
                            and not isinstance(next_index, bool)
                            else 0,
                        )
                    )
                    retry_cursor.pop("exhausted", None)
                    finding = replace(
                        finding,
                        outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                        certificate=None,
                        reason=(
                            f"{finding.reason}; aggregate falsification quantum "
                            "expired before full-negation certification"
                        )[:1000],
                        cursor=retry_cursor,
                        error_kind="timeout",
                    )
                    findings.append(finding)
                    break
                if certification.retryable:
                    # The engine cursor points one past the candidate witness.
                    # Infrastructure did not definitively reject that witness,
                    # so rewind exactly one slot and retain every plan/domain
                    # identity field for the next invocation.
                    retry_cursor = dict(finding.cursor)
                    try:
                        candidate_next_index = max(
                            0, int(retry_cursor.get("next_index") or 0)
                        )
                    except (TypeError, ValueError):
                        candidate_next_index = 0
                    if retry_cursor:
                        pending_index = candidate_metadata.get(
                            "right_pi_candidate_index"
                        )
                        retry_cursor["next_index"] = (
                            pending_index
                            if isinstance(pending_index, int)
                            and not isinstance(pending_index, bool)
                            and pending_index >= 0
                            else max(0, candidate_next_index - 1)
                        )
                        retry_cursor.pop("exhausted", None)
                    finding = replace(
                        finding,
                        outcome=FalsificationOutcome.TRANSIENT_FAILURE,
                        certificate=None,
                        reason=(
                            f"{finding.reason}; full-negation certification "
                            f"is retryable: {certification.reason}"
                        )[:1000],
                        cursor=retry_cursor,
                        error_kind="infrastructure",
                    )
                else:
                    certificate = certification.certificate
                    if (
                        not certification.authoritative
                        and candidate_metadata.get("right_pi_replay") is True
                    ):
                        # A Lean-checked negative concrete instance plus a
                        # typed Pi specialization is mathematical evidence
                        # that must not be burned because our generated replay
                        # recipe regressed. Park it at its exact plan index.
                        pending_index = candidate_metadata.get(
                            "right_pi_candidate_index"
                        )
                        retry_cursor = dict(finding.cursor)
                        if (
                            isinstance(pending_index, int)
                            and not isinstance(pending_index, bool)
                            and pending_index >= 0
                        ):
                            retry_cursor["next_index"] = pending_index
                            retry_cursor.pop("exhausted", None)
                        candidate_record = finding.candidates[0].to_record()
                        prior_disposition = dict(
                            context.cursor.get("recipe_repair_disposition") or {}
                        )
                        candidate_hash = str(
                            candidate_record.get("candidate_hash") or ""
                        )
                        prior_matches = bool(
                            right_pi_recipe_repair_disposition_is_valid(
                                prior_disposition,
                                statement=effective_statement,
                                environment_hash=environment_hash,
                                cursor=dict(context.cursor),
                            )
                            and str(prior_disposition.get("candidate_hash") or "")
                            == candidate_hash
                            and prior_disposition.get("candidate_index")
                            == pending_index
                            and prior_disposition.get("plan_hash")
                            == candidate_metadata.get("right_pi_plan_hash")
                        )
                        attempts = (
                            int(prior_disposition.get("attempts") or 0) + 1
                            if prior_matches
                            else 1
                        )
                        candidate_persistable = (
                            right_pi_candidate_record_is_persistable(
                                candidate_record
                            )
                        )
                        disposition = (
                            make_right_pi_recipe_repair_disposition(
                                statement=effective_statement,
                                environment_hash=environment_hash,
                                plan_hash=str(
                                    candidate_metadata.get("right_pi_plan_hash")
                                    or ""
                                ),
                                candidate_index=(
                                    pending_index
                                    if isinstance(pending_index, int)
                                    and not isinstance(pending_index, bool)
                                    else 0
                                ),
                                candidate_record=candidate_record,
                                attempts=attempts,
                                reason=certification.reason,
                            )
                            if candidate_persistable
                            else make_right_pi_oversized_recipe_repair_disposition(
                                statement=effective_statement,
                                environment_hash=environment_hash,
                                plan_hash=str(
                                    candidate_metadata.get("right_pi_plan_hash")
                                    or ""
                                ),
                                candidate_index=(
                                    pending_index
                                    if isinstance(pending_index, int)
                                    and not isinstance(pending_index, bool)
                                    else 0
                                ),
                                candidate_hash=candidate_hash,
                                attempts=attempts,
                                reason=certification.reason,
                            )
                        )
                        repair_exhausted = bool(
                            disposition["attempts"]
                            >= RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS
                        )
                        if repair_exhausted and not candidate_persistable:
                            retry_cursor.pop("recipe_repair_disposition", None)
                            retry_cursor["next_index"] = (
                                int(pending_index) + 1
                                if isinstance(pending_index, int)
                                and not isinstance(pending_index, bool)
                                else int(retry_cursor.get("next_index") or 0) + 1
                            )
                        else:
                            retry_cursor["recipe_repair_disposition"] = disposition
                        finding = replace(
                            finding,
                            outcome=(
                                FalsificationOutcome.REFUTED
                                if repair_exhausted
                                else FalsificationOutcome.TRANSIENT_FAILURE
                            ),
                            certificate=None,
                            reason=(
                                f"{finding.reason}; typed right-Pi full-negation "
                                f"replay invariant failed"
                                f"{' and bounded repair is exhausted' if repair_exhausted else ''}: "
                                f"{certification.reason}"
                            )[:1000],
                            cursor=retry_cursor,
                            error_kind=(
                                "certificate_recipe_exhausted"
                                if repair_exhausted
                                else "infrastructure"
                            ),
                        )
                    else:
                        finding = replace(
                            finding,
                            certificate=certificate,
                            reason=(
                                finding.reason
                                if certification.authoritative
                                else (
                                    f"{finding.reason}; candidate was not promoted "
                                    f"because full-negation certification was "
                                    f"definitively rejected: {certification.reason}"
                                )[:1000]
                            ),
                        )
            lane_outcomes[engine.name] = finding.outcome
            findings.append(finding)
            if (
                finding.authoritative_refutation
                and self.policy.stop_after_authoritative_refutation
            ):
                break
        return FalsificationReport(
            statement=effective_statement,
            target_kind=target_kind,
            findings=tuple(findings),
            policy_hash=self.policy.policy_hash,
            environment_hash=environment_hash,
        )

    async def falsify_campaign(
        self,
        lean: Any,
        *,
        statement: str,
        target_kind: TargetKind = TargetKind.HELPER,
        preamble: str = "",
        helpers: Sequence[Any] = (),
        local_hypotheses: Sequence[str] = (),
        cursors: dict[str, dict[str, Any]] | None = None,
        report_observer: Callable[[FalsificationReport], Any] | None = None,
    ) -> tuple[FalsificationReport, ...]:
        """Continue finite resumable engines until coverage or a safe stop.

        Engine and operation watchdogs are subordinate to one absolute
        aggregate deadline for the complete campaign call.  It advances only
        while an engine publishes a strictly newer cursor; transient failures,
        evidence of a refutation, completed overlap rounds, and cursor fixed
        points return control to the caller instead of spinning.
        """

        active_cursors = {
            str(engine): dict(cursor)
            for engine, cursor in dict(cursors or {}).items()
            if isinstance(cursor, dict)
        }
        reports: list[FalsificationReport] = []
        campaign_deadline = time.monotonic() + self.policy.aggregate_timeout_s
        attempted_engines: set[str] = set()
        seen_cursor_states: set[str] = {content_hash(active_cursors)}
        while True:
            report = await self.falsify(
                lean,
                statement=statement,
                target_kind=target_kind,
                preamble=preamble,
                helpers=helpers,
                local_hypotheses=local_hypotheses,
                cursors=active_cursors,
                _aggregate_deadline_monotonic=campaign_deadline,
            )
            reports.append(report)
            if report_observer is not None:
                observed = report_observer(report)
                if inspect.isawaitable(observed):
                    await observed
            attempted_engines.update(finding.engine for finding in report.findings)
            if (
                report.authoritative_refutation is not None
                or time.monotonic() >= campaign_deadline
            ):
                break
            next_cursors = {
                engine: dict(cursor) for engine, cursor in active_cursors.items()
            }
            for finding in report.findings:
                if finding.cursor:
                    next_cursors[finding.engine] = dict(finding.cursor)
            cursor_state = content_hash(next_cursors)
            if cursor_state in seen_cursor_states:
                break
            seen_cursor_states.add(cursor_state)
            active_cursors = next_cursors
            next_plan = plan_falsification_lanes(
                self.engines,
                statement=build_local_sequent(statement, local_hypotheses)
                if local_hypotheses
                else statement,
                preamble=preamble,
                cursors=active_cursors,
            )
            if any(lane.engine.name not in attempted_engines for lane in next_plan):
                # A closed/preferred lane can expose a previously shadowed
                # peer even when its own final finding has no pending cursor.
                continue
            rotating_next = tuple(lane for lane in next_plan if lane.rotating)
            if rotating_next:
                # One campaign quantum gives every overlapping lane at most
                # one turn.  Durable lane_quanta makes the next invocation
                # resume fairly without turning campaign completion into an
                # unbounded random/property generator loop.
                if all(lane.engine.name in attempted_engines for lane in rotating_next):
                    break
                continue
            if not report.has_pending_coverage:
                break
        return tuple(reports)
