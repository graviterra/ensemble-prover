"""Prove-mode falsification scheduling: one foreground veto, then yield.

Watchdogs remain, but they are non-terminal. A hung Lean process is cancelled
and joined; progress (cursors, unpromoted candidates, pending certificates) is
preserved; the action yields; and the same work retries after backoff or a
capability-generation wakeup. Nothing here declares a hard mathematical
problem finished.
"""

from __future__ import annotations

import copy
import inspect
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

from .lean_check import safe_helper_sources
from .model import (
    FalsificationOutcome,
    FalsificationReport,
    TargetKind,
    content_hash,
)
from .policy import FalsificationPolicy
from .service import (
    FALSIFICATION_ENGINE_SCHEMA_VERSION,
    FalsificationService,
    _runtime_dependency_identities,
    build_local_sequent,
    falsification_environment_hash,
)


DEFAULT_FALSIFICATION_VETO_ENGINES = ("structural", "finite")
DEFAULT_FALSIFICATION_VETO_MAX_CHECKS = 8
# A concrete Lean probe owns 5s and its local cancellation guard owns 25%
# headroom.  The engine lease must sit strictly outside both or the engine
# watchdog cancels first and can leave Lean teardown holding the sole runner
# permit.  Keep the whole foreground quantum bounded by the 8s search lease.
DEFAULT_FALSIFICATION_VETO_ENGINE_TIMEOUT_S = 7.5
DEFAULT_FALSIFICATION_VETO_SEARCH_TIMEOUT_S = 8.0
# Exponential yield, not a cap that abandons work during a long outage.
DEFAULT_FALSIFICATION_INFRA_BACKOFF_S = (0.0, 1.0, 4.0, 16.0, 32.0)

_SCHEDULER_RUNTIME_ATTR = "_mini_falsification_scheduler_runtime"


@dataclass(frozen=True)
class ProveModeFalsificationDecision:
    """One pre-call scheduler decision shared by execution and telemetry."""

    skip_key: str = ""
    skip_reason: str = ""


def make_falsification_veto_policy(
    base: FalsificationPolicy | None = None,
) -> FalsificationPolicy:
    """Return a short, cheap-engine policy for one foreground veto quantum.

    Certification still uses the caller's ``operation_timeout_s``. Search is
    clipped by the veto engine/aggregate budgets. Instance probes never
    inherit that certification window. An unpromoted candidate is never
    discarded: a short leftover certification window becomes a durable
    retry, not a terminal miss. ``exact_algebra`` is a Lean instance-search
    engine, not a cheap filter, so it stays on the idle/full campaign.
    """

    source = base or FalsificationPolicy()
    requested = tuple(str(engine) for engine in source.engines)
    engines = tuple(
        engine
        for engine in DEFAULT_FALSIFICATION_VETO_ENGINES
        if engine in requested
    )
    if not engines:
        engines = requested
    max_checks = min(
        int(source.max_candidates_per_engine),
        DEFAULT_FALSIFICATION_VETO_MAX_CHECKS,
    )
    search_timeout = min(
        float(source.aggregate_timeout_s),
        DEFAULT_FALSIFICATION_VETO_SEARCH_TIMEOUT_S,
    )
    engine_timeout = min(
        float(source.engine_timeout_s),
        DEFAULT_FALSIFICATION_VETO_ENGINE_TIMEOUT_S,
    )
    return FalsificationPolicy(
        enabled=bool(source.enabled),
        engines=engines,
        max_candidates_per_engine=max_checks,
        max_finite_checks=min(int(source.max_finite_checks), max_checks),
        max_property_examples=source.max_property_examples,
        max_graph_vertices=source.max_graph_vertices,
        max_numeric_examples=source.max_numeric_examples,
        random_seed=source.random_seed,
        operation_timeout_s=float(source.operation_timeout_s),
        engine_timeout_s=engine_timeout,
        aggregate_timeout_s=search_timeout,
        stop_after_authoritative_refutation=True,
        require_axiom_audit=source.require_axiom_audit,
        allowed_axioms=source.allowed_axioms,
    )


def cheap_veto_skip_key(
    *,
    statement: str,
    hypotheses: Sequence[str] = (),
    preamble: str = "",
    policy: FalsificationPolicy,
    lean: Any = None,
) -> str:
    """Identity for the advisory foreground filter, omitting helper growth.

    ``falsification_environment_hash`` still binds cursors and certificates to
    helpers. This key only answers "did we already spend the cheap veto?" so
    adding a helper does not reopen ordinary root search. Pending certificates
    and Lean-checked candidates remain independently replayable.
    """

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
            "statement": str(statement or "").strip(),
            "hypotheses": [
                str(item).strip() for item in hypotheses if str(item).strip()
            ],
            "preamble": str(preamble or ""),
            "semantic_policy": {
                "random_seed": policy.random_seed,
                "allowed_axioms": sorted(set(policy.allowed_axioms)),
                "max_graph_vertices": policy.max_graph_vertices,
                "require_axiom_audit": policy.require_axiom_audit,
            },
            "lean_config": {
                "project_dir": project_dir,
                "preamble_import": str(getattr(cfg, "preamble_import", "") or ""),
                "extra_imports": tuple(getattr(cfg, "extra_imports", ()) or ()),
                "module_search_paths": tuple(
                    getattr(cfg, "module_search_paths", ()) or ()
                ),
                "resolved_lean_path": str(
                    getattr(cfg, "resolved_lean_path", "") or ""
                ),
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


def helper_fingerprint(helpers: Sequence[Any] = ()) -> str:
    return content_hash({"helpers": safe_helper_sources(helpers)})


def scheduler_runtime(dossier: Any) -> dict[str, Any]:
    """Process-local scheduling memory. Not mathematical evidence."""

    state = getattr(dossier, _SCHEDULER_RUNTIME_ATTR, None)
    if not isinstance(state, dict):
        state = {
            "foreground_spent": set(),
            "coverage_pending": set(),
            "infra_backoff": {},
            "helper_fingerprint": {},
        }
        try:
            setattr(dossier, _SCHEDULER_RUNTIME_ATTR, state)
        except Exception as exc:
            raise TypeError(
                "falsification scheduler runtime requires a mutable dossier"
            ) from exc
    state.setdefault("foreground_spent", set())
    state.setdefault("coverage_pending", set())
    state.setdefault("infra_backoff", {})
    state.setdefault("helper_fingerprint", {})
    return state


def copy_scheduler_runtime(dst: Any, src: Any) -> None:
    source = getattr(src, _SCHEDULER_RUNTIME_ATTR, None)
    if not isinstance(source, dict):
        return
    setattr(
        dst,
        _SCHEDULER_RUNTIME_ATTR,
        {
            "foreground_spent": set(source.get("foreground_spent") or ()),
            "coverage_pending": set(source.get("coverage_pending") or ()),
            "infra_backoff": copy.deepcopy(dict(source.get("infra_backoff") or {})),
            "helper_fingerprint": dict(source.get("helper_fingerprint") or {}),
        },
    )


def session_has_recursive_controller(session: Any) -> bool:
    return any(
        str(getattr(action, "id", "") or "") == "recursive_controller"
        for action in getattr(session, "actions", ()) or ()
    )


def _backoff_delay_s(failures: int) -> float:
    schedule = DEFAULT_FALSIFICATION_INFRA_BACKOFF_S
    if failures <= 0:
        return 0.0
    index = min(failures - 1, len(schedule) - 1)
    return float(schedule[index])


def _runtime_capability_key(capability: Any) -> Any:
    """Return copy-safe process-local identity for one runtime generation."""

    if capability is None or type(capability) in {str, int, float, bool, bytes}:
        return capability
    from ..mini_session.session import _dispatch_capability_generation_nonce

    return (
        "mini-capability-generation-v1",
        _dispatch_capability_generation_nonce(capability),
    )


def infra_retry_is_blocked(
    dossier: Any,
    skip_key: str,
    *,
    capability: Any,
    now: float | None = None,
) -> bool:
    """Return True when infrastructure work should yield, not run."""

    record = dict(scheduler_runtime(dossier)["infra_backoff"].get(skip_key) or {})
    if not record:
        return False
    if record.get("capability") != _runtime_capability_key(capability):
        return False
    earliest = float(record.get("earliest_monotonic") or 0.0)
    return float(now if now is not None else time.monotonic()) < earliest


def note_infrastructure_failure(
    dossier: Any,
    skip_key: str,
    *,
    capability: Any,
    now: float | None = None,
) -> None:
    state = scheduler_runtime(dossier)
    current = dict(state["infra_backoff"].get(skip_key) or {})
    failures = int(current.get("failures") or 0) + 1
    moment = float(now if now is not None else time.monotonic())
    state["infra_backoff"][skip_key] = {
        "failures": failures,
        "earliest_monotonic": moment + _backoff_delay_s(failures),
        "capability": _runtime_capability_key(capability),
    }


def clear_infrastructure_backoff(dossier: Any, skip_key: str) -> None:
    scheduler_runtime(dossier)["infra_backoff"].pop(skip_key, None)


def foreground_veto_is_spent(dossier: Any, skip_key: str) -> bool:
    return skip_key in scheduler_runtime(dossier)["foreground_spent"]


def mark_foreground_veto_spent(
    dossier: Any,
    skip_key: str,
    *,
    coverage_pending: bool = False,
    helpers: Sequence[Any] = (),
) -> None:
    state = scheduler_runtime(dossier)
    state["foreground_spent"].add(skip_key)
    if coverage_pending:
        state["coverage_pending"].add(skip_key)
    else:
        state["coverage_pending"].discard(skip_key)
    state["helper_fingerprint"][skip_key] = helper_fingerprint(helpers)
    clear_infrastructure_backoff(dossier, skip_key)


def helpers_changed_since_veto(dossier: Any, skip_key: str, helpers: Sequence[Any]) -> bool:
    previous = str(
        scheduler_runtime(dossier)["helper_fingerprint"].get(skip_key) or ""
    )
    if not previous:
        return False
    return previous != helper_fingerprint(helpers)


def coverage_is_pending(dossier: Any, skip_key: str) -> bool:
    return skip_key in scheduler_runtime(dossier)["coverage_pending"]


def record_veto_outcome(
    dossier: Any,
    skip_key: str,
    report: FalsificationReport,
    *,
    helpers: Sequence[Any] = (),
    capability: Any = None,
    now: float | None = None,
) -> None:
    """Latch search memory without abandoning retryable work."""

    if report.outcome is FalsificationOutcome.TRANSIENT_FAILURE:
        note_infrastructure_failure(
            dossier, skip_key, capability=capability, now=now
        )
        if report.has_pending_coverage or report.unpromoted_refutation_count:
            scheduler_runtime(dossier)["coverage_pending"].add(skip_key)
        return
    mark_foreground_veto_spent(
        dossier,
        skip_key,
        coverage_pending=bool(report.has_pending_coverage),
        helpers=helpers,
    )


def plan_prove_mode_falsification(
    *,
    dossier: Any,
    statement: str,
    local_hypotheses: Sequence[str] = (),
    preamble: str = "",
    policy: FalsificationPolicy,
    lean: Any = None,
    resume: bool = False,
    capability: Any = None,
) -> ProveModeFalsificationDecision:
    """Classify one quantum before it can mutate its scheduler latch."""

    if resume:
        return ProveModeFalsificationDecision(skip_reason="resume")
    if dossier is None:
        return ProveModeFalsificationDecision(skip_reason="dossier_missing")
    if not policy.enabled:
        return ProveModeFalsificationDecision(skip_reason="disabled")
    skip_key = cheap_veto_skip_key(
        statement=statement,
        hypotheses=local_hypotheses,
        preamble=preamble,
        policy=policy,
        lean=lean,
    )
    if foreground_veto_is_spent(dossier, skip_key):
        return ProveModeFalsificationDecision(
            skip_key=skip_key,
            skip_reason="foreground_veto_spent",
        )
    if infra_retry_is_blocked(
        dossier,
        skip_key,
        capability=capability,
    ):
        return ProveModeFalsificationDecision(
            skip_key=skip_key,
            skip_reason="infrastructure_backoff",
        )
    return ProveModeFalsificationDecision(skip_key=skip_key)


async def run_prove_mode_falsification(
    *,
    lean: Any,
    dossier: Any,
    statement: str,
    target_kind: TargetKind = TargetKind.HELPER,
    preamble: str = "",
    helpers: Sequence[Any] = (),
    local_hypotheses: Sequence[str] = (),
    veto_service: FalsificationService,
    campaign_service: FalsificationService,
    resume: bool = False,
    adaptive_campaign: bool = False,
    report_observer: Callable[[FalsificationReport], Any] | None = None,
    capability: Any = None,
    _decision: ProveModeFalsificationDecision | None = None,
) -> tuple[FalsificationReport, ...]:
    """One veto quantum, or a synthetic skip, then optional idle-depth quantum.

    ``adaptive_campaign`` runs one full-policy ``falsify()`` quantum after the
    veto when later proof failure or concrete suspicion warrants deeper
    search. It never loops until domain exhaustion.
    """

    decision = _decision or plan_prove_mode_falsification(
        dossier=dossier,
        statement=statement,
        local_hypotheses=local_hypotheses,
        preamble=preamble,
        policy=campaign_service.policy,
        lean=lean,
        resume=resume,
        capability=capability,
    )
    skip_key = decision.skip_key
    environment_hash = falsification_environment_hash(
        preamble=preamble,
        helpers=helpers,
        policy=campaign_service.policy,
        lean=lean,
    )

    def _empty_report() -> FalsificationReport:
        return FalsificationReport(
            statement=statement,
            target_kind=target_kind,
            findings=(),
            policy_hash=campaign_service.policy.policy_hash,
            environment_hash=environment_hash,
        )

    async def _observe(report: FalsificationReport) -> None:
        if report_observer is None:
            return
        observed = report_observer(report)
        if inspect.isawaitable(observed):
            await observed

    if decision.skip_reason in {"resume", "dossier_missing", "disabled"}:
        return (_empty_report(),)

    reports: list[FalsificationReport] = []
    # Transient infrastructure does not spend the latch.  It retries after
    # backoff or a capability-generation wakeup, indefinitely.
    veto_due = not decision.skip_reason

    if veto_due:
        cursor_getter = getattr(dossier, "falsification_cursors_for_statement", None)
        cursor_statement = (
            build_local_sequent(statement, local_hypotheses)
            if local_hypotheses
            else statement
        )
        veto_environment_hash = falsification_environment_hash(
            preamble=preamble,
            helpers=helpers,
            policy=veto_service.policy,
            lean=lean,
        )
        cursors = (
            cursor_getter(cursor_statement, environment_hash=veto_environment_hash)
            if callable(cursor_getter)
            else {}
        )
        report = await veto_service.falsify(
            lean,
            statement=statement,
            target_kind=target_kind,
            preamble=preamble,
            helpers=helpers,
            local_hypotheses=local_hypotheses,
            cursors=cursors,
        )
        record_veto_outcome(
            dossier,
            skip_key,
            report,
            helpers=helpers,
            capability=capability,
        )
        await _observe(report)
        reports.append(report)
    else:
        reports.append(_empty_report())

    adaptive_campaign_is_serviceable = decision.skip_reason in {
        "",
        "foreground_veto_spent",
    } and not reports[-1].has_transient_failures
    if (
        adaptive_campaign
        and adaptive_campaign_is_serviceable
        and reports[-1].authoritative_refutation is None
    ):
        cursor_getter = getattr(dossier, "falsification_cursors_for_statement", None)
        cursor_statement = (
            build_local_sequent(statement, local_hypotheses)
            if local_hypotheses
            else statement
        )
        cursors = (
            cursor_getter(cursor_statement, environment_hash=environment_hash)
            if callable(cursor_getter)
            else {}
        )
        campaign_report = await campaign_service.falsify(
            lean,
            statement=statement,
            target_kind=target_kind,
            preamble=preamble,
            helpers=helpers,
            local_hypotheses=local_hypotheses,
            cursors=cursors,
        )
        if campaign_report.has_pending_coverage:
            scheduler_runtime(dossier)["coverage_pending"].add(skip_key)
        await _observe(campaign_report)
        reports.append(campaign_report)
    return tuple(reports)
