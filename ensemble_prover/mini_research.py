"""Research recovery inside an ordinary Mini run's existing authorization.

A root owner observes proof work and borrows an existing conversation invocation
at a committed scheduler boundary. Independent discovery workers investigate
exact bottlenecks; their advice returns to the SAME proof session. The native
verifier alone can complete the theorem. No research verdict changes proof
status, resets a governor, or expands the parent's settings.
"""
from __future__ import annotations

import asyncio
import contextvars
from functools import wraps
import hashlib
import json
import logging
import math
import os
import sqlite3
from pathlib import Path
import tempfile
import time
from typing import Any
import uuid

_CURRENT: contextvars.ContextVar[Any] = contextvars.ContextVar("native_research_owner", default=None)
_SCOPED = contextvars.ContextVar("native_research_scoped", default=False)
_RESEARCH = contextvars.ContextVar("native_research_phase", default=False)


def current_native_research() -> Any:
    owner = _CURRENT.get()
    return owner if owner is not None and owner.active and owner.pid == os.getpid() else None


def native_research_entrypoint(function: Any) -> Any:
    """One owner across root samples; recursive and discovery calls inherit."""
    @wraps(function)
    async def wrapped(*args: Any, **kwargs: Any) -> Any:
        from .llm_usage import provider_dispatch_guard
        from .research_claims.strategy_runtime import current_strategy
        if _SCOPED.get():
            return await function(*args, **kwargs)
        scope_token = _SCOPED.set(True)
        owner = None
        owner_token = None
        try:
            if kwargs.get("autonomous_research", True) and current_strategy() is None:
                owner = NativeResearchCoordinator(
                    problem=kwargs.get("problem"), recorder=kwargs.get("recorder"),
                    checkpoint_registry=kwargs.get("checkpoint_registry"),
                )
                owner_token = _CURRENT.set(owner)
                with provider_dispatch_guard(owner.observe_dispatch):
                    return await function(*args, **kwargs)
            return await function(*args, **kwargs)
        finally:
            try:
                if owner is not None:
                    owner.active = False
                    try:
                        await owner.close()
                    except Exception as exc:
                        logging.getLogger(__name__).warning(
                            "Native research cleanup failed (%s)", type(exc).__name__)
            finally:
                if owner_token is not None:
                    _CURRENT.reset(owner_token)
                _SCOPED.reset(scope_token)
    return wrapped


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, allow_nan=False)


def _hash(value: Any) -> str:
    return hashlib.sha256(_json(value).encode()).hexdigest()


def _event(session: Any, verdict: str, **details: Any) -> None:
    record = getattr(session, "_record_event", None)
    if callable(record):
        try:
            record({"phase": "native_research", "verdict": verdict,
                    "iteration": getattr(session, "iteration", 0), **details})
        except Exception:
            pass  # Diagnostics cannot revoke a committed research or proof result.


async def _checkpoint(session: Any) -> None:
    registry = getattr(session, "checkpoint_registry", None)
    if registry is not None:
        await registry.commit_session(session.checkpoint_lane_key, session)


def _grant_usage(run: dict[str, Any], grant: dict[str, Any]) -> tuple[int, bool]:
    """Bound an unfinished grant by subsequent funding, without guessed refunds."""
    if "used" in grant:
        return grant["used"], bool(grant.get("accounting_ambiguous", False))
    start = grant["start_requests"]
    end = run["requests_used"]
    ambiguous = False
    for other in run["native_grants"].values():
        if other["id"] == grant["id"]:
            continue
        if other["start_requests"] > start:
            end = min(end, other["start_requests"])
        elif other["start_requests"] == start:
            if "ordinal" in grant and "ordinal" in other:
                if other["ordinal"] > grant["ordinal"]:
                    end = start
            elif other.get("used") != 0:
                # Old JSON sorts UUID keys; neither that order nor wall time
                # proves which equal-start grant owns the remaining exposure.
                ambiguous = True
    return max(0, end - start), ambiguous and end > start


def _allowed(session: Any) -> bool:
    if getattr(session, "scope", "problem") not in {"problem", "attempt", "sample", "parallel_fanin_recursive"}:
        return False
    if getattr(session, "root_finalized", False) or getattr(session, "terminal_failure_reason", ""):
        return False
    for name in ("_run_governor_exhausted", "_proof_root_waiting_for_finalization"):
        check = getattr(session, name, None)
        if callable(check) and check():
            return False
    return True


def _native_quantum_seconds(donor: Any) -> float:
    """Size a finite research slice for the donated provider's normal latency.

    A subscription reasoning request can legitimately need several minutes.
    The former unconditional 120-second slice cancelled those requests before
    they returned any usable answer, even under the parent's soft policy.
    Provider timeouts are sizing hints here, not additional smaller hard caps:
    the transport still enforces its own policy, and every existing donor or
    parent hard limit takes precedence over this scheduling allowance.
    """
    seconds = 600.0
    config = getattr(donor.client, "cfg", None)
    for name in ("timeout_s", "operation_timeout_s", "request_timeout_s"):
        value = getattr(config, name, None)
        if (not isinstance(value, bool) and isinstance(value, (int, float))
                and math.isfinite(value) and value > 0):
            seconds = max(seconds, float(value))
    if donor.remaining_seconds is not None:
        seconds = min(seconds, donor.remaining_seconds)
    return seconds


class NativeResearchCoordinator:
    """Run-scoped runtime capability; durable state contains only plain data."""
    def __init__(self, *, problem: Any, recorder: Any = None, checkpoint_registry: Any = None):
        self.problem, self.recorder, self.registry = problem, recorder, checkpoint_registry
        self.pid, self.active = os.getpid(), True
        self.lock = asyncio.Lock()
        self.dispatches = 0
        self.last_research_dispatches = 0
        self.store = None
        self.loop = None
        self.donor_key = None
        self.temporary = None
        self.guidance: dict[str, Any] | None = None
        self.pending_objections: list[dict[str, Any]] = []
        self._session = None
        self.pin = {
            "theorem_name": str(getattr(problem, "theorem_name", "")),
            "statement": str(getattr(problem, "statement_type", "")),
            "preamble": str(getattr(problem, "preamble", "")),
            "source_sha256": hashlib.sha256(str(getattr(problem, "raw_text", "")).encode()).hexdigest(),
            "checker_context_sha256": hashlib.sha256(str(getattr(problem, "lean_preamble", "")).encode()).hexdigest(),
        }
        self.binding = _hash(self.pin)

    def observe_dispatch(self, details: Any = None) -> None:
        if not _RESEARCH.get() and self.active and self.pid == os.getpid():
            self.dispatches += 1

    def _state(self, session: Any) -> dict[str, Any]:
        state = getattr(session, "native_research_state", None)
        if not isinstance(state, dict):
            state = {"schema": 1, "binding": self.binding, "paid_actions": 0,
                     "last_boundary": None, "rounds": 0, "grant": None}
            session.native_research_state = state
        if state.get("schema") != 1 or state.get("binding") != self.binding:
            raise ValueError("native research checkpoint target changed")
        return state

    async def boundary(self, session: Any, outcome: Any = None, *, frontier_exhausted: bool = False) -> bool:
        if not self.active or not _allowed(session):
            return False
        # Root samples serialize the research phase but keep their proof engines
        # and exact budgets. Children inherit advice without funding new owners.
        async with self.lock:
            if not _allowed(session):
                return False
            self._session = session
            try:
                state = self._state(session)
            except ValueError as exc:
                _event(session, "research_unavailable", error_type=type(exc).__name__)
                return False
            if state.get("ledger_initialized") or state.get("guidance"):
                try:
                    self._open(session, getattr(session, "prover_client", None))
                except (OSError, ValueError, RuntimeError, sqlite3.Error) as exc:
                    _event(session, "research_unavailable", error_type=type(exc).__name__)
                    return False
            delivery_changed = self._deliver(session)
            action = str(getattr(outcome, "action_id", ""))
            boundary = [int(getattr(session, "iteration", 0)), action]
            if outcome is not None and boundary != state["last_boundary"]:
                state["last_boundary"] = boundary
                metadata = dict(getattr(outcome, "metadata", {}) or {})
                paid = any(
                    int(metadata.get(key, 0) or 0) > 0
                    for key in ("provider_request_count", "provider_calls", "provider_dispatches", "provider_calls_completed", "provider_dispatches_started")
                )
                if paid:
                    state["paid_actions"] += 1
            objections = list(getattr(getattr(session, "conv", None), "_native_research_objections", []) or [])
            if objections:
                self.pending_objections.extend(item for item in objections if item not in self.pending_objections)
            reason = (
                "resume_research_grant" if state.get("grant") else
                "reported_obstacle" if self.pending_objections else
                "proof_frontier_exhausted" if frontier_exhausted and state["paid_actions"] else
                "proof_interval_audit" if state["paid_actions"] >= 3 or self.dispatches - self.last_research_dispatches >= 10 else
                "stagnation" if state["paid_actions"] and int(getattr(session, "stagnation_counter", 0)) >= 3 else None
            )
            if reason is None:
                return delivery_changed
            state["paid_actions"] = 0
            self.last_research_dispatches = self.dispatches
            try:
                return await self._investigate(session, reason)
            except (OSError, ValueError, RuntimeError, sqlite3.Error) as exc:
                # A failed optional research capability is not terminal search
                # authority. Keep the already paid grant for conservative resume.
                _event(session, "research_unavailable", error_type=type(exc).__name__)
                return False

    def _directory(self) -> Path:
        stable_root = getattr(self.registry, "registry_root", None)
        if stable_root is not None:
            return Path(stable_root) / "native_research"
        output = getattr(self.recorder, "output_dir", None)
        if output is not None:
            return Path(output) / "native_research"
        if self.temporary is None:
            self.temporary = tempfile.TemporaryDirectory(prefix="mini-native-research-")
        return Path(self.temporary.name) / "native_research"

    def _open(self, session: Any, client: Any) -> None:
        from .research_claims.discovery import initialize
        from .research_claims.discovery_store import DiscoveryStore
        from .research_claims.model import ClaimSpec, MathematicalContract
        directory = self._directory()
        if self.store is not None:
            return
        state = self._state(session)
        if not (directory / "ledger.sqlite3").exists():
            if state.get("ledger_initialized"):
                raise ValueError("saved native research ledger is missing")
            model = str(getattr(getattr(client, "cfg", None), "model", "configured-model"))
            initialize(directory, target=ClaimSpec("native-root", MathematicalContract(
                self.pin["statement"], "Original Lean theorem; exact formal context in original-target.json"), "native-mini"),
                sources={"original-target.json": _json(self._visible_target(session))}, model=model, review_model=model,
                max_requests=1, max_seconds=120, concurrency=1, strategy_recovery=True,
                strategy_policy={"interval_requests": 3, "interval_seconds": 3600,
                                 "reserve_requests": 1, "reserve_seconds": 1})
            with DiscoveryStore(directory) as created:
                run = created.run_record()
                run.update(native_target_binding=self.binding, native_grants={}, native_guidance=None,
                           native_parent_authorization=True, max_requests=0, status="paused")
                created.save_run(run)
        self.store = DiscoveryStore(directory)
        record = self.store.run_record()
        if record.get("native_target_binding") != self.binding:
            self.store.close()
            self.store = None
            raise ValueError("native research ledger belongs to a different original target")
        self.guidance = record.get("native_guidance")
        state["ledger_initialized"] = True

    def _visible_target(self, session: Any) -> dict[str, Any]:
        conv = getattr(session, "conv", None)
        return {"theorem_name": self.pin["theorem_name"], "statement": self.pin["statement"],
                "model_preamble": str(getattr(conv, "preamble", self.pin["preamble"])),
                "problem": str(getattr(conv, "problem_text", getattr(self.problem, "docstring", ""))),
                "identity_binding": self.binding}

    def _capture(self, session: Any, reason: str) -> str:
        dossier = getattr(session, "dossier", None)
        graph = getattr(dossier, "proof_graph", None)
        helpers = getattr(dossier, "verified_helpers", {}) or {}
        if isinstance(helpers, dict):
            helpers = list(helpers.values())
        context = {
            "original_target": self._visible_target(session), "trigger": reason,
            "first_uncertain_inference": "Determine the earliest unsupported ancestor, not just the current helper.",
            "formal_context": self._visible_target(session)["model_preamble"],
            "selected_work": getattr(session, "selected_work_item_record", None),
            "proof_graph": graph.to_record() if graph is not None and hasattr(graph, "to_record") else None,
            "checked_helpers": [{"name": str(getattr(h, "name", "")), "source": str(getattr(h, "source", h))} for h in helpers],
            "recent_conversation": (session.conv.messages_for_llm()[-8:]
                if callable(getattr(getattr(session, "conv", None), "messages_for_llm", None))
                else []),
            "failure": str(getattr(session, "last_failure_reason", "")),
            "objections": self.pending_objections,
            "authority": "Proof status and helpers remain controlled by Mini's original verifier; all research is advisory.",
        }
        return self.store.put_artifact(_json(context).encode(), name="native-proof-checkpoint.json")

    async def _investigate(self, session: Any, reason: str) -> bool:
        from .mini_research_budget import select_donor, debit_donor, charge_elapsed
        state = self._state(session)
        grant = state.get("grant")
        donor = select_donor(session)
        if grant is not None:
            # An interrupted quantum is conservatively retired. Its durable
            # replies are replayed without authorizing another paid request.
            action = next((a for a in session.actions if a.id == grant["action_id"]), None)
            if action is None:
                raise ValueError("saved research donor no longer exists")
            self._open(session, action.client)
            await self._ensure_loop(session, action.client, str(action.role))
            run = self.store.run_record()
            saved_grant = run["native_grants"].get(grant["id"])
            if saved_grant is not None:
                # Applying an already paid response is permitted even after
                # the old phase deadline. Zero admission prevents new work.
                run["status"] = "running"
                self.store.save_run(run)
                await self.loop.advance_native(max_requests=0, timeout_s=1)
            self._reconcile(session, grant, interrupted=True)
            state["grant"] = None
            await _checkpoint(session)
            self._deliver(session)
            return bool(self.guidance)
        if donor is None:
            _event(session, "research_deferred", reason="no_borrowable_proof_capacity")
            return False
        self._open(session, donor.client)
        await self._ensure_loop(session, donor.client, donor.role)
        assert self.store is not None
        run = self.store.run_record()
        if any("used" not in previous and _grant_usage(run, previous)[1]
               for previous in run["native_grants"].values()):
            # The old owner must first reconcile its conservative exposure.
            # Optional recovery cannot fund work by guessing a legacy refund.
            _event(session, "research_deferred", reason="ambiguous_legacy_grant_accounting")
            return False
        timeout = _native_quantum_seconds(donor)
        checkpoint = self._capture(session, reason)
        grant = {"id": uuid.uuid4().hex, "action_id": donor.action_id,
                 "requests": donor.request_limit, "accounted": 0,
                 "expires_at": time.time() + timeout,
                 "source_invocations": donor.initial_invocations + 1}
        donor = debit_donor(session, donor)
        timeout = min(timeout, _native_quantum_seconds(donor))
        grant["expires_at"] = time.time() + timeout
        grant["seconds"] = timeout
        state["grant"] = grant
        # The budget debit and unique grant id precede every external request.
        await _checkpoint(session)
        with self.store.atomic():
            run = self.store.run_record()
            grants = run["native_grants"]
            if grant["id"] in grants:
                raise ValueError("native grant was already funded")
            # A different restored lane can reach this boundary before the
            # owner of an interrupted grant. Freeze the old usage while this
            # ledger still ends at its last request, so later reconciliation
            # cannot charge this lane's new dispatches to the old donor.
            for previous in grants.values():
                if "used" not in previous:
                    previous["used"], ambiguous = _grant_usage(run, previous)
                    if ambiguous:
                        previous["accounting_ambiguous"] = True
            # Revoke unused capacity of past quanta. Grant new calls solely from
            # the current precommitted donor; no run-limit reset is involved.
            run.update(max_requests=run["requests_used"] + grant["requests"],
                       started_at=run.get("started_at") or time.time(), deadline=grant["expires_at"],
                       max_seconds=timeout, request_timeout_s=timeout, status="running")
            grants[grant["id"]] = {**grant, "start_requests": run["requests_used"],
                                  "ordinal": len(grants), "closed": False}
            self.store.save_run(run)
            for job in self.store.jobs():
                if job["role"] in {"research", "review"} and job["status"] in {"pending", "waiting", "responded"}:
                    self.loop._notify(job["job_id"], {
                        "native_proof_checkpoint": checkpoint,
                        "instruction": "Read the exact checkpoint. Independently audit the route, constants, hypotheses and ancestors. Search original sources for the bottleneck or counterexamples when relevant. Execute a discriminating check or a substantively different derivation. Return concrete advice via formalize/proof_plan; a renamed plan or generic encouragement is insufficient. Never weaken the original theorem.",
                    }, requires_response=True)
            if not any(j["status"] in {"pending", "responded"} for j in self.store.jobs()):
                self.store.add_job("native-root", f"Audit and redirect the native proof checkpoint {checkpoint}; investigate a different route and give its exact next inference.")
        state["rounds"] += 1
        _event(session, "research_started", reason=reason, grant_id=grant["id"],
               requests=grant["requests"], timeout_s=timeout, ledger=str(self.store.directory))
        start = time.monotonic()
        token = _RESEARCH.set(True)
        result: dict[str, Any] = {"reason": "parent_deadline_exhausted", "paid_dispatches": 0}
        try:
            remaining = grant["expires_at"] - time.time()
            parent_remaining = getattr(session, "_run_governor_remaining_s", lambda: None)()
            if parent_remaining is not None:
                remaining = min(remaining, parent_remaining)
            if remaining > 0 and _allowed(session):
                result = await self.loop.advance_native(max_requests=grant["requests"], timeout_s=remaining)
        finally:
            _RESEARCH.reset(token)
            elapsed = time.monotonic() - start
            charge_elapsed(session, donor, elapsed)
            grant["elapsed_accounted"] = elapsed
            self._reconcile(session, grant, elapsed_s=elapsed)
            accrue = getattr(session, "_accrue_run_governor_elapsed", None)
            if callable(accrue):
                accrue()
            state["grant"] = None
            state["paid_actions"] = 0
            self.pending_objections.clear()
            if getattr(session, "conv", None) is not None:
                session.conv._native_research_objections = []
            self._deliver(session)
            await _checkpoint(session)
        research_outcome = result.get("reason", "unknown")
        if research_outcome in {"quantum_timeout", "deadline_exhausted", "parent_deadline_exhausted"}:
            _event(session, "research_timed_out", reason=research_outcome,
                   timeout_s=timeout, paid_dispatches=result.get("paid_dispatches", 0),
                   guidance_available=bool(self.guidance))
        _event(session, "research_round_complete", reason=research_outcome,
               research_round=state["rounds"], research_elapsed_s=elapsed,
               paid_dispatches=result.get("paid_dispatches", 0),
               last_provider_error=result.get("last_provider_error"))
        _event(session, "proof_resumed", research_round=state["rounds"],
               research_outcome=research_outcome, guidance_available=bool(self.guidance))
        return bool(self.guidance)

    async def _ensure_loop(self, session: Any, client: Any, role: str) -> None:
        from .mini_research_budget import clone_research_client
        from .research_claims.discovery import DiscoveryLoop
        key = (id(client), role)
        if self.loop is not None and key == self.donor_key:
            return
        if self.loop is not None:
            await self.loop._retire_clients(set(), closing=True, preserve_failure=True)
        def fresh_transport(worker: str) -> Any:
            return clone_research_client(client)
        self.loop = DiscoveryLoop(self.store, fresh_transport, fresh_transport, native_mode=True,
            cost_controller=getattr(session, "cost_controller", None), owns_clients=True,
            cost_roles={"research": role, "review": role}, on_event=self._research_event)
        self.donor_key = key

    def _reconcile(self, session: Any, grant: dict[str, Any], *,
                   elapsed_s: float | None = None, interrupted: bool = False) -> None:
        with self.store.atomic():
            run = self.store.run_record()
            saved = run["native_grants"].get(grant["id"])
            if saved is not None:
                used, ambiguous = _grant_usage(run, saved)
                if ambiguous:
                    saved["accounting_ambiguous"] = True
                    _event(session, "research_grant_accounting_ambiguous", grant_id=grant["id"])
                missing = max(0, used - grant.get("accounted", 0))
                session.provider_dispatches_started_total = int(getattr(session, "provider_dispatches_started_total", 0)) + missing
                grant["accounted"] = used
                if elapsed_s is not None:
                    saved["elapsed_s"] = elapsed_s
                if interrupted:
                    # A killed process cannot report its precise active duration.
                    # Charge its bounded reserved time rather than renew it.
                    elapsed = saved.get("elapsed_s", grant.get("seconds", 0.0))
                    uncharged = max(0.0, elapsed - grant.get("elapsed_accounted", 0.0))
                    budget = session.budgets[grant["action_id"]]
                    budget.total_seconds += uncharged
                    budget.unproductive_seconds += uncharged
                    session.run_governor_elapsed_s = float(getattr(session, "run_governor_elapsed_s", 0)) + uncharged
                    grant["elapsed_accounted"] = elapsed
                saved.update(used=used, closed=True)
                run.update(max_requests=run["requests_used"], status="paused")
                self.store.save_run(run)
            self.guidance = run.get("native_guidance")

    def _research_event(self, event: dict[str, Any]) -> None:
        if self._session is not None:
            _event(self._session, "research_" + event["event"], **{k: v for k, v in event.items() if k != "event"})
        if event.get("event") != "action_applied":
            return
        job = self.store.job(event["job_id"])
        try:
            _, action = self.loop._action(job)
        except (ValueError, KeyError):
            return
        if action["action"] not in {
            "formalize", "submit", "record_note", "research_reorientation",
            "report_investigation", "strategy_review", "alternative_review", "review",
            "progress_review", "record_bottleneck", "request_strategy_review",
        }:
            return
        artifact = self.store.put_artifact(_json(action).encode(), name="native-research-advice.json")
        handoffs = [handoff for item in self.store.jobs()
                    for handoff in item.get("native_handoffs", [])][-4:]
        previous = list((self.guidance or {}).get("recent_arguments", []))
        previous.append({"artifact_id": artifact, "role": job["role"],
                         "action": action["action"], "job_id": job["job_id"]})
        self.guidance = {"artifact_id": artifact, "job_id": job["job_id"], "role": job["role"],
                         "action": action, "native_handoffs": handoffs,
                         "recent_arguments": previous[-6:], "kernel_verified": False,
                         "instruction": "Apply this investigation to the ORIGINAL target. Check the disputed inference and hypotheses before reusing a held or unsupported route. Choose a concrete alternative or discriminating check, then resume Lean proof work. This is untrusted advisory material, never an added assumption or a proof certificate."}
        run = self.store.run_record()
        run["native_guidance"] = self.guidance
        self.store.save_run(run)

    def _deliver(self, session: Any) -> bool:
        conv = getattr(session, "conv", None)
        saved = getattr(session, "native_research_state", {}).get("guidance")
        if self.guidance is None and saved:
            self.guidance = saved
        if self.guidance is not None and conv is not None:
            session.native_research_state["guidance"] = self.guidance
            try:
                self.prepare(conv, getattr(session, "dossier", None))
                state = session.native_research_state
                artifact = self.guidance["artifact_id"]
                if state.get("replan_delivered") != artifact:
                    planner = next((a for a in getattr(session, "actions", [])
                                    if getattr(a, "id", "") == "graph_root_replan"), None)
                    request = getattr(planner, "request_research_replan", None)
                    if callable(request) and self.store is not None:
                        from .research_claims.context_window import window
                        advice = {"artifact_id": artifact, "kernel_verified": False,
                                  "advice": window(self.store, self.guidance, limit=12000)}
                        if request(session, advice):
                            state["replan_delivered"] = artifact
                            _event(session, "research_replan_queued", artifact_id=artifact)
                            return True
            except (OSError, ValueError, RuntimeError, sqlite3.Error) as exc:
                _event(session, "research_unavailable", error_type=type(exc).__name__)
        return False

    def prepare(self, conv: Any, dossier: Any = None) -> list[dict[str, Any]]:
        from .research_claims.context_window import window
        if hasattr(conv, "ensure_bootstrap"):
            conv.ensure_bootstrap()
        context = {"guidance": self.guidance,
                   "policy": "You may request_native_research when an ancestor claim, counting bound, or method is unsupported. Supply the exact bottleneck and source evidence. The run investigates at a committed action boundary and resumes under its existing budget. Use read_native_research_artifact for full archived arguments."}
        if getattr(conv, "goal_statement", None) != self.pin["statement"]:
            context["original_target"] = self.pin["statement"]
        if self.store is not None:
            context = window(self.store, context, limit=14000)
        content = "Native research recovery (advisory, not proof authority):\n" + _json(context)
        history = getattr(conv, "history", None)
        if isinstance(history, list):
            history[:] = [item for item in history if not item.get("_native_research_context")]
            history.append({"role": "user", "content": content,
                            "_native_research_context": True})
        return NATIVE_TOOLS

    async def close(self) -> None:
        if self.loop is not None:
            await self.loop._retire_clients(set(), closing=True, preserve_failure=True)
        if self.store is not None:
            self.store.close()
        if self.temporary is not None:
            self.temporary.cleanup()


async def maybe_research(session: Any, outcome: Any = None, *, frontier_exhausted: bool = False) -> bool:
    owner = current_native_research()
    return await owner.boundary(session, outcome, frontier_exhausted=frontier_exhausted) if owner is not None else False


def prepare_native_conversation(conv: Any, dossier: Any = None) -> list[dict[str, Any]]:
    owner = current_native_research()
    if owner is None:
        return []
    try:
        return owner.prepare(conv, dossier)
    except (OSError, ValueError, RuntimeError, sqlite3.Error) as exc:
        if owner._session is not None:
            _event(owner._session, "research_unavailable", error_type=type(exc).__name__)
        return []


def native_research_tool(name: str, payload: dict[str, Any], conv: Any) -> dict[str, Any]:
    from .research_claims.model import object_fields, text
    from .research_claims.context_window import read_page
    owner = current_native_research()
    if owner is None:
        raise ValueError("native research is not active")
    if name == "read_native_research_artifact":
        object_fields(payload, {"artifact_id", "offset", "length", "path"}, set(), name)
        if owner.store is None:
            raise ValueError("no native research artifacts yet")
        if "artifact_id" not in payload:
            if owner.guidance is None:
                raise ValueError("no native research advice yet")
            # Optional prompt advice may be dropped to preserve the original
            # source. Keep its entire argument/handoff index discoverable even
            # when the provider never saw an artifact hash.
            payload = {**payload, "artifact_id": owner.store.put_artifact(
                _json(owner.guidance).encode(), name="current-native-research-guidance.json",
            )}
        return read_page(owner.store, **payload)
    if name != "request_native_research":
        raise ValueError("unknown native research tool")
    object_fields(payload, {"statement", "reason", "evidence_artifact_ids"}, {"statement", "reason"}, name)
    text(payload["statement"], "exact bottleneck")
    text(payload["reason"], "complete objection")
    ids = payload.get("evidence_artifact_ids", [])
    if not isinstance(ids, list) or any(not isinstance(item, str) for item in ids):
        raise ValueError("evidence_artifact_ids must be an array of artifact ids")
    for artifact in ids:
        if owner.store is None:
            raise ValueError("unknown native evidence")
        owner.store.read_artifact(artifact)
    objections = list(getattr(conv, "_native_research_objections", []) or [])
    if payload not in objections:
        objections.append(payload)
    conv._native_research_objections = objections[-8:]
    owner.pending_objections = objections[-8:]
    return {"status": "queued_for_committed_boundary", "kernel_verified": False,
            "instruction": "Preserve exact reasoning and settle this action; research will inspect the obstacle within remaining settings."}


NATIVE_TOOLS = [
    {"type": "function", "function": {"name": "request_native_research",
     "description": "Request independent investigation of an unsupported ancestor or stalled method; never refutes or stops the run.",
     "parameters": {"type": "object", "properties": {"statement": {"type": "string"}, "reason": {"type": "string"}, "evidence_artifact_ids": {"type": "array", "items": {"type": "string"}}}, "required": ["statement", "reason"], "additionalProperties": False}}},
    {"type": "function", "function": {"name": "read_native_research_artifact",
     "description": "Read exact pages of archived research arguments or sources. Omit artifact_id for the complete current advice envelope, including argument and handoff links.",
     "parameters": {"type": "object", "properties": {"artifact_id": {"type": "string"}, "offset": {"type": "integer"}, "length": {"type": "integer"}, "path": {"type": "array", "items": {"anyOf": [{"type": "string"}, {"type": "integer"}]}}}, "required": [], "additionalProperties": False}}},
]
