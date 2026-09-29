"""Durable research allocation, independent of mathematical proof authority.

All changes share the discovery ledger's writer transaction. A StrategyYield
returns control to research; it is never an instruction to terminate a run.
Reviews restrict expenditure, not the truth of a Lean proposition.
"""

from __future__ import annotations

import hashlib
import math
import os
import time
import uuid
from contextlib import contextmanager, nullcontext
from copy import deepcopy
from typing import Any, Callable, Iterator

from .discovery_store import DiscoveryStore
from .model import json_text, positive_int, text
from .store import ResearchStoreError


class StrategyYield(BaseException):
    """Nonterminal control transfer; ordinary provider retries must not catch it."""

    def __init__(self, reason: str, *, subject_id: str = "", allocation_id: str = ""):
        super().__init__(reason)
        self.reason = reason
        self.subject_id = subject_id
        self.allocation_id = allocation_id

    def to_dict(self) -> dict[str, Any]:
        result = {
            "status": "yielded_for_review",
            "reason": self.reason,
            "subject_id": self.subject_id,
            "allocation_id": self.allocation_id,
        }
        lineage = getattr(self, "frontier_request_lineage", None)
        if lineage is not None:
            result["frontier_request_lineage"] = lineage
        return result


def _digest(value: Any) -> str:
    return hashlib.sha256(json_text(value).encode()).hexdigest()


def _seconds(value: Any, name: str) -> float:
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(value)
        or value <= 0
    ):
        raise ValueError(f"{name} must be finite and positive")
    return float(value)


class StrategyController:
    """One owner for leases, scoped objections, and conserved proof intervals."""

    Yield = StrategyYield
    SCOPES = {
        "claim_contradiction",
        "method_barrier",
        "unsupported_bridge",
        "allocation_exhausted",
    }
    MAX_ARTIFACT_BYTES = 4 * 1024 * 1024
    MAX_ARTIFACTS_PER_ATTEMPT = 32

    def __init__(
        self, store: DiscoveryStore, *, clock: Callable[[], float] = time.time
    ):
        self.store = store
        self.clock = clock
        self.snapshot()

    @classmethod
    def enable(
        cls,
        store: DiscoveryStore,
        *,
        interval_requests: int = 10,
        interval_seconds: float = 600,
        reserve_requests: int = 4,
        reserve_seconds: float = 60,
        max_no_progress: int = 2,
        original_lean: dict[str, Any] | None = None,
        clock: Callable[[], float] = time.time,
        frontier_research: dict[str, Any] | None = None,
    ) -> StrategyController:
        for name, value in (
            ("interval_requests", interval_requests),
            ("reserve_requests", reserve_requests),
            ("max_no_progress", max_no_progress),
        ):
            positive_int(value, name)
        _seconds(interval_seconds, "interval_seconds")
        _seconds(reserve_seconds, "reserve_seconds")
        with nullcontext() if store._applying else store.atomic():
            run = store.run_record()
            if run.get("strategy_review") is not None:
                raise ValueError("strategy controller already enabled")
            root = store.get_claim(run["target_id"])
            original_anchor = None
            if original_lean is not None:
                from ..formalization.environment import EnvironmentSnapshot
                from .pinned_target import validate_capture

                if not run.get("closed_loop"):
                    raise ValueError(
                        "original target capture requires a pinned Lean environment"
                    )
                validate_capture(
                    original_lean,
                    EnvironmentSnapshot.from_dict(run["closed_loop"]["environment"]),
                    capture_root=store.directory / "original-modules",
                )
                source_id = original_lean["original_source_sha256"]
                if source_id not in run["sources"].values():
                    raise ValueError(
                        "original capture does not match an owner source artifact"
                    )
                original_anchor = {
                    "binding": original_lean["binding"],
                    "source_artifact": source_id,
                    "artifact": deepcopy(original_lean["artifact"]),
                }
            root_statement = root["spec"]["contract"]["statement"].strip()
            formal_identity = _digest({"statement": root_statement, "context": ""})
            root_id = "subject-" + formal_identity
            state: dict[str, Any] = {
                "schema": 1,
                "owner_id": uuid.uuid4().hex,
                "root_binding": _digest(root),
                "root_id": root_id,
                "original_lean": deepcopy(original_lean),
                "original_anchor": original_anchor,
                "policy": {
                    "interval_requests": interval_requests,
                    "interval_seconds": interval_seconds,
                    "reserve_requests": reserve_requests,
                    "reserve_seconds": reserve_seconds,
                    "max_no_progress": max_no_progress,
                },
                "generation": 0,
                "subjects": {},
                "allocations": {},
                "reviews": {},
                "holds": {},
                "attempts": {},
                "events": [],
                "implications": [],
            }
            state["subjects"][root_id] = cls._new_subject(
                root_id,
                root_statement,
                "",
                formal_identity,
            )
            from .frontier.config import normalize_config

            frontier = normalize_config(
                frontier_research,
                permit_lease_seconds=reserve_seconds,
                max_no_progress=max_no_progress,
            )
            if frontier["mode"] != "off":
                state["frontier_research"] = {
                    "mode": frontier["mode"],
                    "progress_policy_version": frontier["progress_policy_version"],
                    "tool_policy_version": frontier["tool_policy_version"],
                }
            run["strategy_review"] = state
            run["original_target_anchor"] = original_anchor
            if frontier["mode"] != "off":
                from .frontier.persist import install_campaign

                install_campaign(store, state, run, frontier)
            store.save_run(run)
        return cls(store, clock=clock)

    def _frontier_mode(self, state: dict[str, Any]) -> str:
        from .frontier.hooks import mode_of

        return mode_of(state)

    @staticmethod
    def _new_subject(
        subject_id: str, statement: str, parent_id: str, formal_identity: str
    ) -> dict[str, Any]:
        return {
            "subject_id": subject_id,
            "statement": statement,
            "parent_ids": [parent_id] if parent_id else [],
            "formal_identity": formal_identity,
            "disposition": "candidate",
            "generation": 0,
            "evidence_revision": 0,
            "decision_generation": 0,
            "evidence_tokens": {},
            "decision_tokens": {},
            "no_progress_intervals": 0,
            "alternative_after_interval": 0,
            "interval_sequence": 0,
            "progress_receipts": [],
            "alternative_receipts": [],
        }

    @property
    def root_id(self) -> str:
        return self.snapshot()["root_id"]

    def snapshot(self) -> dict[str, Any]:
        run = self.store.run_record(scheduling=True)
        state = run.get("strategy_review")
        if (
            not isinstance(state, dict)
            or type(state.get("schema")) is not int
            or state["schema"] != 1
        ):
            raise ResearchStoreError(
                "missing or unsupported strategy controller schema"
            )
        if state["root_binding"] != _digest(self.store.get_claim(run["target_id"])):
            raise ResearchStoreError("strategy original root binding changed")
        if bool(state.get("original_lean")) != bool(
            state.get("original_anchor")
        ) or state.get("original_anchor") != run.get("original_target_anchor"):
            raise ValueError("original capture anchor or pin is missing")
        if state.get("original_lean"):
            pin, anchor = state["original_lean"], state.get("original_anchor")
            if (
                not anchor
                or pin["binding"] != anchor["binding"]
                or pin["original_source_sha256"] != anchor["source_artifact"]
                or pin["artifact"] != anchor["artifact"]
                or anchor["source_artifact"] not in run["sources"].values()
            ):
                raise ResearchStoreError("strategy original capture anchor changed")
        return state

    @contextmanager
    def _edit(self) -> Iterator[tuple[dict[str, Any], dict[str, Any]]]:
        # DiscoveryStore._transaction permits composing mutations in its owner
        # atomic block, while a read-only snapshot remains protected by store.
        with nullcontext() if self.store._applying else self.store.atomic():
            state = self.snapshot()
            run = self.store.run_record(scheduling=True)
            yield state, run
            run["strategy_review"] = state
            self.store.save_run(run)

    def _event(self, state: dict[str, Any], kind: str, **payload: Any) -> None:
        state["events"].append(
            {
                "sequence": len(state["events"]) + 1,
                "kind": kind,
                "time": self.clock(),
                **payload,
            }
        )

    @staticmethod
    def _generation(state: dict[str, Any]) -> int:
        state["generation"] += 1
        return state["generation"]

    def subject(self, subject_id: str) -> dict[str, Any]:
        try:
            return self.snapshot()["subjects"][subject_id]
        except KeyError as exc:
            raise ValueError("unknown strategy subject handle") from exc

    def register_subject(
        self, statement: str, *, parent_id: str | None = None, formal_context: str = ""
    ) -> dict[str, Any]:
        statement = text(statement, "exact subject statement")
        formal_identity = _digest(
            {"statement": statement.strip(), "context": formal_context}
        )
        subject_id = "subject-" + formal_identity
        with self._edit() as (state, _):
            if parent_id is not None and parent_id not in state["subjects"]:
                raise ValueError("unknown parent subject")
            subject = state["subjects"].setdefault(
                subject_id,
                self._new_subject(
                    subject_id, statement, parent_id or "", formal_identity
                ),
            )
            subject["formal_context"] = formal_context
            if (
                parent_id
                and parent_id != subject_id
                and parent_id not in subject["parent_ids"]
            ):
                subject["parent_ids"].append(parent_id)
            self._refresh_dispositions(state)
            result = deepcopy(subject)
            aliases = [
                item
                for item in state["subjects"].values()
                if item["subject_id"] != subject_id
                and item["statement"].strip() == statement.strip()
                and item["disposition"] == "suspended"
            ]
        # Context changes never imply semantic equality. Route a potential
        # duplicate to independent applicability review, with a capped lease.
        for old in aliases[:1]:
            review = self.request_implication(
                subject_id,
                old["subject_id"],
                argument="Same proposition text in changed formal context. Independently compare both contexts, including instances and notation; an added helper may or may not preserve the claim.",
                artifact_ids=[],
                author="owner-context-correspondence",
            )
            if (
                not review.get("preliminary_hold_installed")
                and review["status"] == "review_pending"
            ):
                try:
                    self.preliminary_hold(
                        review["review_id"],
                        seconds=self.snapshot()["policy"]["reserve_seconds"],
                    )
                except ValueError:
                    pass  # The fixed cap cannot be renewed by repeated entry.
        return result

    @staticmethod
    def _reservations(state: dict[str, Any]) -> int:
        return sum(
            a["request_limit"] - a["requests_used"]
            for a in state["allocations"].values()
            if a["status"] == "active"
        )

    def _blocked(
        self, state: dict[str, Any], subject_ids: list[str], method: str
    ) -> str | None:
        required = set(subject_ids)
        # A proof of B implying A permits an allocation objection against A to
        # restrict B. The reverse implication does not have that consequence.
        while True:
            expanded = required | {
                item["consequence"]
                for item in state["implications"]
                if item["premise"] in required
                and state["reviews"].get(item.get("review_id"), {}).get("status")
                == "applicable"
                and not state["reviews"][item["review_id"]].get("superseded_by")
            }
            if expanded == required:
                break
            required = expanded
        for hold in state["holds"].values():
            if hold["subject_id"] not in required:
                continue
            if hold["expires_at"] is not None and self.clock() >= hold["expires_at"]:
                continue
            if (
                hold["scope"] in {"method_barrier", "unsupported_bridge"}
                and hold["method"] != method
            ):
                continue
            return hold["subject_id"]
        return None

    def _refresh_dispositions(self, state: dict[str, Any]) -> None:
        for subject in state["subjects"].values():
            held = any(
                h["subject_id"] == subject["subject_id"]
                and h["scope"] == "claim_contradiction"
                and (h["expires_at"] is None or self.clock() < h["expires_at"])
                for h in state["holds"].values()
            )
            subject["disposition"] = "suspended" if held else "candidate"

    def allocate(
        self,
        subject_id: str,
        consumer_id: str,
        *,
        method: str,
        settlement_only: bool = False,
        settlement_seconds: float = 30,
    ) -> dict[str, Any]:
        self.expire_holds()
        method = text(method, "method")
        with self._edit() as (state, run):
            subject = state["subjects"].get(subject_id)
            if subject is None:
                raise ValueError("unknown strategy subject")
            consumer = self.store.job(consumer_id)
            if not settlement_only and self._blocked(state, [subject_id], method):
                raise StrategyYield("suspended", subject_id=subject_id)
            prepared = None
            if self._frontier_mode(state) == "adaptive" and not settlement_only:
                from .frontier.hooks import authorize_prepare

                prepared = authorize_prepare(
                    self, state, run, subject_id, consumer_id, method
                )
            elif (
                not settlement_only
                and subject["no_progress_intervals"]
                - subject["alternative_after_interval"]
                >= state["policy"]["max_no_progress"]
            ):
                raise StrategyYield("alternative_required", subject_id=subject_id)
            for previous in state["allocations"].values():
                if (prepared is not None and previous["status"] == "prepared"
                        and consumer_id in previous["consumers"]
                        and previous.get("frontier_permit_id")
                        and previous.get("frontier_permit_id") != prepared.get("permit_id")):
                    from .frontier.hooks import release_prepared

                    # An explicitly replaced permit fences the old preparation.
                    # Its old claim may be released; the fresh claim stays held.
                    release_prepared(self, state, run, previous)
                if (
                    consumer_id in previous["consumers"]
                    and previous["status"] in {"active", "prepared"}
                    and not previous.get("consumer_bindings", {})
                    .get(consumer_id, {})
                    .get("released")
                ):
                    raise ValueError("consumer already has an active or prepared allocation")
            policy = state["policy"]
            available = (
                run["max_requests"]
                - run["requests_used"]
                - policy["reserve_requests"]
                - self._reservations(state)
            )
            seconds = min(
                policy["interval_seconds"],
                (run["deadline"] or self.clock() + run["max_seconds"])
                - self.clock()
                - policy["reserve_seconds"],
            )
            if settlement_only:
                seconds = min(300, _seconds(settlement_seconds, "settlement seconds"))
                available = (
                    1  # Satisfy local eligibility; grants zero dispatches below.
                )
            if available <= 0 or seconds <= 0:
                raise StrategyYield("review_reserve", subject_id=subject_id)
            allocation_id = "allocation-" + uuid.uuid4().hex
            generation = self._generation(state)
            subject["generation"] = generation
            allocation = {
                "allocation_id": allocation_id,
                "subject_id": subject_id,
                "subjects": [subject_id],
                "consumer_id": consumer_id,
                "consumers": [consumer_id],
                "method": method,
                "consumer_turn": consumer["turn"],
                "claim_id": consumer["claim_id"],
                "claim_revision": consumer["revision"],
                "generation": generation,
                "owner_id": state["owner_id"],
                "process_id": os.getpid(),
                "request_limit": 0
                if settlement_only or prepared is not None
                else min(policy["interval_requests"], available),
                "requests_used": 0,
                "settlement_only": settlement_only,
                "producer_interval": subject["interval_sequence"] + 1,
                "expires_at": self.clock() + seconds,
                "started_at": self.clock(),
                "status": "prepared" if prepared is not None else "active",
                "interval_recorded": False,
                "consumer_bindings": {
                    consumer_id: {
                        "consumer_turn": consumer["turn"],
                        "claim_id": consumer["claim_id"],
                        "claim_revision": consumer["revision"],
                        "released": False,
                        "subjects": [subject_id],
                    }
                },
            }
            if prepared is not None:
                allocation.update(
                    frontier_approach_id=prepared["approach_id"],
                    frontier_permit_id=prepared["permit_id"],
                    frontier_claim_id=prepared["claim_id"],
                    frontier_handoff_id=prepared.get("handoff_id"),
                    frontier_handoff_producer=prepared.get("producer_id"),
                )
                allocation["frontier_basis"] = self._frontier_allocation_basis(state, allocation)
            state["allocations"][allocation_id] = allocation
            self._event(
                state,
                "allocation_started",
                allocation_id=allocation_id,
                subject_id=subject_id,
            )
            return deepcopy(allocation)

    def _check(
        self,
        state: dict[str, Any],
        run: dict[str, Any],
        lease: dict[str, Any],
        *,
        dispatch: bool = False,
    ) -> dict[str, Any]:
        current = state["allocations"].get(lease.get("allocation_id"))
        subject_id = lease.get("subject_id", "")
        if current is None or lease.get("owner_id") != state["owner_id"]:
            raise StrategyYield("missing_owner_binding", subject_id=subject_id)
        if current.get("frontier_approach_id") and not current.get("settlement_only"):
            if current.get("frontier_basis") != self._frontier_allocation_basis(state, current):
                raise StrategyYield("stale_frontier_scope", subject_id=subject_id, allocation_id=current["allocation_id"])
        consumer_binding = current.get("consumer_bindings", {}).get(
            lease.get("consumer_id"), {}
        )
        blocked = self._blocked(
            state,
            consumer_binding.get("subjects", current["subjects"]),
            current["method"],
        )
        if blocked and not current.get("settlement_only"):
            raise StrategyYield(
                "suspended", subject_id=blocked, allocation_id=current["allocation_id"]
            )
        if (
            any(lease.get(key) != current[key] for key in ("generation", "process_id"))
            or current["process_id"] != os.getpid()
            or current["status"] != "active" and not (current["status"] == "prepared" and not dispatch)
        ):
            raise StrategyYield(
                "stale_lease",
                subject_id=subject_id,
                allocation_id=current["allocation_id"],
            )
        self._check_consumer(current, lease.get("consumer_id"))
        if run["status"] != "running" and not (
            current.get("settlement_only")
            and run["status"] in {"budget_exhausted", "deadline_exhausted"}
        ):
            raise StrategyYield(
                "run_not_active",
                subject_id=subject_id,
                allocation_id=current["allocation_id"],
            )
        if (
            self.clock() >= current["expires_at"]
            or dispatch
            and current["requests_used"] >= current["request_limit"]
        ):
            raise StrategyYield(
                "interval_exhausted",
                subject_id=subject_id,
                allocation_id=current["allocation_id"],
            )
        return current

    def _check_consumer(
        self, current: dict[str, Any], consumer_id: str | None = None
    ) -> None:
        consumer_id = consumer_id or current["consumer_id"]
        bound = current.get("consumer_bindings", {current["consumer_id"]: current}).get(
            consumer_id
        )
        if bound is None or bound.get("released") or bound.get("revoked"):
            raise StrategyYield(
                "stale_consumer",
                subject_id=current["subject_id"],
                allocation_id=current["allocation_id"],
            )
        consumer = self.store.job(consumer_id)
        if (
            consumer["status"] != "running"
            or consumer["turn"] != bound["consumer_turn"]
            or consumer["claim_id"] != bound["claim_id"]
            or consumer["revision"] != bound["claim_revision"]
            or self.store.get_claim(bound["claim_id"])["revision"]
            != bound["claim_revision"]
        ):
            raise StrategyYield(
                "stale_consumer",
                subject_id=current["subject_id"],
                allocation_id=current["allocation_id"],
            )

    def join_consumer(self, lease: dict[str, Any], consumer_id: str) -> dict[str, Any]:
        """Share remaining requests/time; joining never creates a new budget."""
        with self._edit() as (state, run):
            allocation = self._check(state, run, lease)
            consumer = self.store.job(consumer_id)
            if (
                consumer["status"] != "running"
                or self.store.get_claim(consumer["claim_id"])["revision"]
                != consumer["revision"]
            ):
                raise ValueError("shared consumer must be current and running")
            if any(
                a["status"] == "active"
                and consumer_id in a["consumers"]
                and not a.get("consumer_bindings", {})
                .get(consumer_id, {})
                .get("released")
                for a in state["allocations"].values()
            ):
                raise ValueError("consumer already funded by an active interval")
            bindings = allocation["consumer_bindings"]
            if consumer_id in bindings:
                raise ValueError("consumer already joined this interval")
            bindings[consumer_id] = {
                "consumer_turn": consumer["turn"],
                "claim_id": consumer["claim_id"],
                "claim_revision": consumer["revision"],
                "released": False,
                "subjects": [allocation["subject_id"]],
            }
            allocation["consumers"].append(consumer_id)
            self._event(
                state,
                "consumer_joined",
                allocation_id=allocation["allocation_id"],
                consumer_id=consumer_id,
            )
            return {**deepcopy(allocation), "consumer_id": consumer_id}

    def check(self, lease: dict[str, Any]) -> None:
        self.expire_holds()
        with self.store.read_snapshot():
            self._check(self.snapshot(), self.store.run_record(scheduling=True), lease)

    def attach_subject(self, lease: dict[str, Any], subject_id: str) -> None:
        with self._edit() as (state, run):
            allocation = self._check(state, run, lease)
            if subject_id not in state["subjects"]:
                raise ValueError("unknown subject")
            if not allocation.get("settlement_only") and self._blocked(
                state, [subject_id], allocation["method"]
            ):
                raise StrategyYield(
                    "suspended",
                    subject_id=subject_id,
                    allocation_id=allocation["allocation_id"],
                )
            if subject_id not in allocation["subjects"]:
                allocation["subjects"].append(subject_id)
            subjects = allocation["consumer_bindings"][lease["consumer_id"]]["subjects"]
            if subject_id not in subjects:
                subjects.append(subject_id)

    def admit(
        self, lease: dict[str, Any], attempt_id: str, *, operation_seconds: float,
        provider_request_key: str | None = None,
    ) -> dict[str, Any]:
        text(attempt_id, "single-use attempt ID")
        _seconds(operation_seconds, "operation_seconds")
        with self._edit() as (state, run):
            if attempt_id in state["attempts"]:
                raise StrategyYield(
                    "attempt_reused", allocation_id=lease.get("allocation_id", "")
                )
            current = state["allocations"].get(lease.get("allocation_id"))
            if (
                current is not None
                and current.get("status") == "prepared"
                and self._frontier_mode(state) == "adaptive"
            ):
                from .frontier.hooks import activate_prepared

                activate_prepared(self, state, run, current)
            allocation = self._check(state, run, lease, dispatch=True)
            if allocation.get("frontier_handoff_id"):
                from .frontier.hooks import check_handoff_admission

                check_handoff_admission(self, state, run, allocation)
            if provider_request_key and self._frontier_mode(state) == "adaptive":
                from .frontier.persist import load_campaign, save_campaign
                from .frontier.records import FrontierRefusal
                from .frontier.retry import authorize_execution

                campaign = load_campaign(self.store, state["owner_id"])
                lineage = "proof-request:" + _digest({"basis": allocation["frontier_basis"], "request": provider_request_key})
                try:
                    authorize_execution(campaign, lineage, lane_id="provider", now=self.clock(),
                                        deadline=min(allocation["expires_at"], run["deadline"]))
                except FrontierRefusal as exc:
                    refusal = StrategyYield(exc.reason, allocation_id=allocation["allocation_id"])
                    refusal.frontier_request_lineage = lineage
                    raise refusal from exc
                save_campaign(self.store, state["owner_id"], run["target_id"], campaign)
            if (
                run["requests_used"]
                >= run["max_requests"] - state["policy"]["reserve_requests"]
            ):
                raise StrategyYield(
                    "review_reserve", allocation_id=allocation["allocation_id"]
                )
            if run["deadline"] is None or self.clock() + operation_seconds > min(
                allocation["expires_at"],
                run["deadline"] - state["policy"]["reserve_seconds"],
            ):
                raise StrategyYield(
                    "review_reserve", allocation_id=allocation["allocation_id"]
                )
            allocation["requests_used"] += 1
            run["requests_used"] += 1
            receipt = {
                "attempt_id": attempt_id,
                "allocation_id": allocation["allocation_id"],
                "generation": allocation["generation"],
                "consumer_id": lease["consumer_id"],
                "process_id": os.getpid(),
                "status": "exposure_claimed",
                "artifacts": [],
                "ingress_deadline": min(
                    run["deadline"],
                    self.clock()
                    + operation_seconds
                    + state["policy"]["reserve_seconds"],
                ),
            }
            state["attempts"][attempt_id] = receipt
            self._event(
                state,
                "dispatch_admitted",
                attempt_id=attempt_id,
                allocation_id=allocation["allocation_id"],
            )
            return deepcopy(receipt)

    def admit_control(self, attempt_id: str, job_id: str, turn: int, *, retry: bool = False) -> dict[str, Any]:
        """Research and review spend reserved capacity through the same ledger."""
        with self._edit() as (state, run):
            job = self.store.job(job_id)
            if attempt_id in state["attempts"]:
                raise StrategyYield("attempt_reused")
            if job["status"] != "running" or job["turn"] != turn:
                raise StrategyYield("stale_job")
            if self.store.get_claim(job["claim_id"])["revision"] != job["revision"]:
                raise StrategyYield("claim_changed")
            if (
                run["status"] != "running"
                or self.clock() >= run["deadline"]
                or run["requests_used"] + self._reservations(state)
                >= run["max_requests"]
            ):
                raise StrategyYield("global_limit")
            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import authorize_control_admission

                job.pop("frontier_lane_probe", None)
                if retry:
                    job["frontier_retry_pending"] = True
                authorize_control_admission(self, state, run, job)
            from .research_control import admit_research

            admit_research(self.store, job, state, run, self.clock(), self._reservations(state))
            run["requests_used"] += 1
            receipt = {
                "attempt_id": attempt_id,
                "allocation_id": None,
                "admitted_at": self.clock(),
                "consumer_id": job_id,
                "consumer_turn": turn,
                "status": "exposure_claimed",
                "process_id": os.getpid(),
                "artifacts": [],
                "ingress_deadline": run["deadline"],
            }
            if job.get("frontier_approach_allocation_id"):
                receipt["approach_allocation_id"] = job["frontier_approach_allocation_id"]
            if self._frontier_mode(state) == "adaptive":
                from .frontier.tool_runtime import dispatch_binding

                receipt["frontier_binding"] = dispatch_binding(self.store, state, job)
                receipt["frontier_lane_probe"] = bool(job.get("frontier_lane_probe"))
                receipt["frontier_operation_lineage"] = job.get("frontier_operation_lineage")
            state["attempts"][attempt_id] = receipt
            self._event(
                state,
                "research_dispatch_admitted",
                attempt_id=attempt_id,
                job_id=job_id,
            )
            return deepcopy(receipt)

    def settle(self, attempt_id: str, *, outcome: str) -> None:
        if outcome not in {"completed", "unknown", "failed"}:
            raise ValueError("invalid attempt settlement")
        with self._edit() as (state, _):
            receipt = state["attempts"][attempt_id]
            if (
                receipt["status"] == "exposure_claimed"
                or receipt["status"] == "unknown"
                and outcome == "completed"
            ):
                receipt["status"] = outcome
            self._event(
                state,
                "attempt_settled",
                attempt_id=attempt_id,
                outcome=receipt["status"],
            )

    def receive_artifact(self, attempt_id: str, content: bytes) -> str:
        if not isinstance(content, bytes) or len(content) > self.MAX_ARTIFACT_BYTES:
            raise ValueError("artifact ingress size exceeded")
        with self._edit() as (state, _):
            attempt = state["attempts"].get(attempt_id)
            if attempt is None or self.clock() > attempt["ingress_deadline"]:
                raise ValueError("artifact ingress expired or unknown")
            digest = hashlib.sha256(content).hexdigest()
            if digest not in attempt["artifacts"]:
                if len(attempt["artifacts"]) >= self.MAX_ARTIFACTS_PER_ATTEMPT:
                    raise ValueError("artifact ingress count exceeded")
                self.store.put_artifact(content, name="strategy-candidate")
                attempt["artifacts"].append(digest)
            return digest

    def note_operational_yield(self, lease: dict[str, Any], outcome: dict[str, Any]) -> None:
        """Persist operational refusal before any enclosing scope settles work."""
        reasons = {"retry_exhausted", "retry_deadline", "paused_operational", "provider_timeout",
                   "provider_failure", "context_overflow", "proof_context_overflow"}
        if outcome.get("reason") not in reasons:
            return
        with self._edit() as (state, run):
            if self._frontier_mode(state) != "adaptive":
                return
            allocation = state["allocations"][lease["allocation_id"]]
            allocation["frontier_operational"] = True
            allocation["frontier_explanation"] = outcome["reason"]
            lineage = outcome.get("frontier_request_lineage")
            if lineage:
                from .frontier.persist import load_campaign, save_campaign

                campaign = load_campaign(self.store, state["owner_id"])
                budget = campaign["retries"].get(lineage)
                if budget is not None:
                    budget["paused"] = True
                    campaign["approaches"][allocation["frontier_approach_id"]]["operation_lineage"] = lineage
                    allocation["frontier_operation_lineage"] = lineage
                    save_campaign(self.store, state["owner_id"], run["target_id"], campaign)

    def finish_interval(
        self,
        lease: dict[str, Any],
        *,
        progress: bool = False,
        progress_receipt: str | None = None,
    ) -> None:
        with self._edit() as (state, _):
            allocation = state["allocations"][lease["allocation_id"]]
            if progress:
                receipt = state["reviews"].get(progress_receipt or "", {})
                if (
                    allocation["generation"] != lease["generation"]
                    or allocation["status"] != "active"
                    or receipt.get("status") != "progress"
                    or receipt.get("allocation_id") != allocation["allocation_id"]
                    or receipt.get("subject_id") != allocation["subject_id"]
                    or receipt.get("progress_consumed")
                ):
                    raise ValueError(
                        "current independent single-use progress assessment required"
                    )
                self._check_consumer(allocation, lease.get("consumer_id"))
                allocation["pending_progress_receipt"] = progress_receipt
            if allocation.get("status") == "prepared":
                from .frontier.hooks import release_prepared

                release_prepared(self, state, self.store.run_record(scheduling=True), allocation)
                return
            if allocation["interval_recorded"]:
                return
            bindings = allocation.get("consumer_bindings", {})
            if bindings:
                if lease.get("consumer_id") not in bindings:
                    raise ValueError("unknown interval consumer")
                bindings[lease["consumer_id"]]["released"] = True
                live = False
                for consumer_id in bindings:
                    try:
                        self._check_consumer(allocation, consumer_id)
                        live = True
                    except StrategyYield:
                        pass
                if live:
                    return
            self._record_interval(state, allocation)

    def _record_interval(
        self, state: dict[str, Any], allocation: dict[str, Any]
    ) -> None:
        """Settle one research interval identically on release and owner restart."""
        if self._frontier_mode(state) == "adaptive":
            from .frontier.hooks import settle_adaptive_interval

            settle_adaptive_interval(self, state, allocation)
            return
        progress = False
        progress_receipt = None
        pending = allocation.get("pending_progress_receipt")
        if (
            pending
            and state["reviews"][pending].get("status") == "progress"
            and not state["reviews"][pending].get("progress_consumed")
        ):
            progress, progress_receipt = True, pending
            state["reviews"][pending]["progress_consumed"] = True
        if allocation.get("settlement_only"):
            allocation.update(
                status="yielded",
                interval_recorded=True,
                generation=self._generation(state),
            )
            return
        subject = state["subjects"][allocation["subject_id"]]
        subject["interval_sequence"] += 1
        allocation.update(
            status="yielded",
            interval_recorded=True,
            generation=self._generation(state),
        )
        allocation["finished_interval"] = subject["interval_sequence"]
        subject["generation"] = allocation["generation"]
        if progress:
            subject["progress_receipts"].append(progress_receipt)
            subject.update(no_progress_intervals=0, alternative_after_interval=0)
        else:
            subject["no_progress_intervals"] += 1
        self._event(
            state,
            "interval_finished",
            allocation_id=allocation["allocation_id"],
            progress=progress,
        )
        if self._frontier_mode(state) == "observe":
            from .frontier.hooks import note_observed_interval

            note_observed_interval(self, state, allocation, progress=progress)

    @staticmethod
    def _review_key(scope: str, method: str) -> str:
        return (
            scope
            + ":"
            + (method if scope in {"method_barrier", "unsupported_bridge"} else "")
        )

    @classmethod
    def _review_basis(
        cls, subject: dict[str, Any], scope: str, method: str
    ) -> dict[str, Any]:
        relevant = {cls._review_key(scope, method), "claim_contradiction:"}
        return {
            "formal_identity": subject["formal_identity"],
            "evidence_revision": {
                key: subject["evidence_tokens"].get(key, 0) for key in sorted(relevant)
            },
            "decision_generation": {
                key: subject["decision_tokens"].get(key, 0) for key in sorted(relevant)
            },
        }

    def request_review(
        self,
        subject_id: str,
        *,
        scope: str,
        argument: str,
        artifact_ids: list[str],
        author: str,
        method: str = "",
        supersedes: list[str] | None = None,
    ) -> dict[str, Any]:
        if scope not in self.SCOPES:
            raise ValueError("unknown strategy review scope")
        argument = text(argument, "complete applicability argument")
        text(author, "review requester")
        if not isinstance(artifact_ids, list) or any(
            not isinstance(aid, str) for aid in artifact_ids
        ):
            raise ValueError("artifact_ids must be an array of artifact IDs")
        for aid in artifact_ids:
            self.store.read_artifact(aid)
        supersedes = list(supersedes or [])
        with self._edit() as (state, _):
            subject = state["subjects"].get(subject_id)
            if subject is None:
                raise ValueError("unknown subject handle")
            for rid in supersedes:
                if (
                    rid not in state["reviews"]
                    or state["reviews"][rid]["subject_id"] != subject_id
                ):
                    raise ValueError("superseded review must belong to exact subject")
            identity = _digest(
                [
                    subject_id,
                    scope,
                    method,
                    argument,
                    sorted(artifact_ids),
                    sorted(supersedes),
                ]
            )
            duplicate = next(
                (
                    r
                    for r in reversed(list(state["reviews"].values()))
                    if r["identity"] == identity and r["status"] != "stale"
                ),
                None,
            )
            if duplicate is not None:
                return deepcopy(duplicate)
            # A stale assessment needs a new decision basis, but its unchanged
            # objection is already in the evidence ledger. Counting retries as
            # new evidence lets two queued objections invalidate each other
            # forever before either independent decision can become current.
            if not any(r["identity"] == identity for r in state["reviews"].values()):
                subject["evidence_revision"] += 1
                key = self._review_key(scope, method)
                subject["evidence_tokens"][key] = subject["evidence_tokens"].get(key, 0) + 1
            review_id = "strategy-review-" + uuid.uuid4().hex
            review = {
                "review_id": review_id,
                "identity": identity,
                "subject_id": subject_id,
                "scope": scope,
                "method": method,
                "argument": argument,
                "artifact_ids": artifact_ids,
                "author": author,
                "supersedes": supersedes,
                "status": "review_pending",
                "job_id": None,
                "basis": self._review_basis(subject, scope, method),
                "supersession_basis": {
                    rid: self._decision_identity(state["reviews"][rid])
                    for rid in supersedes
                },
            }
            state["reviews"][review_id] = review
            self._event(
                state,
                "strategy_review_requested",
                review_id=review_id,
                subject_id=subject_id,
            )
            return deepcopy(review)

    def _revoke(
        self, state: dict[str, Any], subject_id: str, scope: str, method: str
    ) -> None:
        generation = self._generation(state)
        state["subjects"][subject_id]["generation"] = generation
        for allocation in state["allocations"].values():
            if (
                allocation["status"] == "active"
                and not allocation.get("settlement_only")
                and self._blocked(state, allocation["subjects"], allocation["method"])
            ):
                bindings = allocation.get("consumer_bindings", {})
                for bound in bindings.values():
                    if self._blocked(state, bound["subjects"], allocation["method"]):
                        bound["revoked"] = True
                if any(
                    not bound.get("revoked") and not bound.get("released")
                    for bound in bindings.values()
                ):
                    continue
                allocation.update(status="suspended", generation=generation)
                if not allocation["interval_recorded"]:
                    if self._frontier_mode(state) == "adaptive":
                        allocation["frontier_revoked"] = True
                        self._record_interval(state, allocation)
                        allocation["status"] = "suspended"
                        continue
                    allocation["interval_recorded"] = True
                    state["subjects"][allocation["subject_id"]][
                        "no_progress_intervals"
                    ] += 1
                    state["subjects"][allocation["subject_id"]][
                        "interval_sequence"
                    ] += 1
                    allocation["finished_interval"] = state["subjects"][
                        allocation["subject_id"]
                    ]["interval_sequence"]

    def preliminary_hold(self, review_id: str, *, seconds: float) -> None:
        _seconds(seconds, "hold seconds")
        with self._edit() as (state, _):
            review = state["reviews"][review_id]
            if review.get("preliminary_hold_installed"):
                raise ValueError("preliminary hold already installed")
            if review["status"] != "review_pending":
                raise ValueError("review is no longer pending")
            subject_holds = sum(
                bool(r.get("preliminary_hold_installed"))
                for r in state["reviews"].values()
                if r["subject_id"] == review["subject_id"]
            )
            if subject_holds >= 2:
                raise ValueError("preliminary hold cap reached")
            review["preliminary_hold_installed"] = True
            state["holds"][review_id] = {
                key: review[key] for key in ("subject_id", "scope", "method")
            }
            state["holds"][review_id]["expires_at"] = self.clock() + min(
                seconds, state["policy"]["reserve_seconds"]
            )
            self._revoke(state, review["subject_id"], review["scope"], review["method"])
            self._refresh_dispositions(state)
            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import sync_strategy_holds

                sync_strategy_holds(self, state, self.store.run_record(scheduling=True))

    def expire_holds(self) -> None:
        with self._edit() as (state, _):
            for review_id, hold in list(state["holds"].items()):
                if (
                    hold["expires_at"] is not None
                    and self.clock() >= hold["expires_at"]
                ):
                    del state["holds"][review_id]
                    state["subjects"][hold["subject_id"]]["generation"] = (
                        self._generation(state)
                    )
                    self._event(state, "preliminary_hold_expired", review_id=review_id)
            self._refresh_dispositions(state)

            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import sync_strategy_holds

                sync_strategy_holds(self, state, self.store.run_record(scheduling=True))

    @staticmethod
    def _decision_identity(review: dict[str, Any]) -> dict[str, Any]:
        return {key: review.get(key) for key in ("status", "verdict", "superseded_by")}

    def decide(self, review_id: str, verdict: str, *, rationale: str) -> dict[str, Any]:
        if verdict not in {"hold", "dismiss", "unresolved"}:
            raise ValueError("invalid allocation review verdict")
        text(rationale, "independent review rationale")
        with self._edit() as (state, _):
            review = state["reviews"][review_id]
            if review["status"] != "review_pending":
                return deepcopy(review)
            subject = state["subjects"][review["subject_id"]]
            basis = self._review_basis(subject, review["scope"], review["method"])
            review.update(rationale=rationale, verdict=verdict)
            supersession_basis = {
                rid: self._decision_identity(state["reviews"][rid])
                for rid in review["supersedes"]
            }
            if (
                review["basis"] != basis
                or review["supersession_basis"] != supersession_basis
            ):
                review["status"] = "stale"
                return deepcopy(review)
            review["status"] = "reviewed_hold" if verdict == "hold" else verdict
            subject["decision_generation"] += 1
            key = self._review_key(review["scope"], review["method"])
            subject["decision_tokens"][key] = subject["decision_tokens"].get(key, 0) + 1
            subject["generation"] = self._generation(state)
            if verdict != "unresolved":
                for rid in review["supersedes"]:
                    state["holds"].pop(rid, None)
                    state["reviews"][rid]["superseded_by"] = review_id
            state["holds"].pop(review_id, None)
            if verdict == "hold":
                state["holds"][review_id] = {
                    key: review[key] for key in ("subject_id", "scope", "method")
                }
                state["holds"][review_id]["expires_at"] = None
                self._revoke(
                    state, review["subject_id"], review["scope"], review["method"]
                )
            self._refresh_dispositions(state)
            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import sync_strategy_holds

                sync_strategy_holds(self, state, self.store.run_record(scheduling=True))
            if self._frontier_mode(state) == "adaptive" and verdict == "dismiss":
                from .frontier.hooks import restore_subject

                restore_subject(self, state, review["subject_id"])
            self._event(
                state,
                "strategy_review_decided",
                review_id=review_id,
                verdict=verdict,
                subject_id=subject["subject_id"],
            )
            return deepcopy(review)

    def bind_review_job(self, review_id: str, job_id: str) -> None:
        with self._edit() as (state, _):
            review = state["reviews"][review_id]
            if review["job_id"] not in {None, job_id}:
                raise ValueError("review already assigned")
            review["job_id"] = job_id

    @staticmethod
    def _credited_progress_artifacts(
        state: dict[str, Any], subject_id: str
    ) -> set[str]:
        """Include approved work awaiting interval settlement in single-use credit."""
        return {
            aid
            for review in state["reviews"].values()
            if review.get("kind") == "progress"
            and review["subject_id"] == subject_id
            and review["status"] == "progress"
            for aid in review["artifact_ids"]
        }

    def _frontier_allocation_basis(self, state: dict[str, Any], allocation: dict[str, Any]) -> dict[str, Any]:
        from .frontier.persist import load_campaign

        campaign = load_campaign(self.store, state["owner_id"])
        approach_id = allocation["frontier_approach_id"]
        approach = campaign["approaches"][approach_id]
        return {
            "root_binding": campaign["root"]["binding"],
            "approach_id": approach_id,
            "subject_identity": state["subjects"][allocation["subject_id"]]["formal_identity"],
            "question_id": approach["question_id"],
            "question_revision": campaign["questions"][approach["question_id"]]["revision"],
            "route_id": approach["route_id"],
            "route_revision": campaign["routes"][approach["route_id"]]["revision"],
        }

    def _progress_basis(self, state: dict[str, Any], allocation: dict[str, Any], *, current: bool = False) -> dict[str, Any]:
        """A sibling method cannot obsolete this approach's independent assessment."""
        subject = state["subjects"][allocation["subject_id"]]
        approach_id = allocation.get("frontier_approach_id")
        if self._frontier_mode(state) != "adaptive" or not approach_id:
            return {"generation": subject["generation"], "interval_sequence": subject["interval_sequence"]}
        if not current and not allocation.get("frontier_basis"):
            raise ValueError("allocation lacks an immutable frontier scope")
        basis = self._frontier_allocation_basis(state, allocation) if current else deepcopy(allocation["frontier_basis"])
        settled = [item for item in state["allocations"].values()
                   if item.get("frontier_approach_id") == approach_id and item["interval_recorded"]
                   and isinstance(item.get("finished_interval"), int)]
        basis["settled_allocations"] = [item["allocation_id"] for item in sorted(settled, key=lambda item: item["finished_interval"])]
        return basis

    def request_progress(
        self, allocation_id: str, *, artifact_ids: list[str], argument: str, author: str
    ) -> dict[str, Any]:
        """Ask an independent worker whether actual work advanced the bottleneck."""
        with nullcontext() if self.store._applying else self.store.atomic():
            with self._edit() as (state, _):
                allocation = state["allocations"][allocation_id]
                admitted = {
                    aid
                    for attempt in state["attempts"].values()
                    if attempt["allocation_id"] == allocation_id
                    for aid in attempt["artifacts"]
                }
                if not artifact_ids or not set(artifact_ids) <= admitted:
                    raise ValueError(
                        "progress must reference artifacts from this admitted attempt"
                    )
                subject = state["subjects"][allocation["subject_id"]]
                basis = self._progress_basis(state, allocation)
                if basis != self._progress_basis(state, allocation, current=True):
                    raise ValueError("progress belongs to a stale frontier scope")
                superseded = (
                    allocation.get("finished_interval") != subject["interval_sequence"]
                    if "approach_id" not in basis
                    else bool(basis["settled_allocations"] and basis["settled_allocations"][-1] != allocation_id)
                )
                if allocation.get("progress_credited") or (
                    allocation["interval_recorded"]
                    and superseded
                ):
                    raise ValueError(
                        "progress belongs to a previously credited or superseded interval"
                    )
                credited = self._credited_progress_artifacts(
                    state, subject["subject_id"]
                )
                if set(artifact_ids) & credited:
                    raise ValueError("progress evidence already credited")
            review = self.request_review(
                allocation["subject_id"],
                scope="allocation_exhausted",
                argument=f"Progress assessment for {allocation_id}: {argument}",
                artifact_ids=artifact_ids,
                author=author,
            )
            with self._edit() as (state, _):
                current = state["reviews"][review["review_id"]]
                # Repeating an investigator's request cannot change the basis
                # another worker was assigned. A stale assessment needs a new
                # review ID before it can inspect a later allocation snapshot.
                if current["status"] == "review_pending" and "progress_basis" not in current:
                    current.update(
                        kind="progress",
                        allocation_id=allocation_id,
                        progress_basis=basis,
                    )
                return deepcopy(current)

    def decide_progress(
        self, review_id: str, *, relevant: bool, rationale: str
    ) -> dict[str, Any]:
        if type(relevant) is not bool:
            raise ValueError("progress relevance must be boolean")
        text(rationale, "independent progress rationale")
        with self._edit() as (state, _):
            review = state["reviews"][review_id]
            if review.get("kind") != "progress":
                raise ValueError("not an assigned progress assessment")
            if review["status"] != "review_pending":
                return deepcopy(review)
            subject = state["subjects"][review["subject_id"]]
            allocation = state["allocations"][review["allocation_id"]]
            current = self._progress_basis(state, allocation, current=True)
            review.update(
                rationale=rationale, verdict="relevant" if relevant else "unresolved"
            )
            if (
                allocation.get("progress_credited")
                or current != review["progress_basis"]
                or set(review["artifact_ids"])
                & self._credited_progress_artifacts(state, subject["subject_id"])
                or self._blocked(state, [subject["subject_id"]], allocation["method"])
            ):
                review["status"] = "stale"
            elif relevant:
                review["status"] = "progress"
                allocation["progress_credited"] = True
                if self._frontier_mode(state) == "adaptive":
                    from .frontier.hooks import note_progress

                    note_progress(self, state, review, formal=bool(review.get("frontier_formal")))
                    if not allocation["interval_recorded"]:
                        allocation["pending_progress_receipt"] = review_id
                    else:
                        review["progress_consumed"] = True
                elif not allocation["interval_recorded"]:
                    allocation["pending_progress_receipt"] = review_id
                else:
                    review["progress_consumed"] = True
                    subject["progress_receipts"].append(review_id)
                    subject.update(
                        no_progress_intervals=0, alternative_after_interval=0
                    )
            else:
                review["status"] = "unresolved"
            self._event(
                state,
                "progress_review_decided",
                review_id=review_id,
                status=review["status"],
            )
            return deepcopy(review)

    def request_implication(
        self,
        premise: str,
        consequence: str,
        *,
        argument: str,
        artifact_ids: list[str],
        author: str,
    ) -> dict[str, Any]:
        """Request B⇒A applicability; this never supplies a theorem certificate."""
        with nullcontext() if self.store._applying else self.store.atomic():
            state = self.snapshot()
            if (
                premise == consequence
                or premise not in state["subjects"]
                or consequence not in state["subjects"]
            ):
                raise ValueError("implication requires two distinct issued subjects")
            review = self.request_review(
                premise,
                scope="claim_contradiction",
                argument=f"Allocation applicability {premise} implies {consequence}: {text(argument, 'implication argument')}",
                artifact_ids=artifact_ids,
                author=author,
            )
            with self._edit() as (state, _):
                review = state["reviews"][review["review_id"]]
                if review["status"] == "review_pending":
                    review.update(
                        kind="implication",
                        premise=premise,
                        consequence=consequence,
                        relation_basis={
                            sid: state["subjects"][sid]["formal_identity"]
                            for sid in (premise, consequence)
                        },
                    )
                return deepcopy(review)

    def decide_implication(
        self, review_id: str, *, applicable: bool, rationale: str
    ) -> dict[str, Any]:
        if type(applicable) is not bool:
            raise ValueError("applicability must be boolean")
        text(rationale, "independent applicability rationale")
        with self._edit() as (state, _):
            review = state["reviews"][review_id]
            if review.get("kind") != "implication":
                raise ValueError("not an assigned implication review")
            if review["status"] != "review_pending":
                return deepcopy(review)
            review.update(rationale=rationale)
            if review["relation_basis"] != {
                sid: state["subjects"][sid]["formal_identity"]
                for sid in (review["premise"], review["consequence"])
            }:
                review["status"] = "stale"
            else:
                review["status"] = "applicable" if applicable else "unresolved"
                state["holds"].pop(review_id, None)
                if applicable:
                    state["implications"].append(
                        {
                            "premise": review["premise"],
                            "consequence": review["consequence"],
                            "review_id": review_id,
                        }
                    )
                    self._revoke(state, review["premise"], "claim_contradiction", "")
            self._refresh_dispositions(state)
            self._event(
                state,
                "implication_review_decided",
                review_id=review_id,
                status=review["status"],
            )
            return deepcopy(review)

    def record_alternative(
        self, subject_id: str, job_id: str, artifact_id: str
    ) -> None:
        """Owner records executed research, never a merely queued plan."""
        with self._edit() as (state, _):
            job = self.store.job(job_id)
            if (
                job["role"] != "research"
                or job["status"] != "finished"
                or job.get("alternative_for") != subject_id
                or not job.get("response")
                or job["turn"] < 1
            ):
                raise ValueError("alternative investigation has not executed")
            if not any(a["consumer_id"] == job_id for a in state["attempts"].values()):
                raise ValueError("alternative lacks a dispatch receipt")
            assessment = state["reviews"].get(job.get("alternative_assessment"), {})
            if (
                assessment.get("kind") != "alternative"
                or assessment.get("status") != "substantive"
                or assessment.get("producer_job") != job_id
                or assessment.get("subject_id") != subject_id
                or assessment.get("requirement") != job.get("alternative_requirement")
                or job.get("investigation_artifact") != artifact_id
                or assessment.get("artifact_ids") != [artifact_id]
            ):
                raise ValueError(
                    "alternative investigation requires an independent substantive assessment"
                )
            self.store.read_artifact(artifact_id)
            subject = state["subjects"][subject_id]
            if any(
                item["job_id"] == job_id or item["artifact_id"] == artifact_id
                for item in subject["alternative_receipts"]
            ):
                raise ValueError("alternative result already consumed")
            if job.get("alternative_requirement") != subject["interval_sequence"]:
                raise ValueError(
                    "alternative investigation belongs to a stale requirement"
                )
            if self._frontier_mode(state) == "adaptive":
                from .frontier.owner import report_scope_current
                from .frontier.persist import load_campaign

                campaign = load_campaign(self.store, state["owner_id"])
                if campaign is None or not report_scope_current(self, campaign, job):
                    raise ValueError("alternative investigation belongs to a stale frontier scope")
            receipt = {
                "job_id": job_id,
                "artifact_id": artifact_id,
                "interval": subject["no_progress_intervals"],
            }
            if receipt not in subject["alternative_receipts"]:
                subject["alternative_receipts"].append(receipt)
            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import grant_alternative

                grant_alternative(self, state, subject_id, job, artifact_id)
            else:
                subject["alternative_after_interval"] = subject["no_progress_intervals"]

    def recover(self) -> None:
        """A new owner process cannot revive an old dispatch permission."""
        with self._edit() as (state, _):
            for attempt in state["attempts"].values():
                if attempt["status"] == "exposure_claimed":
                    attempt["status"] = "unknown"
            for allocation in state["allocations"].values():
                if allocation.get("status") == "prepared":
                    from .frontier.hooks import release_prepared

                    release_prepared(self, state, self.store.run_record(scheduling=True), allocation)
                    continue
                if allocation["status"] == "active":
                    if not allocation["interval_recorded"]:
                        self._record_interval(state, allocation)
                    else:
                        allocation.update(
                            status="yielded", generation=self._generation(state)
                        )
            if self._frontier_mode(state) == "adaptive":
                from .frontier.hooks import settle_recovered_research

                settle_recovered_research(self, state)
            self._event(state, "owner_recovered")
        self.expire_holds()
