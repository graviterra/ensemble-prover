"""Bound research attention, retain work, and require independent next steps.

These are allocation decisions, never mathematical judgements. Dispatch receipts
remain the accounting authority, including retries and interrupted old owners.
"""

from __future__ import annotations

import hashlib
from contextlib import nullcontext
from typing import Any

from .model import json_text
from .strategy import StrategyYield


REORIENTATION_FIELDS = {
    "rationale", "next_question", "first_uncertain_inference",
    "discriminating_check", "avoid",
}
INSTRUCTIONS = """
Research and review have bounded allocations, including transport retries.
The research_allocation packet gives the remaining calls. Reading is information
collection, not mathematical progress. Before an allocation ends, submit your
actual argument or exact gap; record_note preserves useful intermediate work.
An assigned research_reorientation reviewer must independently inspect the
checkpoint and conclude with:
{"action":"research_reorientation","rationale":"what failed and why",
 "next_question":"specific next mathematical task",
 "first_uncertain_inference":"exact bottleneck",
 "discriminating_check":"calculation, derivation, or source check to execute",
 "avoid":"unsupported assumptions and exhausted routes to avoid"}.
This action allocates a new investigation; it cannot establish truth or falsity.
Use inspected source content, precise quantifiers and useful prior work. Do not
request another generic summary or repeat a prior assignment under a new name.
"""


def _allocation(job: dict[str, Any], state: dict[str, Any]) -> dict[str, Any]:
    record = job.setdefault("research_control", {})
    receipts = [item for item in state["attempts"].values()
                if item.get("consumer_id") == job["job_id"]
                and item.get("allocation_id") is None]
    # Reconstruct from authoritative admissions, not turns or successful actions.
    record["requests_used"] = len(receipts)
    times = [item["admitted_at"] for item in receipts if "admitted_at" in item]
    if times:
        record["started_at"] = min(times)
    return record


def _limit(job: dict[str, Any], state: dict[str, Any]) -> int:
    return min(4, state["policy"]["interval_requests"]) if job["role"] == "review" else state["policy"]["interval_requests"]


def _research_count(store: Any, state: dict[str, Any]) -> int:
    # Old receipts have no role field. Resolve their durable producer rather
    # than resetting attention when a pre-upgrade run is resumed.
    researchers = {job["job_id"] for job in store.jobs() if job["role"] == "research"}
    return sum(item.get("allocation_id") is None and item["consumer_id"] in researchers
               for item in state["attempts"].values())


def _reason(store: Any, job: dict[str, Any], state: dict[str, Any], run: dict[str, Any], now: float,
            reservations: int = 0) -> str | None:
    record = _allocation(job, state)
    if record.get("closed"):
        return "research_allocation_closed"
    if record["requests_used"] >= _limit(job, state):
        return "research_interval_exhausted"
    if record.get("started_at") is not None and now >= record["started_at"] + state["policy"]["interval_seconds"]:
        return "research_interval_expired"
    if job["role"] == "research":
        reviewed = state.get("research_attention", {}).get("reviewed_through", 0)
        if _research_count(store, state) - reviewed >= state["policy"]["interval_requests"]:
            return "research_phase_exhausted"
        reserve = min(state["policy"]["reserve_requests"], run["max_requests"] // 2)
        if run["requests_used"] + reservations >= run["max_requests"] - reserve:
            return "research_review_reserve"
        if record.get("requests_used") and now >= run["deadline"] - min(
            state["policy"]["reserve_seconds"], run["max_seconds"] / 2
        ):
            return "research_review_reserve"
    return None


def admit_research(store: Any, job: dict[str, Any], state: dict[str, Any],
                   run: dict[str, Any], now: float, reservations: int) -> None:
    """Called inside the existing single writer dispatch debit transaction."""
    reason = _reason(store, job, state, run, now, reservations)
    if reason:
        raise StrategyYield(reason)
    record = job["research_control"]
    record.setdefault("started_at", now)
    record["requests_used"] += 1
    store.save_job(job)


class ResearchControl:
    """Scheduler-owned checkpoints with independently assigned followups."""

    def __init__(self, loop: Any, controller: Any):
        self.loop, self.store, self.controller = loop, loop.store, controller

    def _atomic(self):
        return nullcontext() if self.store._applying else self.store.atomic()

    def context(self, job: dict[str, Any]) -> dict[str, Any]:
        state = self.controller.snapshot()
        record = _allocation(job, state)
        run = self.store.run_record(scheduling=True)
        own_remaining = max(0, _limit(job, state) - record["requests_used"])
        global_remaining = max(0, run["max_requests"] - run["requests_used"] - self.controller._reservations(state))
        phase_remaining = None
        if job["role"] == "research":
            reviewed = state.get("research_attention", {}).get("reviewed_through", 0)
            phase_remaining = max(0, state["policy"]["interval_requests"] - (_research_count(self.store, state) - reviewed))
            global_remaining = max(0, global_remaining - min(state["policy"]["reserve_requests"], run["max_requests"] // 2))
        remaining = min(own_remaining, global_remaining,
                        phase_remaining if phase_remaining is not None else own_remaining)
        result = {"research_allocation": {
            "requests_used": record["requests_used"],
            "requests_remaining": remaining,
            "job_requests_remaining": own_remaining,
            "phase_requests_remaining": phase_remaining,
            "global_requests_available": global_remaining,
            "must_conclude": remaining <= 1,
            "reading_is_not_mathematical_progress": True,
            "directive": job.get("research_directive"),
            "prior_checkpoint_artifact": job.get("research_prior_checkpoint"),
            "portfolio_checkpoint_artifacts": job.get("research_portfolio_checkpoints", []),
        }}
        if job.get("research_reorientation_for"):
            from .model import load_json

            result["assigned_research_checkpoint"] = load_json(
                self.store.read_artifact(job["research_checkpoint"]).decode()
            )
        return result

    def before_request(self, job: dict[str, Any]) -> bool:
        with self._atomic():
            current = self.store.job(job["job_id"])
            state = self.controller.snapshot()
            reason = _reason(self.store, current, state, self.store.run_record(scheduling=True),
                             self.controller.clock(), self.controller._reservations(state))
            if reason:
                if current["role"] == "research" and not current["research_control"].get("closed"):
                    child = next((item for item in self.store.jobs()
                                  if item["parent_job"] == current["job_id"]
                                  and item["role"] in {"review", "formalization"}
                                  and item["status"] in {"pending", "running", "responded", "tool_running"}), None)
                    if child is not None:
                        current["research_control"]["waiting_for"] = child["job_id"]
                        current["status"] = "waiting"
                        self.store.save_job(current)
                        return False
                self.handle_yield(current, reason)
                return False
            return True

    def synchronize(self) -> None:
        # Never close an in-flight/received turn: its response may contain the
        # useful argument earned by the final admitted request.
        for job in self.store.jobs():
            if job["role"] in {"research", "review"} and job["status"] == "pending":
                self.before_request(job)

    def after_action(self, job: dict[str, Any], action: dict[str, Any], result: Any,
                     novelty: dict[str, Any]) -> None:
        with self._atomic():
            if job.get("research_control", {}).get("closed"):
                return
            action_text, result_text = json_text(action), json_text(result)
            job["research_last_action"] = {
                "kind": action["action"],
                "action_artifact": self.store.put_artifact(action_text.encode(), name="research-checkpoint-action.json"),
                "result_artifact": self.store.put_artifact(result_text.encode(), name="research-checkpoint-result.json"),
                "action_preview": action_text[:2000],
                "action_preview_complete": len(action_text) <= 2000,
                "result_preview": result_text[:2000],
                "result_preview_complete": len(result_text) <= 2000,
            }
            self.store.save_job(job)
            if job["role"] == "review" and job["status"] == "finished":
                self._complete_phase()
                return
            if action["action"] == "submit" and action.get("kind") == "gap":
                self.handle_yield(job, "research_gap_submitted")
            elif novelty.get("consecutive_repeated_retrievals", 0) >= 3:
                self.handle_yield(job, "research_repeated_retrieval")
            elif job["status"] in {"pending", "running", "responded"}:
                self.before_request(job)

    def _checkpoint(self, job: dict[str, Any], reason: str) -> str:
        transcript = self.store.put_artifact(json_text(job).encode(), name="research-complete-checkpoint.json")
        packet = {
            "reason": reason, "producer": job["job_id"], "claim_id": job["claim_id"],
            "assignment": job["question"], "complete_job_artifact": transcript,
            "last_action": job.get("research_last_action"),
            "last_response_artifact": job.get("response"),
            "last_validation_result": ({"accepted": False, "error": job["last_error"]}
                                       if job.get("last_error") else None),
            "memory": job.get("research_memory", {}),
            "prior_directive": job.get("research_directive"),
            "prior_checkpoint": job.get("research_prior_checkpoint"),
            "late_candidate_artifacts": job.get("late_research_candidates", []),
            "interpretation": "Allocation ended; truth and falsity remain unchanged.",
        }
        return self.store.put_artifact(json_text(packet).encode(), name="research-review-checkpoint.json")

    def handle_yield(self, job: dict[str, Any], reason: str) -> None:
        with self._atomic():
            job = self.store.job(job["job_id"])
            record = _allocation(job, self.controller.snapshot())
            if record.get("closed"):
                job["status"] = "finished"
                self.store.save_job(job)
                return
            checkpoint = self._checkpoint(job, reason)
            record.update(closed=True, reason=reason, checkpoint=checkpoint)
            job.update(status="finished", last_error=None)
            self.store.save_job(job)
            if job["role"] == "review":
                self._incomplete_review(job, reason)
                self._fallback(job, checkpoint, reason)
            else:
                existing = next((item for item in self.store.jobs()
                                 if item.get("research_reorientation_for")
                                 and item["status"] in {"pending", "running", "responded", "tool_running"}
                                 and not item.get("research_control", {}).get("closed")), None)
                if existing is not None:
                    existing.setdefault("research_portfolio_checkpoints", []).append(checkpoint)
                    self.store.save_job(existing)
                    job["research_successor"] = existing["job_id"]
                    self.store.save_job(job)
                    return
                reviewer = self.store.add_job(
                    job["claim_id"],
                    "Independently inspect the assigned checkpoint. Identify the exact unsupported inference, preserve useful results and prescribe one concrete discriminating next task with research_reorientation. Read sources only as needed to decide this task; do not repeat the producer's retrieval loop.",
                    role="review", parent_job=job["job_id"],
                )
                reviewer.update(research_reorientation_for=job["job_id"], research_checkpoint=checkpoint,
                                research_portfolio_checkpoints=[checkpoint])
                self._carry_memory(job, reviewer)
                self.store.save_job(reviewer)
                job["research_successor"] = reviewer["job_id"]
                self.store.save_job(job)

    def _fallback(self, reviewer: dict[str, Any], checkpoint: str, reason: str) -> None:
        self._complete_phase()
        directive = {
            "decision": "review_inconclusive", "rationale": reason,
            "next_question": "Resolve the first uncertain inference in the prior investigation.",
            "first_uncertain_inference": "Extract the exact unsupported inference from the archived work; do not assume it is true.",
            "discriminating_check": self._fallback_check(),
            "avoid": "Do not repeat the prior retrieval sequence or treat an unfinished review as approval. Produce an actual derivation or exact gap.",
        }
        self._followup(reviewer, directive, checkpoint)

    def _complete_phase(self) -> None:
        """Independent review work permits new attention, never proof credit."""
        with self.controller._edit() as (state, _):
            state["research_attention"] = {"reviewed_through": _research_count(self.store, state)}

    def _incomplete_review(self, job: dict[str, Any], reason: str) -> None:
        review_id = job.get("strategy_review_id")
        if not review_id:
            return
        with self.controller._edit() as (state, _):
            review = state["reviews"][review_id]
            if review["status"] != "review_pending":
                return
            review.update(status="unresolved", allocation_incomplete=True,
                          rationale="No independent decision was completed: " + reason)
            hold = state["holds"].get(review_id)
            if hold is not None and hold["expires_at"] is not None:
                state["holds"].pop(review_id)
            self.controller._refresh_dispositions(state)
            self.controller._event(state, "research_review_allocation_incomplete", review_id=review_id)

    @staticmethod
    def _carry_memory(producer: dict[str, Any], recipient: dict[str, Any]) -> None:
        memory = producer.get("research_memory") or producer.get("research_prior_memory")
        if memory is not None:
            recipient["research_prior_memory"] = memory

    def _fallback_check(self) -> str:
        checks = (
            "Write out the exact quantifiers and hypotheses and test the first proposed implication on an explicit admissible example.",
            "Derive a weaker local estimate directly from definitions, with explicit constants, and identify exactly which sum would recover the root.",
            "Verify one cited obstruction against its original source, specifying the exact theorem and whether its hypotheses match the bottleneck.",
            "Construct a mathematically different route avoiding the unsupported bridge and execute its first substantive calculation.",
        )
        completed = sum(bool(job.get("research_control", {}).get("closed")) for job in self.store.jobs())
        return checks[(completed // 2) % len(checks)]

    def _followup(self, reviewer: dict[str, Any], directive: dict[str, Any], checkpoint: str) -> dict[str, Any]:
        signature = hashlib.sha256(json_text({key: " ".join(str(directive.get(key, "")).casefold().split())
                                            for key in ("next_question", "discriminating_check")}).encode()).hexdigest()
        if any(job.get("research_route_signature") == signature for job in self.store.jobs()):
            directive = {**directive, "repeated_assignment": True,
                         "discriminating_check": self._fallback_check(),
                         "avoid": directive["avoid"] + " The proposed assignment repeats archived work; perform this new check before returning to it."}
        question = "\n".join(f"{key}: {directive[key]}" for key in (
            "next_question", "first_uncertain_inference", "discriminating_check", "avoid"
        ))
        root_id = self.store.run_record(scheduling=True)["target_id"]
        if reviewer["claim_id"] != root_id:
            question = (
                "Pursue the original root, using or avoiding the separately scoped bottleneck "
                + reviewer["claim_id"] + ". The stronger helper is not an assumption of the root.\n" + question
            )
        child = self.store.add_job(root_id, question, parent_job=reviewer["job_id"])
        child.update(research_directive=directive, research_prior_checkpoint=checkpoint,
                     research_route_signature=signature,
                     research_portfolio_checkpoints=reviewer.get("research_portfolio_checkpoints", []))
        self._carry_memory(reviewer, child)
        self.store.save_job(child)
        reviewer["research_successor"] = child["job_id"]
        self.store.save_job(reviewer)
        return child

    def apply_reorientation(self, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any]:
        if job["role"] != "review" or not job.get("research_reorientation_for"):
            raise ValueError("only the assigned independent checkpoint reviewer may reorient")
        if job.get("research_control", {}).get("closed"):
            raise ValueError("the assigned allocation has already ended")
        directive = {key: action[key] for key in REORIENTATION_FIELDS}
        directive["decision"] = "investigate"
        job["status"] = "finished"
        job.setdefault("research_control", {})["closed"] = True
        self._complete_phase()
        child = self._followup(job, directive, job["research_checkpoint"])
        return {"program": child["job_id"], "directive": directive, "kernel_verified": False}
