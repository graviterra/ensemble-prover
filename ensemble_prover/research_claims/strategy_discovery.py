"""Discovery adapters for continuous, evidence-aware strategy recovery."""

from __future__ import annotations

from typing import Any
from contextlib import nullcontext

from .model import json_text, text
from .strategy import StrategyController, StrategyYield
from .research_control import INSTRUCTIONS, REORIENTATION_FIELDS, ResearchControl


ACTION_FIELDS = {
    "research_reorientation": REORIENTATION_FIELDS,
    "request_strategy_review": {
        "subject_handle",
        "scope",
        "argument",
        "evidence_artifact_ids",
        "remaining_uncertainty",
    },
    "strategy_review": {"verdict", "rationale"},
    "request_progress_review": {"allocation_id", "evidence_artifact_ids", "argument"},
    "progress_review": {"relevant", "rationale"},
    "request_implication_review": {
        "premise",
        "consequence",
        "argument",
        "evidence_artifact_ids",
    },
    "implication_review": {"applicable", "rationale"},
    "report_investigation": {
        "method",
        "derivation",
        "first_uncertain_inference",
        "evidence_artifact_ids",
        "remaining_gap",
    },
    "alternative_review": {"substantive", "rationale"},
    "lookup_strategy_subject": {"query"},
    "record_bottleneck": {
        "statement",
        "parent_subject_handle",
        "first_uncertain_inference",
        "quantitative_requirements",
    },
}

def _validate_action_values(action: dict[str, Any]) -> None:
    """Reject malformed model values before using handles or recording evidence."""
    kind = action["action"]
    if kind not in ACTION_FIELDS:
        raise ValueError("unknown strategy action")
    arrays = {"evidence_artifact_ids", "supersedes"}
    booleans = {"relevant", "applicable", "substantive"}
    for field in ACTION_FIELDS[kind] - arrays - booleans:
        text(action[field], field)
    if "method" in action:
        text(action["method"], "method", optional=True)
    for field in arrays & action.keys():
        value = action[field]
        if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
            raise ValueError(f"{field} must be an array of identifiers")
    for field in booleans & action.keys():
        if type(action[field]) is not bool:
            raise ValueError(f"{field} must be boolean")


SYSTEM = INSTRUCTIONS + """
This run has an autonomous research controller. Finishing one investigation
does not stop the run. Pursue the original root within the authorized total
budget; when a route stalls or is contradicted, execute a materially different
investigation. Preserve useful checked facts, exact gaps, and failed approaches.
Do not repeatedly formalize an unsupported stronger claim, rename its helpers,
or confuse an unperformed counterexample search with evidence of truth.

Additional actions:
{"action":"record_bottleneck","statement":"exact claim",
 "parent_subject_handle":"issued handle","first_uncertain_inference":"...",
 "quantitative_requirements":"constants, quantifiers, losses and uniformity"}
{"action":"lookup_strategy_subject","query":"claim or supplier to inspect"}
{"action":"request_strategy_review","subject_handle":"issued handle",
 "scope":"claim_contradiction|method_barrier|unsupported_bridge|allocation_exhausted",
 "argument":"complete applicability argument","evidence_artifact_ids":[],
 "remaining_uncertainty":"what remains unverified","supersedes":[]}
  Creates an independent allocation review. It neither refutes the theorem nor
  automatically launches a formal proof of negation. Challenge false ancestors
  even while their current helper is true. Read complete source artifacts.
  To appeal a standing hold, explicitly list its issued review IDs in supersedes.

A strategy-review worker may inspect sources and claims but must conclude with
{"action":"strategy_review","verdict":"hold|dismiss|unresolved",
 "rationale":"independent hypothesis/quantifier checks and exact scope"}.
Review only its assigned objection and explicitly assigned supersessions.
Hold only the implicated claim, method, or bridge. Budget exhaustion alone
does not show falsity: return unresolved and propose a discriminating next step.
An inconclusive appeal does not overturn existing evidence. A source vote is
never a Lean certificate. Explain what a replacement route must avoid and what
would justify returning to the old route. Investigators cannot review themselves.

To justify returning to a difficult but viable route, request independent review:
{"action":"request_progress_review","allocation_id":"issued allocation",
 "evidence_artifact_ids":["admitted attempt artifact"],"argument":"how this advances the exact bottleneck"}
An assigned progress reviewer concludes with
{"action":"progress_review","relevant":true,"rationale":"checked first uncertain inference, constants and quantifiers"}.
Use relevant=false when uncertain. Helper counts, new notation, unsupported
experiments and repeated failed attempts do not establish relevant progress.

Working context is bounded; complete history remains in immutable artifacts.
{"action":"read_artifact","artifact_id":"SHA256","path":["JSON key",0],"offset":0,"length":6000}
Read exact JSON paths or successive character pages (maximum 12000). A partial
page or an archived field is uninspected, never evidence that something is absent.

Transfer objections across changed statements/contexts only by explicit review:
{"action":"request_implication_review","premise":"issued B","consequence":"issued A",
 "argument":"complete derivation B implies A, with every hypothesis","evidence_artifact_ids":[]}
The assigned reviewer uses {"action":"implication_review","applicable":true,"rationale":"..."}.
Check both exact contexts. Return applicable=false if uncertain. A held A can
restrict B only in the B-implies-A direction. This is allocation advice, never
a Lean implication certificate. Prove equivalence with two explicit directions.

Complete an alternative by reporting actual work, including unsuccessful work:
{"action":"report_investigation","method":"distinct method","derivation":"complete argument or executed checks",
 "first_uncertain_inference":"exact next step","evidence_artifact_ids":[],"remaining_gap":"what is open"}
An independent reviewer uses {"action":"alternative_review","substantive":true,"rationale":"..."}
only when the report actually investigates a different approach with a concrete
derivation/check and precise gap. A promised plan or renamed method earns no
renewal. This assessment grants exploration credit, not mathematical proof.
"""


class StrategyIntegration:
    """The loop remains the execution owner; this adapter never stops the run."""

    def __init__(self, loop: Any):
        self.loop = loop
        self.store = loop.store
        self.controller = StrategyController(self.store)
        self.research = ResearchControl(loop, self.controller)

    def context(self, job: dict[str, Any]) -> dict[str, Any]:
        from .literature import source_context

        state = self.controller.snapshot()
        context = {
            "strategy_control": {
                "root_subject": state["root_id"],
                "original_lean_target": state["original_lean"],
                "subjects": list(state["subjects"].values()),
                "holds": list(state["holds"].values()),
                "reviews": list(state["reviews"].values()),
                "policy": state["policy"],
                "alternative_for": job.get("alternative_for"),
                "proof_attempt_artifacts": {
                    item["job_id"]: item["proof_feedback"]
                    for item in self.store.jobs()
                    if item.get("proof_feedback")
                },
                "methods": [
                    {
                        "subject_id": item["subject_id"],
                        "method": item["method"],
                        "status": item["status"],
                    }
                    for item in state["allocations"].values()
                ],
                "progress_inventory": [
                    {
                        "allocation_id": item["allocation_id"],
                        "subject_id": item["subject_id"],
                        "artifacts": [
                            aid
                            for attempt in state["attempts"].values()
                            if attempt["allocation_id"] == item["allocation_id"]
                            for aid in attempt["artifacts"]
                        ],
                    }
                    for item in list(state["allocations"].values())[-8:]
                    if not item.get("progress_credited")
                ],
            }
        }
        if job.get("strategy_review_id"):
            review = state["reviews"][job["strategy_review_id"]]
            context["assigned_strategy_objection"] = {
                "record": review,
                "subject": state["subjects"][review["subject_id"]],
                "complete_artifacts": {
                    aid: source_context(self.store, aid)
                    for aid in review["artifact_ids"]
                },
                "superseded_reviews": [
                    state["reviews"][rid] for rid in review["supersedes"]
                ],
            }
            if review.get("kind") == "implication":
                context["assigned_strategy_objection"]["consequence"] = state[
                    "subjects"
                ][review["consequence"]]
        return context

    def synchronize(self) -> None:
        """Durable inbox intake and queued review work share the owner transaction."""
        self.controller.expire_holds()
        self.research.synchronize()
        with self.store.atomic():
            state = self.controller.snapshot()
            root_claim = self.store.run_record(scheduling=True)["target_id"]
            for review in state["reviews"].values():
                if review["status"] != "review_pending" or review["job_id"] is not None:
                    continue
                parent = next(
                    (
                        job["job_id"]
                        for job in self.store.jobs()
                        if review["author"] in {job["job_id"], job["worker"]}
                    ),
                    None,
                )
                job = self.store.add_job(
                    root_claim,
                    "Independently assess the assigned strategy objection; check exact hypotheses, constants and quantifiers. Decide resource allocation without asserting a formal disproof.",
                    role="review",
                    parent_job=parent,
                )
                job["strategy_review_id"] = review["review_id"]
                self.store.save_job(job)
                self.controller.bind_review_job(review["review_id"], job["job_id"])
            for job in self.store.jobs():
                if job.get("strategy_capacity_wait"):
                    if self.store.get_claim(job["claim_id"])["revision"] != job["revision"]:
                        job["strategy_capacity_wait"] = False
                        self.loop._mark_stale(job)
                        continue
                    if job["status"] != "waiting":
                        job["strategy_capacity_wait"] = False
                        self.store.save_job(job)
                        continue
                    run = self.store.run_record(scheduling=True)
                    if (
                        run["requests_used"]
                        + self.controller._reservations(self.controller.snapshot())
                        < run["max_requests"]
                    ):
                        job.update(status="pending", strategy_capacity_wait=False)
                        self.store.save_job(job)

    def ensure_alternative(
        self, subject_id: str, *, reason: str, parent_job: str | None = None
    ) -> dict[str, Any]:
        """Queue one real investigation per requirement, not an unbounded fanout."""
        subject = self.controller.subject(subject_id)
        requirement = subject["interval_sequence"]
        for job in self.store.jobs():
            if (
                job.get("alternative_for") == subject_id
                and job.get("alternative_requirement") == requirement
                and job["status"]
                in {"pending", "running", "responded", "tool_running", "waiting"}
            ):
                return job
        question = (
            "Execute a new investigation toward the original root. The previous strategy requires review: "
            + reason
            + "\nExact bottleneck: "
            + subject["statement"]
            + "\nRead its complete objections and quantitative requirements. Investigate a changed method or a route avoiding this claim. "
            "Name the first uncertain inference and perform a discriminating check, literature investigation, or substantive mathematical derivation. "
            "Do not merely rename the old plan. Report the complete result, useful facts, and remaining gap. "
            "A method barrier may permit a different method for the same true claim; a claim contradiction requires avoiding or resolving that claim."
        )
        job = self.store.add_job(
            self.store.run_record(scheduling=True)["target_id"], question, parent_job=parent_job
        )
        job.update(alternative_for=subject_id, alternative_requirement=requirement)
        self.store.save_job(job)
        return job

    def ensure_work(self) -> bool:
        """An exhausted research program cannot turn the whole run idle/blocked."""
        if self.store.stop_reason() or self.store.run_record(scheduling=True)["status"] != "running":
            return False
        jobs = self.store.jobs()
        if any(
            job["status"] in {"pending", "responded", "running", "tool_running"}
            for job in jobs
        ):
            return False
        with self.store.atomic():
            # Waiting investigations with no runnable dependencies have no
            # reason to block a fresh research program.
            for job in jobs:
                if job.get("alternative_for") and job["status"] == "waiting":
                    job["status"] = "finished"
                    self.store.save_job(job)
            held = list(self.controller.snapshot()["holds"].values())
            subject_id = held[-1]["subject_id"] if held else self.controller.root_id
            self.ensure_alternative(
                subject_id,
                reason="No runnable proof route; continue mathematical research",
            )
        return True

    def apply_action(
        self, job: dict[str, Any], action: dict[str, Any]
    ) -> dict[str, Any]:
        _validate_action_values(action)
        kind = action["action"]
        if kind == "research_reorientation":
            return self.research.apply_reorientation(job, action)
        if kind == "report_investigation":
            if job["role"] != "research" or not job.get("alternative_for"):
                raise ValueError(
                    "report this work from an assigned alternative investigation"
                )
            report = {
                key: text(action[key], key)
                for key in (
                    "method",
                    "derivation",
                    "first_uncertain_inference",
                    "remaining_gap",
                )
            }
            for aid in action["evidence_artifact_ids"]:
                self.store.read_artifact(aid)
            report["evidence_artifact_ids"] = action["evidence_artifact_ids"]
            aid = self.store.put_artifact(
                json_text(report).encode(),
                name="complete-alternative-investigation.json",
            )
            with self.store.atomic() if not self.store._applying else nullcontext():
                review = self.controller.request_review(
                    job["alternative_for"],
                    scope="allocation_exhausted",
                    argument=(
                        "Independently assess whether this report contains a substantive investigation of a different route. "
                        f"Producer {job['job_id']}; requirement {job['alternative_requirement']}."
                    ),
                    artifact_ids=[aid],
                    author=job["job_id"],
                )
                with self.controller._edit() as (state, _):
                    review = state["reviews"][review["review_id"]]
                    if review["status"] == "review_pending":
                        review.update(
                            kind="alternative",
                            producer_job=job["job_id"],
                            requirement=job["alternative_requirement"],
                        )
                job.update(
                    status="finished",
                    investigation_artifact=aid,
                    alternative_assessment=review["review_id"],
                )
                self.store.save_job(job)
            return {"review": review, "kernel_verified": False}
        if kind == "alternative_review":
            if job["role"] != "review" or not job.get("strategy_review_id"):
                raise ValueError(
                    "only the assigned independent worker may review exploration"
                )
            if type(action["substantive"]) is not bool:
                raise ValueError("substantive must be boolean")
            with self.controller._edit() as (state, _):
                review = state["reviews"][job["strategy_review_id"]]
                if review.get("kind") != "alternative":
                    raise ValueError("not an assigned alternative assessment")
                if review["status"] == "review_pending":
                    review.update(
                        status="substantive" if action["substantive"] else "unresolved",
                        rationale=text(action["rationale"], "assessment rationale"),
                    )
            if review["status"] == "substantive":
                try:
                    self.controller.record_alternative(
                        review["subject_id"],
                        review["producer_job"],
                        review["artifact_ids"][0],
                    )
                except ValueError as exc:
                    review = {**review, "renewal_note": str(exc)}
            job["status"] = "finished"
            self.loop._notify(
                job["parent_job"],
                {"alternative_review": review, "kernel_verified": False},
                requires_response=True,
            )
            return {"alternative_review": review, "kernel_verified": False}
        if kind == "request_implication_review":
            if job["role"] == "review":
                raise ValueError(
                    "investigators request independent applicability review"
                )
            return {
                "review": self.controller.request_implication(
                    action["premise"],
                    action["consequence"],
                    argument=action["argument"],
                    artifact_ids=action["evidence_artifact_ids"],
                    author=job["job_id"],
                ),
                "kernel_verified": False,
            }
        if kind == "implication_review":
            if job["role"] != "review" or not job.get("strategy_review_id"):
                raise ValueError("only the assigned reviewer may assess implication")
            result = self.controller.decide_implication(
                job["strategy_review_id"],
                applicable=action["applicable"],
                rationale=action["rationale"],
            )
            job["status"] = "finished"
            self.loop._notify(
                job["parent_job"],
                {"applicability_review": result, "kernel_verified": False},
                requires_response=True,
            )
            return {"applicability_review": result, "kernel_verified": False}
        if kind == "request_progress_review":
            if job["role"] == "review":
                raise ValueError(
                    "reviewers cannot request their own progress assessment"
                )
            return {
                "review": self.controller.request_progress(
                    action["allocation_id"],
                    artifact_ids=action["evidence_artifact_ids"],
                    argument=action["argument"],
                    author=job["job_id"],
                ),
                "kernel_verified": False,
            }
        if kind == "progress_review":
            review_id = job.get("strategy_review_id")
            if job["role"] != "review" or not review_id:
                raise ValueError(
                    "only the assigned independent reviewer may assess progress"
                )
            result = self.controller.decide_progress(
                review_id, relevant=action["relevant"], rationale=action["rationale"]
            )
            job["status"] = "finished"
            self.loop._notify(
                job["parent_job"],
                {"progress_review": result, "kernel_verified": False},
                requires_response=True,
            )
            return {"progress_review": result, "kernel_verified": False}
        if kind == "strategy_review":
            review_id = job.get("strategy_review_id")
            if job["role"] != "review" or not review_id:
                raise ValueError(
                    "only the assigned independent strategy reviewer may decide"
                )
            if self.controller.snapshot()["reviews"][review_id].get("kind") in {
                "progress",
                "implication",
                "alternative",
            }:
                raise ValueError(
                    "use the decision action for this assigned review kind"
                )
            review = self.controller.decide(
                review_id, action["verdict"], rationale=action["rationale"]
            )
            job["status"] = "finished"
            if review["status"] == "stale":
                # Reassign against current evidence explicitly. The stale
                # response cannot silently acquire a newer review basis.
                self.controller.request_review(
                    review["subject_id"],
                    scope=review["scope"],
                    method=review["method"],
                    argument=review["argument"],
                    artifact_ids=review["artifact_ids"],
                    author=review["author"],
                    supersedes=review["supersedes"],
                )
            elif review["status"] in {"reviewed_hold", "unresolved"}:
                self.ensure_alternative(
                    review["subject_id"],
                    reason=review["rationale"],
                    parent_job=job["parent_job"],
                )
            self.loop._notify(
                job["parent_job"],
                {"strategy_review": review, "kernel_verified": False},
                requires_response=True,
            )
            return {"strategy_review": review, "kernel_verified": False}
        if kind == "lookup_strategy_subject":
            query = text(action["query"], "subject query").casefold()
            return {
                "subjects": [
                    subject
                    for subject in self.controller.snapshot()["subjects"].values()
                    if query in subject["statement"].casefold()
                    or query == subject["subject_id"]
                ][:32]
            }
        if kind == "record_bottleneck":
            parent = action["parent_subject_handle"]
            self.controller.subject(parent)
            subject = self.controller.register_subject(
                action["statement"], parent_id=parent
            )
            note = self.store.put_artifact(
                json_text(
                    {
                        "first_uncertain_inference": text(
                            action["first_uncertain_inference"],
                            "first uncertain inference",
                        ),
                        "quantitative_requirements": text(
                            action["quantitative_requirements"],
                            "quantitative requirements",
                        ),
                    }
                ).encode(),
                name="bottleneck-requirements.json",
            )
            with self.controller._edit() as (state, _):
                artifacts = state["subjects"][subject["subject_id"]].setdefault(
                    "requirements_artifacts", []
                )
                if note not in artifacts:
                    artifacts.append(note)
            return {
                "subject": subject,
                "requirements_artifact": note,
                "kernel_verified": False,
            }
        if kind == "request_strategy_review":
            subject_id = text(action["subject_handle"], "subject handle")
            self.controller.subject(subject_id)
            method = action.get("method", "")
            if method and method not in {
                item["method"]
                for item in self.controller.snapshot()["allocations"].values()
                if subject_id in item["subjects"]
            }:
                raise ValueError("choose an issued method handle for this subject")
            if (
                action["scope"] in {"method_barrier", "unsupported_bridge"}
                and not method
            ):
                methods = {
                    item["method"]
                    for item in self.controller.snapshot()["allocations"].values()
                    if subject_id in item["subjects"] and item["status"] == "active"
                }
                if len(methods) != 1:
                    raise ValueError(
                        "choose the exact method handle from strategy_control.methods"
                    )
                method = methods.pop()
            review = self.controller.request_review(
                subject_id,
                scope=action["scope"],
                argument=text(action["argument"], "applicability argument")
                + "\nRemaining uncertainty: "
                + text(action["remaining_uncertainty"], "remaining uncertainty"),
                artifact_ids=action["evidence_artifact_ids"],
                author=job["job_id"],
                method=method,
                supersedes=action.get("supersedes"),
            )
            return {"review": review, "kernel_verified": False}
        raise ValueError("unknown strategy action")

    def record_finished_alternative(self, job: dict[str, Any]) -> None:
        if job.get("alternative_for"):
            self.store.save_job(job)
            try:
                self.controller.record_alternative(
                    job["alternative_for"],
                    job["job_id"],
                    job.get("investigation_artifact", job["response"]),
                )
            except ValueError as exc:
                # Preserve research results even when their old requirement is
                # stale; they cannot grant current allocation renewal.
                job["alternative_accounting_note"] = str(exc)

    def yield_job(
        self, job: dict[str, Any], outcome: dict[str, Any], *, feedback: Any = None
    ) -> None:
        with self.store.atomic():
            current = self.store.job(job["job_id"])
            if current["status"] == "verified":
                from .proof_bridge import validate_receipt

                validate_receipt(self.store, current, current.get("proof_receipt"))
                return
            if current["turn"] != job["turn"] or current["status"] in {"stale", "superseded"}:
                return
            job = current
            if feedback is not None:
                job["proof_feedback"] = self.loop._blob(
                    feedback, "yielded-proof-feedback.json"
                )
                self.retain_feedback(job, feedback)
            lease = job.get("strategy_lease")
            if lease:
                self.controller.finish_interval(lease)
            job.update(status="waiting", strategy_outcome=outcome, last_error=None)
            self.store.save_job(job)
            subject_id = (
                outcome.get("subject_id")
                or (lease or {}).get("subject_id")
                or self.controller.root_id
            )
            self.ensure_alternative(
                subject_id, reason=outcome["reason"], parent_job=job["parent_job"]
            )
            self.loop._notify(
                job["parent_job"],
                {
                    "strategy_result": outcome,
                    "proof_feedback": feedback,
                    "artifact_id": job.get("proof_feedback"),
                    "kernel_verified": False,
                },
                requires_response=True,
            )

    def retain_feedback(self, job: dict[str, Any], feedback: Any) -> None:
        lease = job.get("strategy_lease")
        if lease is None:
            return
        attempts = [
            a
            for a in self.controller.snapshot()["attempts"].values()
            if a["allocation_id"] == lease["allocation_id"]
            and a["consumer_id"] == job["job_id"]
        ]
        if attempts:
            try:
                self.controller.receive_artifact(
                    attempts[-1]["attempt_id"], json_text(feedback).encode()
                )
                self.controller.settle(attempts[-1]["attempt_id"], outcome="completed")
            except ValueError as exc:
                job["feedback_provenance_note"] = str(exc)

    def prepare_proof(self, job: dict[str, Any]) -> dict[str, Any]:
        subject_id = job.get("strategy_subject_id")
        if subject_id is None:
            run = self.store.run_record(scheduling=True)
            subject_id = (
                self.controller.root_id
                if job["claim_id"] == run["target_id"]
                else self.controller.register_subject(
                    self.store.get_claim(job["claim_id"])["spec"]["contract"][
                        "statement"
                    ],
                    parent_id=self.controller.root_id,
                )["subject_id"]
            )
        method = job.get("strategy_method") or job["handoff_artifact"]
        try:
            existing = next(
                (
                    a
                    for a in self.controller.snapshot()["allocations"].values()
                    if a["subject_id"] == subject_id
                    and a["method"] == method
                    and a["status"] == "active"
                    and not a.get("settlement_only")
                    and job["job_id"] not in a["consumers"]
                ),
                None,
            )
            if existing:
                for consumer_id in existing["consumers"]:
                    try:
                        self.controller._check_consumer(existing, consumer_id)
                        existing = {**existing, "consumer_id": consumer_id}
                        break
                    except StrategyYield:
                        continue
            lease = (
                self.controller.join_consumer(existing, job["job_id"])
                if existing
                else self.controller.allocate(subject_id, job["job_id"], method=method)
            )
        except StrategyYield:
            # Existing source can still earn mathematical acceptance. This
            # capability permits bounded local rechecking, zero model calls.
            lease = self.controller.allocate(
                subject_id,
                job["job_id"],
                method=method,
                settlement_only=True,
                settlement_seconds=self.store.run_record()["closed_loop"][
                    "lean_timeout_s"
                ],
            )
        job.update(
            strategy_subject_id=subject_id, strategy_method=method, strategy_lease=lease
        )
        self.store.save_job(job)
        return lease
