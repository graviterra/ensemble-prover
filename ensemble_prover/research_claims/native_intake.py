"""Independent, bounded research admission from current proof-side evidence.

Local checked declarations are advisory evidence of applicability. Only an
assigned review can prescribe another investigation; no progress credit is
created by this admission path.
"""
from __future__ import annotations

import json
import hashlib
from typing import Any

from .model import json_text
from .frontier.records import digest


def helper_evidence(dossier: Any) -> dict[str, dict[str, Any]]:
    """Snapshot current renderable declarations with intact structural receipts."""
    from ..proof_dossier import (
        helper_decl_statement, text_hash, verified_helper_bound_contract_identity,
        verified_helper_has_typed_binder_evidence,
        is_answer_unsafe_helper_source, is_answer_unsafe_statement_text,
    )
    from ..mini_session.progress_identity import helper_progress_keys

    if dossier is None or not getattr(dossier, "verified_helpers", None):
        return {}
    from ..proof_dossier import retirement_snapshot
    revision = dossier.helper_revision()
    cache_key = (revision, retirement_snapshot()) if revision is not None else None
    cached = getattr(dossier, "_native_intake_evidence_snapshot", None)
    if cache_key is not None and cached is not None and cached[0] == cache_key:
        return cached[1]
    visible = {name: helper for name, helper in dossier.verified_helpers.items()
               if dossier._verified_helper_context_visible(helper)}
    dependencies = {name: dossier._verified_helper_generated_dependencies(helper) for name, helper in visible.items()}
    renderable = dossier._verified_helper_renderable_names(visible, dependency_names_by_helper=dependencies)
    safety = dossier._answer_safety_kwargs()
    keys = helper_progress_keys(dossier)
    result = {}
    for name, helper in visible.items():
        identity = verified_helper_bound_contract_identity(helper)
        if (helper.source_hash != text_hash(helper.source)
                or not identity or not verified_helper_has_typed_binder_evidence(helper)
                or is_answer_unsafe_helper_source(helper.source, **safety)
                or is_answer_unsafe_statement_text(helper_decl_statement(helper.source), **safety)):
            continue
        result[name] = {
            "name": name, "source": helper.source,
            "source_sha256": hashlib.sha256(helper.source.encode()).hexdigest(), "source_hash": helper.source_hash, "contract_identity": identity,
            "environment": helper.verification_environment_hash,
            "statement": helper_decl_statement(helper.source),
            "open_premises": list(helper.open_premise_statements),
            "proof_binder_types": list(helper.contract_proof_binder_types),
            "currently_renderable": name in renderable,
            "dependency_context": [{"name": dependency,
                "source_hash": getattr(dossier.verified_helpers.get(dependency), "source_hash", None),
                "source_sha256": hashlib.sha256(dossier.verified_helpers[dependency].source.encode()).hexdigest()
                    if dependency in dossier.verified_helpers else None,
                "visible": dependency in visible, "renderable": dependency in renderable}
                for dependency in dependencies[name]],
            "support_receipts": dict(helper.support_source_hashes),
            "replay_context_receipts": dict(helper.replay_context_source_hashes),
            "progress_key": keys[name], "authority": "checked_in_recorded_environment_relevance_unreviewed",
        }
    if cache_key is not None:
        dossier._native_intake_evidence_snapshot = (cache_key, result)
    return result


def scope(campaign: dict[str, Any], approach: dict[str, Any]) -> dict[str, Any]:
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    return {"root_binding": campaign["root"]["binding"], "approach_id": approach["approach_id"],
            "question_id": question["question_id"], "question_revision": question["revision"],
            "route_id": route["route_id"], "route_revision": route["revision"]}


def subject(store: Any, job: dict[str, Any]) -> dict[str, Any]:
    reference = job.get("assigned_research_subject")
    if reference:
        return json.loads(store.read_artifact(reference))
    packet = json.loads(store.read_artifact(job["native_intake_artifact"]))
    value = {"version": 1, "origin": "native_evidence_intake", "reviewer_job_id": job["job_id"],
             "checkpoint_artifact": job["native_intake_artifact"],
             "report_artifact": job["native_intake_artifact"], "binding": packet["binding"],
             "question": packet["question"], "question_id": packet["binding"]["question_id"],
             "question_revision": packet["binding"]["question_revision"],
             "inspection": "unknown", "authority": "advisory_assignment_only"}
    value["subject_id"] = digest(value)
    job["assigned_research_subject"] = store.put_artifact(json_text(value).encode(), name="native-intake-subject.json")
    store.save_job(job)
    return value


def enqueue(loop: Any, packet: dict[str, Any], claim_id: str) -> dict[str, Any]:
    """Called inside the ordinary donated-quantum funding transaction."""
    from .frontier.owner import FrontierOwner
    from .frontier.approaches import issue_review_authorization

    store = loop.store
    if packet.get("native_target_claim_id") != claim_id:
        raise ValueError("native intake target changed before funding")
    intake_id = digest(packet)
    existing = next((j for j in store.jobs() if j.get("native_intake_id") == intake_id), None)
    if existing:
        return existing
    artifact = store.put_artifact(json_text(packet).encode(), name="native-evidence-intake.json")
    job = store.add_job(claim_id,
        "Independently inspect this exact native evidence intake. Checked local declarations retain their stated premises; their relevance to the root is unreviewed. Proposed investigations are speculative. Read the assigned artifact as needed. Conclude with research_reorientation and investigation_warranted:true only if one concrete changed investigation is justified; otherwise use false. Supply a specific next_question, first_uncertain_inference and discriminating_check. Never claim progress credit from this intake.", role="review")
    job.update(native_intake_id=intake_id, native_intake_artifact=artifact,
               native_intake_reviewer_worker=job["worker"],
               native_intake_lane=packet["lane"], native_context_binding=packet["native_context_binding"],
               native_target_claim_id=claim_id, frontier_approach_id=packet["binding"]["approach_id"],
               frontier_question_id=packet["binding"]["question_id"])
    owner = FrontierOwner(loop.strategy.controller)
    def authorize(campaign: dict[str, Any]) -> None:
        authorization = issue_review_authorization(campaign, question_id=packet["binding"]["question_id"],
            evidence_basis=artifact, producer_ids=packet["authors"],
            ceiling={"requests": min(4, loop.strategy.controller.snapshot()["policy"]["interval_requests"])},
            now=loop.strategy.controller.clock())
        job["frontier_review_authorization"] = authorization["authorization_id"]
    owner._edit(authorize)
    store.save_job(job)
    subject(store, job)
    return job


def apply_decision(control: Any, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any]:
    """Consume one paid exact review and optionally admit one scoped successor."""
    from .frontier.owner import FrontierOwner
    from .frontier.approaches import approach_is_held, request_readmission
    from .frontier.investigation import bind_question
    from .frontier.progress import active_permit, issue_permit, mark_permits_stale

    store = control.store
    controller = control.controller
    if job["role"] != "review" or job.get("research_control", {}).get("closed"):
        raise ValueError("native intake requires its open independent reviewer")
    assigned = subject(store, job)
    if action.get("subject_id") != assigned["subject_id"]:
        raise ValueError("native intake requires its exact assigned subject_id")
    if action.get("inspection_status", "claimed_complete") == "incomplete":
        return {"status": "inspection_incomplete", "subject_id": assigned["subject_id"], "kernel_verified": False}
    if action.get("inspection_status", "claimed_complete") != "claimed_complete":
        raise ValueError("invalid inspection_status")
    if type(action.get("investigation_warranted")) is not bool:
        raise ValueError("native intake requires explicit investigation_warranted boolean")
    if action.get("substantive_progress", False):
        raise ValueError("native intake cannot establish substantive progress credit")
    decision = action.get("approach_decision", "continue")
    if decision not in {"continue", "alternative"}:
        raise ValueError("approach_decision must be continue or alternative")
    if decision == "alternative":
        from .frontier.approaches import normalize_mechanism
        if not isinstance(action.get("approach_difference"), str) or not action["approach_difference"].strip():
            raise ValueError("alternative intake requires approach_difference")
        normalize_mechanism(action.get("approach_mechanism"))
    packet = json.loads(store.read_artifact(job["native_intake_artifact"]))
    if digest(packet) != job["native_intake_id"]:
        raise ValueError("native intake artifact identity mismatch")
    state = controller.snapshot()
    attempt = state["attempts"].get(job.get("frontier_response_attempt_id", ""), {})
    binding = attempt.get("frontier_binding") or {}
    if (attempt.get("consumer_id") != job["job_id"] or job.get("response") not in attempt.get("artifacts", [])
            or any(binding.get(key) != packet["binding"][key] for key in ("approach_id", "root_binding"))
            or binding.get("control_authorization") != job.get("frontier_review_authorization")
            or binding.get("native_context_binding") != packet["native_context_binding"]
            or binding.get("native_target_claim_id") != job["native_target_claim_id"]
            or binding.get("subject_revision") != job["revision"]
            or job["worker"] in packet["authors"]
            or job["worker"] != job.get("native_intake_reviewer_worker")):
        raise ValueError("native intake requires an independent paid response")
    manifest = json.loads(store.read_artifact(job["request_delivery_manifest"]))
    if (manifest.get("subject_id") != assigned["subject_id"]
            or manifest.get("dispatch_attempt_id") != attempt["attempt_id"]
            or manifest.get("response_artifact") != job["response"]
            or manifest.get("dispatch_status") != "response_received"):
        raise ValueError("native intake subject was not delivered for this response")
    validator = getattr(control, "native_intake_validator", None)
    current_evidence = validator(packet) if callable(validator) else None
    if current_evidence is None:
        raise ValueError("native intake requesting scope is unavailable")
    owner = FrontierOwner(controller)
    result: dict[str, Any] = {"status": "declined", "kernel_verified": False, "credit_minted": False}
    def decide(campaign: dict[str, Any]) -> None:
        approach = campaign["approaches"].get(packet["binding"]["approach_id"])
        run = store.run_record(scheduling=True)
        authorization = campaign["review_authorizations"].get(job.get("frontier_review_authorization", ""), {})
        if (current_evidence is not True or approach is None or scope(campaign, approach) != packet["binding"]
                or authorization.get("status") != "open" or authorization.get("evidence_basis") != job["native_intake_artifact"]
                or authorization.get("producer_ids") != packet["authors"]
                or run.get("native_active_target_claim_id") != job["native_target_claim_id"]
                or run.get("native_active_target_context_binding") != packet["native_context_binding"]
                or approach_is_held(campaign, approach["approach_id"])
                or approach["status"] in {"completed", "superseded", "dormant", "held"}
                or controller._blocked(state, [approach.get("subject_id") or state["root_id"]], approach.get("method", ""))
                or campaign["retries"].get(approach.get("operation_lineage") or "", {}).get("paused")):
            result["status"] = "stale"
            return
        decisions = campaign.setdefault("native_intake_decisions", {})
        if job["native_intake_id"] in decisions:
            raise ValueError("native intake already settled")
        decisions[job["native_intake_id"]] = {"reviewer_id": job["job_id"], "artifact": job["native_intake_artifact"],
            "attempt_id": attempt["attempt_id"], "warranted": action["investigation_warranted"], "credit_minted": False}
        authorization["status"] = "closed"
        if not action["investigation_warranted"]:
            return
        # Existing earned work keeps its permit and assignment. A competing
        # intake cannot overwrite a funded or higher-value continuation.
        if active_permit(campaign, approach["approach_id"]):
            result["status"] = "existing_work_retained"
            return
        if decision == "alternative":
            from copy import deepcopy
            from .frontier.approaches import fork_approach
            from .frontier.hooks import scoped_research_mechanism
            mechanism = scoped_research_mechanism(controller, job, action["approach_mechanism"])
            if any(existing["mechanism"] == mechanism and existing["status"] != "superseded"
                   for existing in campaign["approaches"].values()):
                raise ValueError("alternative intake must change the mathematical mechanism")
            parent = approach
            approach = fork_approach(campaign, parent["approach_id"], mechanism=mechanism,
                first_uncertain_inference=action["first_uncertain_inference"],
                first_investigation=action["discriminating_check"], quantitative_target=mechanism["quantitative_target"],
                key_obligations=[parent["bottleneck_obligation"]], now=controller.clock(),
                parent_grant_remaining=1, difference=action["approach_difference"])
            for field in ("native_context_binding", "native_target_claim_ids", "native_scope_bindings"):
                if field in parent:
                    approach[field] = deepcopy(parent[field])
            question = campaign["questions"][approach["question_id"]]
            permit = active_permit(campaign, approach["approach_id"])
            if permit is None:
                raise ValueError("alternative intake did not receive bounded exploration")
        else:
            previous = campaign["questions"][approach["question_id"]]
            question = bind_question(campaign, approach_id=approach["approach_id"],
                uncertainty=action["first_uncertain_inference"], why=action["rationale"],
                scope={**previous["scope"], "next_question": action["next_question"],
                       "discriminating_check": action["discriminating_check"]},
                operations=previous["admissible_operations"], changed=True)
            approach["next_operation"] = action["discriminating_check"]
            mark_permits_stale(campaign, approach["approach_id"])
            permit = issue_permit(campaign, kind="campaign_exploration", approach_id=approach["approach_id"],
                question_id=question["question_id"], question_revision=question["revision"],
                route_revision=campaign["routes"][approach["route_id"]]["revision"], operation=approach["next_operation"],
                expires_at=controller.clock() + campaign["policy"]["permit_lease_seconds"])
            approach.update(resume_condition=None, blocked_reason=None)
            if approach["status"] == "paused":
                request_readmission(campaign, approach["approach_id"], now=controller.clock())
        child = store.add_job(job["claim_id"], action["next_question"], parent_job=job["job_id"])
        child.update(native_target_claim_id=job["native_target_claim_id"], native_context_binding=packet["native_context_binding"],
            frontier_approach_id=approach["approach_id"], frontier_question_id=question["question_id"],
            native_intake_successor_for=job["native_intake_id"],
            native_intake_evidence_artifact=job["native_intake_artifact"],
            research_prior_checkpoint=job["native_intake_artifact"], research_directive={
                key: action[key] for key in ("rationale", "next_question", "first_uncertain_inference", "discriminating_check", "avoid")})
        if job.get("native_proof_checkpoint"):
            child["native_proof_checkpoint"] = job["native_proof_checkpoint"]
        handoff = {"intake_artifact": job["native_intake_artifact"],
                   "native_proof_checkpoint": job.get("native_proof_checkpoint"),
                   "directive": child["research_directive"], "authority": "advisory_investigation_only"}
        child["native_intake_handoff_artifact"] = store.put_artifact(
            json_text(handoff).encode(), name="native-intake-handoff.json")
        store.save_job(child)
        job["research_successor"] = child["job_id"]
        decisions[job["native_intake_id"]].update(permit_id=permit["permit_id"], successor=child["job_id"])
        result.update(status="investigation_admitted", program=child["job_id"])
    owner._edit(decide)
    job.update(status="finished", native_intake_result=result)
    job.setdefault("research_control", {})["closed"] = True
    store.save_job(job)
    return result
