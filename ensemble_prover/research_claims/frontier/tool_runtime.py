"""Bind executed research tools to their paid response and exact question.

The existing tool backends own execution and resource limits. These records
retain provenance across checkpoints without treating successful execution as
mathematical progress or permitting another model request.
"""

from __future__ import annotations

from typing import Any

from .approaches import approach_is_held
from .hooks import mode_of, phase_for_scope
from .investigation import normalize_observation, register_source_application, store_observation
from .persist import load_campaign, save_campaign
from .records import digest

TOOLS = frozenset({
    "literature_search", "fetch_source", "read_source_page", "search_source",
    "experiment", "read_artifact", "read_claim",
})


def _enabled(loop: Any) -> bool:
    return loop.strategy is not None and mode_of(loop.strategy.controller.snapshot()) == "adaptive"


def _key(job: dict[str, Any], action: dict[str, Any]) -> str:
    return digest({"job": job["job_id"], "turn": job["turn"], "response": job["response"], "action": action})


def dispatch_binding(store: Any, state: dict[str, Any], job: dict[str, Any]) -> dict[str, Any] | None:
    """Capture the question at paid admission, before the provider can respond."""
    campaign = load_campaign(store, state["owner_id"])
    if campaign is None:
        return None
    approach = campaign["approaches"].get(job.get("frontier_approach_id", ""))
    authorization = campaign["review_authorizations"].get(job.get("frontier_review_authorization", ""))
    native_scope = {
        "native_target_claim_id": job.get("frontier_native_target_claim_id"),
        "native_context_binding": job.get("native_context_binding"),
    }
    if job["role"] == "review" and authorization is not None:
        # Inspection uses its own bounded control authorization, including when
        # the owner raised an objection before any approach was admitted.
        return {
            "question_id": "review:" + authorization["authorization_id"], "question_revision": 1,
            "approach_id": approach["approach_id"] if approach else "",
            "route_id": approach["route_id"] if approach else "", "route_revision": None,
            "root_binding": campaign["root"]["binding"], "subject_revision": job["revision"],
            "control_authorization": authorization["authorization_id"],
            "admissible_operations": ["literature", "experiment", "retrieval"],
            **native_scope,
        }
    if approach is None:
        return None
    question = campaign["questions"][approach["question_id"]]
    route = campaign["routes"][approach["route_id"]]
    return {
        "question_id": question["question_id"], "question_revision": question["revision"],
        "approach_id": approach["approach_id"], "route_id": route["route_id"], "route_revision": route["revision"],
        "root_binding": campaign["root"]["binding"], "subject_revision": job["revision"],
        "admissible_operations": list(question["admissible_operations"]),
        **native_scope,
    }


def begin_tool(loop: Any, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any] | None:
    """Persist intent or return a bounded refusal/cached result before execution."""
    if action["action"] not in TOOLS or not _enabled(loop):
        return None
    controller = loop.strategy.controller
    with controller._edit() as (state, run):
        current = loop.store.job(job["job_id"])
        if (current["status"] != "responded" or current["turn"] != job["turn"]
                or current.get("response") != job.get("response")):
            return {"status": "unavailable", "reason": "stale_response", "kernel_verified": False}
        campaign = load_campaign(loop.store, state["owner_id"])
        if campaign is None:
            return {"status": "unavailable", "reason": "frontier_unavailable", "kernel_verified": False}
        operations = campaign.setdefault("tool_operations", {})
        key = _key(job, action)
        previous = operations.get(key)
        if previous is not None:
            if previous.get("result_artifact"):
                return loop._read_json(previous["result_artifact"])
            # An interrupted external operation is not safe to repeat merely
            # because its response is being replayed after restart.
            return {"status": "interrupted_outcome_unknown", "reason": "tool_intent_already_recorded", "kernel_verified": False}
        approach_id = job.get("frontier_approach_id")
        approach = campaign["approaches"].get(approach_id or "")
        receipt = state["attempts"].get(job.get("frontier_response_attempt_id", ""))
        if (receipt is not None and (receipt.get("consumer_id") != job["job_id"]
                                     or job["response"] not in receipt.get("artifacts", []))):
            receipt = None
        binding = (receipt or {}).get("frontier_binding") or {}
        authorization = campaign["review_authorizations"].get(binding.get("control_authorization", ""))
        control = (job["role"] == "review" and authorization is not None
                   and job.get("frontier_review_authorization") == authorization["authorization_id"]
                   and authorization["status"] == "open")
        reason = None
        if (approach is None and not control) or receipt is None:
            reason = "tool_requires_bound_paid_response"
        elif controller.clock() >= run["deadline"]:
            reason = "deadline"
        elif run["status"] not in {"running", "budget_exhausted"}:
            reason = "run_stopped"
        elif not control and approach is not None and (
            approach_is_held(campaign, approach["approach_id"])
            or controller._blocked(state, [approach.get("subject_id") or state["root_id"]], approach.get("method", ""))
        ):
            reason = "suspended"
        elif loop.store.get_claim(job["claim_id"])["revision"] != job["revision"]:
            reason = "claim_changed"
        elif loop.store.get_claim(run["target_id"])["revision"] != run["target_revision"]:
            reason = "root_changed"
        if (approach is None and not control) or receipt is None:
            return {"status": "unavailable", "reason": reason, "kernel_verified": False}
        if control:
            question = {"uncertainty": job["question"], "admissible_operations": binding["admissible_operations"]}
        else:
            assert approach is not None
            question = campaign["questions"][approach["question_id"]]
        if not binding:
            return {"status": "unavailable", "reason": "tool_requires_bound_paid_response", "kernel_verified": False}
        if not control:
            assert approach is not None
            route = campaign["routes"][approach["route_id"]]
            if (binding["approach_id"] != approach_id or binding["question_id"] != question["question_id"]
                    or binding["question_revision"] != question["revision"]
                    or binding["route_id"] != route["route_id"] or binding["route_revision"] != route["revision"]):
                reason = "question_or_route_changed"
        if binding["root_binding"] != campaign["root"]["binding"]:
            reason = "question_or_route_changed"
        if (binding.get("native_target_claim_id") != run.get("native_active_target_claim_id")
                or binding.get("native_context_binding") != run.get("native_active_target_context_binding")):
            reason = "native_grant_scope_changed"
        category = ("experiment" if action["action"] == "experiment" else
                    "retrieval" if action["action"] in {"read_artifact", "read_claim"} else "literature")
        allowed = set(binding.get("admissible_operations", []))
        current_allowed = set(question["admissible_operations"])
        if category != "retrieval" and not all(
            category in operations or action["action"] in operations for operations in (allowed, current_allowed)
        ):
            reason = reason or "operation_outside_question"
        operation = {
            "operation_id": key, "job_id": job["job_id"], "action": action["action"],
            "response_artifact": job["response"], "status": "deferred" if reason else "running",
            "binding": {**binding, "attempt_id": receipt["attempt_id"]},
            "declared_scope": str(action.get("scope") or action.get("query") or question["uncertainty"]),
            "input_artifact": loop._blob(action, "research-tool-input.json"),
            "started_at": controller.clock(),
        }
        operations[key] = operation
        phase_for_scope(campaign, binding.get("native_target_claim_id"), binding.get("native_context_binding"))["tails"][receipt["attempt_id"]] = {
            "receipt_id": receipt["attempt_id"], "operation_id": key,
            "action": action["action"], "status": operation["status"],
            "provider_admission": False, "continuation_credit": False,
        }
        if not reason:
            if control:
                campaign["history"]["control_tool_admissions"] = campaign["history"].get("control_tool_admissions", 0) + 1
            else:
                campaign["history"]["costs_by_approach"][approach_id]["tool_admissions"] += 1
        save_campaign(loop.store, state["owner_id"], run["target_id"], campaign)
        if reason:
            return {"status": "unavailable", "reason": reason, "kernel_verified": False}
    return None


def record_tool_result(loop: Any, job: dict[str, Any], action: dict[str, Any], result: Any) -> None:
    """Settle a tool receipt before checkpointing the response that produced it."""
    if action["action"] not in TOOLS or not _enabled(loop):
        return
    controller = loop.strategy.controller
    with controller._edit() as (state, run):
        campaign = load_campaign(loop.store, state["owner_id"])
        if campaign is None:
            return
        operation = campaign.get("tool_operations", {}).get(_key(job, action))
        if operation is None or operation.get("result_artifact"):
            return
        result_artifact = loop._blob(result, "research-tool-observation.json")
        body = result if isinstance(result, dict) else {}
        status = body.get("status", "completed")
        success = status in {"completed", "success", "ok"}
        outcome = "observed" if success else "timeout" if status == "timeout" else (
            "unavailable" if status in {"unavailable", "tool_unavailable"} else "inconclusive"
        )
        observation = normalize_observation(
            status="success" if success else "warning", outcome=outcome,
            summary=str(body.get("reason") or body.get("coverage") or status), binding=operation["binding"],
            declared_scope=operation["declared_scope"],
            script_reported_coverage="unverified output in " + result_artifact if action["action"] == "experiment" else "not_applicable",
            owner_observed_execution=str({"status": status, "runtime_started": body.get("runtime_started"),
                                         "complete": body.get("complete"), "exit_code": body.get("exit_code")}),
            mathematical_coverage=None, evidence_class="observation_only", artifacts=[result_artifact],
            next_actions=[], recovery=None if success else {"reason": str(body.get("reason", status))},
            cost_receipts=[operation["operation_id"]],
        )
        saved = store_observation(campaign, observation)
        operation.update(result_artifact=result_artifact, observation_id=saved["observation_id"],
                         status="completed" if success else "incomplete", finished_at=controller.clock())
        if action["action"] == "experiment":
            campaign["experiments"][operation["operation_id"]] = {
                "experiment_id": operation["operation_id"], "question_id": operation["binding"]["question_id"],
                "profile": "stdlib", "script_artifact": loop.store.put_artifact(
                    str(action["code"]).encode(), name="research-experiment.py"),
                "spec_artifact": operation["input_artifact"], "result_artifact": result_artifact,
                "status": operation["status"], "environment": body.get("environment", {}),
                "mutable_process": False, "evidence_class": "observation_only", "mathematical_coverage": None,
                "refutes_exact_claim": False,
            }
        tail = phase_for_scope(campaign, operation["binding"].get("native_target_claim_id"),
                               operation["binding"].get("native_context_binding"))["tails"].get(operation["binding"]["attempt_id"])
        if tail is not None and tail.get("operation_id") == operation["operation_id"]:
            tail["status"] = operation["status"]
        if action["action"] in {"literature_search", "fetch_source", "read_source_page", "search_source"}:
            source = body.get("source_artifact") or body.get("original_artifact") or action.get("artifact_id")
            if isinstance(source, str) and success:
                register_source_application(
                    campaign, question_id=operation["binding"]["question_id"], source_hash=source,
                    version=source, location=str(action.get("page") or action.get("url") or action.get("query", "")),
                    hypotheses=[], target=operation["declared_scope"], uncovered=["applicability not independently assessed"],
                    stage="metadata" if action["action"] == "literature_search" else "source_inspection",
                )
        current = loop.store.job(job["job_id"])
        if current["turn"] == job["turn"] and current.get("response") == job.get("response"):
            current["frontier_last_observation"] = saved["observation_id"]
            job["frontier_last_observation"] = saved["observation_id"]
            loop.store.save_job(current)
        save_campaign(loop.store, state["owner_id"], run["target_id"], campaign)
