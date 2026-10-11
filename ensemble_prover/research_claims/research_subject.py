"""Immutable advisory assignments and exact delivery observations.

Subject identity binds a review, never mathematical authority or comprehension.
"""
from __future__ import annotations

import hashlib
import json
from typing import Any

from .model import json_text


def ensure_subject(store: Any, job: dict[str, Any]) -> dict[str, Any] | None:
    if not job.get("research_reorientation_for"):
        return None
    reference = job.get("assigned_research_subject")
    if reference:
        return json.loads(store.read_artifact(reference))
    checkpoint_id = job["research_checkpoint"]
    checkpoint = json.loads(store.read_artifact(checkpoint_id))
    # A checkpoint's frozen producer takes precedence over its live successor.
    producer = (json.loads(store.read_artifact(checkpoint["complete_job_artifact"]))
                if checkpoint.get("complete_job_artifact") else
                store.job(job["research_reorientation_for"]))
    report = checkpoint.get("investigation_artifact") or producer.get("investigation_artifact")
    if report:
        store.read_artifact(report)
    binding = producer.get("frontier_report_basis", {}).get("binding", {})
    packet = {
        "version": 1, "reviewer_job_id": job["job_id"],
        "producer_job_id": job["research_reorientation_for"],
        "checkpoint_artifact": checkpoint_id, "report_artifact": report,
        "question": producer.get("question", checkpoint.get("assignment", job["question"])),
        "question_id": producer.get("frontier_question_id"),
        "question_revision": binding.get("question_revision", producer.get("revision")), "binding": binding,
        "inspection": "unknown", "authority": "advisory_assignment_only",
    }
    native_checkpoint = producer.get("native_proof_checkpoint")
    if native_checkpoint:
        native = json.loads(store.read_artifact(native_checkpoint))
        packet["research_contracts"] = native.get("research_contracts", [])
        packet["diagnostic_capabilities"] = native.get("diagnostic_capabilities", {})
        packet["native_checkpoint_artifact"] = native_checkpoint
    # A compact comparison concerns the exact current question. Full histories
    # remain referenced; unknown global novelty does not block a scoped next task.
    packet["scoped_comparison"] = {
        "root_contract": store.get_claim(job["claim_id"])["spec"]["contract"],
        "question": packet["question"], "question_id": packet["question_id"],
        "binding": packet["binding"], "global_novelty": "unknown",
        "instruction": "Compare this exact question and its cited premises first. You may reorient on scoped evidence without claiming global novelty. Substantive credit still requires the cumulative comparison; missing source inspection is unknown."}
    from .research_findings import comparison_packet
    comparison = comparison_packet(store, producer)
    jobs = {item["job_id"]: item for item in store.jobs()}
    same_question = [item for item in comparison["prior_reports"]
                     if (producer.get("frontier_question_id") is not None
                         and jobs[item["job_id"]].get("frontier_question_id") == producer["frontier_question_id"])
                     or (producer.get("frontier_question_id") is None
                         and jobs[item["job_id"]].get("question") == producer.get("question"))]
    scoped = {**packet["scoped_comparison"], "research_contracts": packet.get("research_contracts", []),
              "prior_reports": same_question, "scoped_obstructions": comparison["scoped_obstructions"],
              "full_baseline_artifact_ids": comparison["baseline_artifact_ids"],
              "full_prior_report_artifact_ids": comparison["prior_report_artifact_ids"],
              "coverage": "exact_contracts_and_report_excerpts_not_full_source_inspection"}
    from .context_window import window
    scoped = window(store, scoped, limit=6000)
    scoped_artifact = store.put_artifact(json_text(scoped).encode(), name="question-scoped-comparison.json")
    packet["scoped_comparison"] = {"artifact_id": scoped_artifact,
        "baseline_artifact_ids": [scoped_artifact],
        "prior_report_artifact_ids": [item["artifact_id"] for item in same_question],
        "scope": "assigned_question", "global_novelty": "unknown",
        "instruction": "For question-scoped research novelty cite this artifact as comparison_scope_artifact in progress_delta and compare its exact question, cited contracts, prior reports and scoped obstructions. Missing full-history inspection remains unknown. This can only earn advisory research progress, never formal credit."}
    packet["subject_id"] = hashlib.sha256(json_text(packet).encode()).hexdigest()
    reference = store.put_artifact(json_text(packet).encode(), name="assigned-research-subject.json")
    job["assigned_research_subject"] = reference
    store.save_job(job)
    return packet


def subject_view(store: Any, job: dict[str, Any]) -> dict[str, Any] | None:
    packet = ensure_subject(store, job)
    if packet is None:
        return None
    artifact = packet["report_artifact"] or packet["checkpoint_artifact"]
    return {**packet, "subject_artifact": job["assigned_research_subject"],
            "report_text": store.read_artifact(artifact).decode(),
            "content_artifact": artifact, "offset": 0, "coverage": "complete"}


def bounded_subject(store: Any, value: dict[str, Any], limit: int) -> dict[str, Any]:
    """Identity and exact pointer always precede text and older context."""
    result = {key: value[key] for key in ("subject_id", "subject_artifact", "report_artifact")}
    result.update(coverage="not_in_this_window", inspection="unknown")
    if len(json_text(result)) > limit:
        raise ValueError("context limit cannot fit assigned subject identity")
    for key in ("checkpoint_artifact", "question_id", "question_revision", "binding", "research_contracts", "diagnostic_capabilities", "question", "scoped_comparison"):
        candidate = {**result, key: value.get(key)}
        if len(json_text(candidate)) <= limit:
            result = candidate
    # Prefix slicing is exact and Unicode-safe; measure JSON escaping, not len(text).
    if isinstance(value.get("report_text"), str):
        prefix = {**result, "content_artifact": value["content_artifact"], "offset": 0,
                  "total_characters": len(value["report_text"]), "coverage": "partial", "report_text": ""}
        if len(json_text(prefix)) <= limit:
            low, high = 0, len(value["report_text"])
            while low < high:
                middle = (low + high + 1) // 2
                if len(json_text({**prefix, "report_text": value["report_text"][:middle]})) <= limit:
                    low = middle
                else:
                    high = middle - 1
            prefix["report_text"] = value["report_text"][:low]
            if low == len(value["report_text"]):
                prefix["coverage"] = "complete"
            result = prefix
    return result


def delivery_manifest(store: Any, messages: list[dict[str, Any]], request_artifact: str, *,
                      dispatch_attempt_id: str = "", response_artifact: str = "") -> dict[str, Any]:
    """Observe exact surviving text in the final provider request, not read history."""
    pages: list[dict[str, Any]] = []
    subjects: list[str] = []
    def visit(value: Any) -> None:
        if isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, dict):
            subject = value.get("assigned_research_subject")
            if isinstance(subject, dict) and isinstance(subject.get("subject_id"), str):
                subjects.append(subject["subject_id"])
            aid, offset = value.get("content_artifact"), value.get("offset")
            content = value.get("report_text", value.get("text"))
            if isinstance(aid, str) and type(offset) is int and offset >= 0 and isinstance(content, str):
                original = store.read_artifact(aid).decode()
                if original[offset:offset + len(content)] == content:
                    page = {"content_artifact": aid, "offset": offset, "end": offset + len(content),
                            "total_characters": len(original),
                            "coverage": "complete" if offset == 0 and len(content) == len(original) else "partial"}
                    if page not in pages:
                        pages.append(page)
            for child in value.values():
                if isinstance(child, (dict, list)):
                    visit(child)
    for message in messages:
        content = message.get("content")
        if isinstance(content, str):
            try:
                visit(json.loads(content))
            except (ValueError, RecursionError):
                pass
        else:
            visit(content)
    confirmed = bool(dispatch_attempt_id and response_artifact)
    return {"version": 2, "request_artifact": request_artifact,
            "subject_id": subjects[0] if subjects else None, "prepared_ranges": pages,
            "delivered_ranges": pages if confirmed else [],
            "dispatch_status": "response_received" if confirmed else "not_confirmed",
            "dispatch_attempt_id": dispatch_attempt_id or None,
            "response_artifact": response_artifact or None,
            "inspection": "unknown", "coverage_basis": "final_serialized_request",
            "delivery_evidence": "response_for_authorized_request" if confirmed else "prepared_only",
            "authority": "delivery_observation_only"}
