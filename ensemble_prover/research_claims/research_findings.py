"""Cumulative advisory research context and independently reviewed novelty."""

from __future__ import annotations

from typing import Any

from .model import load_json
from .research_control import native_job_context, native_job_target


def comparison_packet(store: Any, producer: dict[str, Any]) -> dict[str, Any]:
    """Index complete prior reports and the supplied baseline in this exact scope."""
    run = store.run_record(scheduling=True)
    jobs = {job["job_id"]: job for job in store.jobs()}
    target = native_job_target(producer, jobs)
    recorded_contexts = run.get("native_job_contexts", {})
    context = native_job_context(producer, jobs, recorded_contexts=recorded_contexts)
    baseline = list(run["sources"].values())
    initial = run.get("native_research_baselines", {}).get(context)
    if initial:
        baseline.append(initial)
    prior = []
    for job in jobs.values():
        artifact = job.get("investigation_artifact")
        if (not artifact or job["job_id"] == producer["job_id"]
                or (context is None and native_job_target(job, jobs) != target)
                or native_job_context(job, jobs, recorded_contexts=recorded_contexts) != context
                or (producer.get("research_report_sequence") is not None
                    and job.get("research_report_sequence", 0) >= producer["research_report_sequence"])):
            continue
        report = load_json(store.read_artifact(artifact).decode())
        prior.append({"artifact_id": artifact, "job_id": job["job_id"],
                      "method": report.get("method", "")[:160],
                      "derivation_excerpt": report.get("derivation", "")[:400],
                      "remaining_gap_excerpt": report.get("remaining_gap", "")[:250],
                      "coverage": "excerpt; inspect complete artifact for comparison"})
    findings = []
    strategy = run.get("strategy_review") or {}
    if strategy.get("owner_id") and (strategy.get("frontier_research") or {}).get("mode") == "adaptive":
        from .frontier.persist import load_campaign

        campaign = load_campaign(store, strategy["owner_id"])
        if campaign:
            findings = [{key: item[key] for key in (
                "finding_id", "conclusion", "assumptions", "kind", "report_artifact")}
                for item in campaign.get("research_findings", {}).values()
                if item["context_binding"] == context
                and (context is not None or item["target_claim_id"] == target)]
    return {"target_claim_id": target, "context_binding": context,
            "baseline_artifact_ids": list(dict.fromkeys(baseline)),
            "prior_reports": prior,
            "prior_report_artifact_ids": list(dict.fromkeys(item["artifact_id"] for item in prior)),
            "reviewed_findings": findings,
            "authority": "Research comparison is advisory; formal truth requires the existing verifier."}


def validate_delta(delta: Any) -> dict[str, Any]:
    """Require a precise conclusion and an explicit cumulative comparison."""
    if not isinstance(delta, dict):
        raise ValueError("progress_delta must be an object")
    fields = {"conclusion", "new_inference", "kind", "assumptions",
              "baseline_artifact_ids", "prior_report_artifact_ids"}
    if set(delta) != fields:
        raise ValueError("progress_delta requires conclusion, new_inference, kind, assumptions, baseline_artifact_ids and prior_report_artifact_ids")
    for field in ("conclusion", "new_inference", "kind"):
        if not isinstance(delta[field], str) or not delta[field].strip():
            raise ValueError(f"progress_delta.{field} must be nonempty text")
    if delta["kind"] not in {"derivation", "formalization", "source_verification", "obstruction"}:
        raise ValueError("unknown progress_delta kind")
    for field in ("assumptions", "baseline_artifact_ids", "prior_report_artifact_ids"):
        if (not isinstance(delta[field], list)
                or any(not isinstance(item, str) or not item.strip() for item in delta[field])):
            raise ValueError(f"progress_delta.{field} must be an array of nonempty strings")
    return delta


def assess_delta(controller: Any, campaign: dict[str, Any], producer: dict[str, Any], *,
                 reviewer_id: str, delta: dict[str, Any] | None, rationale: str,
                 subject: str | None = None) -> dict[str, Any]:
    """Share novelty accounting across independent report review pathways."""
    from .frontier.owner import report_scope_current
    from .frontier.progress import apply_contribution
    from .frontier.records import digest

    if not report_scope_current(controller, campaign, producer):
        return {"status": "stale", "credit_minted": False}
    if delta is None:
        return {"status": "novelty_unresolved", "credit_minted": False}
    finding = validate_delta(delta)
    comparison = comparison_packet(controller.store, producer)
    for field in ("baseline_artifact_ids", "prior_report_artifact_ids"):
        if set(finding[field]) != set(comparison[field]):
            return {"status": "cumulative_comparison_required", "credit_minted": False}
    identity = digest({
        "target": comparison["context_binding"] or comparison["target_claim_id"],
        "context": comparison["context_binding"],
        "conclusion": " ".join(finding["conclusion"].split()),
        "assumptions": sorted({" ".join(item.split()) for item in finding["assumptions"]}),
        "kind": finding["kind"],
    })
    findings = campaign.setdefault("research_findings", {})
    if identity in findings:
        return {"status": "repeated_conclusion", "credit_minted": False, "finding_id": identity}
    artifact = producer["investigation_artifact"]
    state = controller.snapshot()
    approach = campaign["approaches"][producer["frontier_approach_id"]]
    controller.store.read_artifact(artifact)
    result = apply_contribution(
        campaign, approach_id=approach["approach_id"], obligation_id=approach["bottleneck_obligation"],
        proposed_class="research_advance", subject=subject or approach.get("subject_id") or state["root_id"],
        context=campaign["root"]["context"], operation_id=reviewer_id, artifacts=[artifact],
        claim=finding["conclusion"], explanation=rationale, now=controller.clock(),
    )
    findings[identity] = {**finding, "finding_id": identity, "report_artifact": artifact,
                          "reviewer_id": reviewer_id, "producer_id": producer["job_id"],
                          "target_claim_id": comparison["target_claim_id"],
                          "context_binding": comparison["context_binding"],
                          "assessment": result, "kernel_verified": False}
    return result
