"""Question contracts and normalized tool observations.

A successful call is not research progress. Coverage the owner did not
establish stays unknown. Metadata is not applicability.
"""

from __future__ import annotations

from typing import Any

from .records import FrontierRefusal, digest, new_id


OBSERVATION_STATUSES = frozenset({"success", "warning", "error"})
OBSERVATION_OUTCOMES = frozenset({
    "checked",
    "observed",
    "inconclusive",
    "unavailable",
    "timeout",
    "invalid_input",
    "failed",
})
TAIL_ACTIONS = frozenset({
    "source_fetch",
    "read_source",
    "experiment",
    "lean_check",
    "artifact_read",
    "derivation",
})


def bind_question(
    state: dict[str, Any],
    *,
    approach_id: str,
    uncertainty: str,
    why: str,
    scope: dict[str, Any],
    operations: list[str],
    changed: bool,
) -> dict[str, Any]:
    """A renamed question keeps the same lineage. A changed one is explicit."""
    approach = state["approaches"][approach_id]
    current = state["questions"][approach["question_id"]]
    lineage_key = digest({
        "approach_lineage": approach["lineage_id"],
        "uncertainty": uncertainty.strip(),
        "scope": scope,
        "admissible_operations": sorted(set(operations)),
    })
    if not changed or lineage_key == current.get("lineage_key"):
        current["revision"] = current["revision"]
        current["alias"] = uncertainty.strip()
        return current
    question = {
        "question_id": new_id("question"),
        "revision": 1,
        "approach_id": approach_id,
        "uncertainty": uncertainty.strip(),
        "why": why,
        "scope": scope,
        "admissible_operations": list(operations),
        "outcome_map": current["outcome_map"],
        "lineage_key": lineage_key,
        "previous_question_id": current["question_id"],
    }
    state["questions"][question["question_id"]] = question
    approach["question_id"] = question["question_id"]
    approach["bottleneck_obligation"] = approach["bottleneck_obligation"]
    approach["inconclusive_extensions"] = approach["inconclusive_extensions"]
    return question


def normalize_observation(
    *,
    status: str,
    outcome: str,
    summary: str,
    binding: dict[str, Any],
    declared_scope: str,
    script_reported_coverage: str,
    owner_observed_execution: str,
    mathematical_coverage: str | None,
    evidence_class: str,
    artifacts: list[str],
    next_actions: list[dict[str, Any]],
    recovery: dict[str, Any] | None,
    cost_receipts: list[str],
) -> dict[str, Any]:
    if status not in OBSERVATION_STATUSES:
        raise FrontierRefusal("unknown_observation_status")
    if outcome not in OBSERVATION_OUTCOMES:
        raise FrontierRefusal("unknown_observation_outcome")
    if evidence_class not in {"observation_only", "research_advance", "formal_advance"}:
        raise FrontierRefusal("observation_cannot_certify")
    if mathematical_coverage is not None and evidence_class == "observation_only":
        # Owner-established coverage may be recorded, but it is not a theorem.
        pass
    return {
        "status": status,
        "outcome": outcome,
        "summary": summary[:500],
        "binding": {
            "question_id": binding["question_id"],
            "approach_id": binding["approach_id"],
            "attempt_id": binding.get("attempt_id", ""),
            "root_binding": binding.get("root_binding", ""),
            "route_id": binding.get("route_id", ""),
            "route_revision": binding.get("route_revision"),
            "question_revision": binding.get("question_revision"),
            "subject_revision": binding.get("subject_revision"),
            "control_authorization": binding.get("control_authorization"),
            "native_target_claim_id": binding.get("native_target_claim_id"),
            "native_context_binding": binding.get("native_context_binding"),
        },
        "coverage": {
            "declared_scope": declared_scope,
            "script_reported_coverage": script_reported_coverage,
            "owner_observed_execution": owner_observed_execution,
            "mathematical_coverage": mathematical_coverage,
        },
        # Tool output, including self-reported coverage, has no authority to
        # certify either mathematical significance or a checked proposition.
        # Contribution review is a separate owner operation.
        "evidence_class": "observation_only",
        "artifacts": list(artifacts),
        "next_actions": list(next_actions),
        "recovery": recovery,
        "cost": list(cost_receipts),
        "continuation_credit": False,
    }


def store_observation(state: dict[str, Any], observation: dict[str, Any]) -> dict[str, Any]:
    observation = dict(observation)
    observation["observation_id"] = new_id("observation")
    observation["coverage_key"] = digest({
        "question_id": observation["binding"]["question_id"],
        "declared_scope": observation["coverage"]["declared_scope"],
        "owner_observed_execution": observation["coverage"]["owner_observed_execution"],
        "script_reported_coverage": observation["coverage"]["script_reported_coverage"],
        "artifacts": observation["artifacts"],
    })
    state["observations"][observation["observation_id"]] = observation
    return observation


def repeated_read(state: dict[str, Any], question_id: str, coverage_key: str) -> dict[str, Any] | None:
    for observation in state["observations"].values():
        if (
            observation["binding"]["question_id"] == question_id
            and observation.get("coverage_key") == coverage_key
        ):
            return {
                "cached": True,
                "continuation_credit": False,
                "observation_id": observation["observation_id"],
                "summary": observation["summary"],
                "reminder": observation["binding"]["question_id"],
            }
    return None


def register_source_application(
    state: dict[str, Any],
    *,
    question_id: str,
    source_hash: str,
    version: str,
    location: str,
    hypotheses: list[str],
    target: str,
    uncovered: list[str],
    stage: str,
) -> dict[str, Any]:
    if stage not in {"metadata", "source_inspection", "applicability", "formalization"}:
        raise FrontierRefusal("unknown_source_stage")
    record = {
        "application_id": new_id("source"),
        "question_id": question_id,
        "source_hash": source_hash,
        "version": version,
        "location": location,
        "hypotheses": list(hypotheses),
        "target": target,
        "uncovered": list(uncovered),
        "stage": stage,
        "kernel_verified": False,
    }
    if stage == "metadata":
        record["kernel_verified"] = False
        record["applicability"] = "not_assessed"
    elif uncovered:
        record["applicability"] = "missing_condition"
        record["kernel_verified"] = False
    elif stage == "applicability":
        record["applicability"] = "reviewed_not_checked"
        record["kernel_verified"] = False
    state["source_applications"][record["application_id"]] = record
    return record


def cached_source(state: dict[str, Any], source_hash: str, version: str) -> dict[str, Any] | None:
    for record in state["source_applications"].values():
        if record["source_hash"] == source_hash and record["version"] == version:
            return record
    return None


class MetadataConnector:
    """Initial literature connector. No matches are not a negative theorem."""

    name = "crossref-metadata"

    def coverage(self) -> str:
        return "bibliographic_metadata_only"


def register_experiment(state: dict[str, Any], spec: dict[str, Any]) -> dict[str, Any]:
    if spec.get("packages") or spec.get("install_packages"):
        raise FrontierRefusal("package_installation_forbidden")
    profile = spec.get("profile", "")
    profiles = state["manifest"].get("experiment_profiles", [])
    if profile not in profiles:
        raise FrontierRefusal("profile_unavailable")
    required = {"question_id", "profile", "script_hash", "input_hashes", "seed", "runtime_version", "limits"}
    if not required <= set(spec):
        raise FrontierRefusal("experiment_spec_incomplete")
    arithmetic = spec.get("arithmetic", "exact")
    if arithmetic not in {"exact", "floating"}:
        raise FrontierRefusal("unknown_arithmetic_mode")
    record = {
        "experiment_id": new_id("experiment"),
        "question_id": spec["question_id"],
        "profile": profile,
        "script_hash": spec["script_hash"],
        "input_hashes": list(spec["input_hashes"]),
        "seed": spec["seed"],
        "runtime_version": spec["runtime_version"],
        "limits": dict(spec["limits"]),
        "arithmetic": arithmetic,
        "status": "specified",
        "mutable_process": False,
        "refutes_exact_claim": False,
    }
    state["experiments"][record["experiment_id"]] = record
    return record


def interpret_experiment(state: dict[str, Any], experiment_id: str, *, outcome: str, exact_replay: bool, omitted_cases: bool) -> dict[str, Any]:
    experiment = state["experiments"][experiment_id]
    experiment["outcome"] = outcome
    experiment["exact_replay"] = exact_replay
    experiment["omitted_cases"] = omitted_cases
    if experiment["arithmetic"] == "floating":
        experiment["refutes_exact_claim"] = False
        experiment["evidence_class"] = "observation_only"
    elif omitted_cases or not exact_replay:
        experiment["refutes_exact_claim"] = False
        experiment["evidence_class"] = "observation_only"
        experiment["mathematical_coverage"] = None
    elif outcome == "counterexample" and exact_replay:
        experiment["refutes_exact_claim"] = False
        experiment["evidence_class"] = "observation_only"
        experiment["witness_status"] = "candidate_requires_independent_replay"
    else:
        experiment["evidence_class"] = "observation_only"
    experiment["status"] = "observed"
    return experiment


def accept_replayed_witness(state: dict[str, Any], experiment_id: str) -> dict[str, Any]:
    experiment = state["experiments"][experiment_id]
    if experiment.get("witness_status") != "candidate_requires_independent_replay":
        raise FrontierRefusal("no_witness_candidate")
    if experiment.get("omitted_cases") or experiment["arithmetic"] != "exact":
        raise FrontierRefusal("witness_not_exact")
    experiment["witness_status"] = "independently_replayed"
    experiment["evidence_class"] = "observation_only"
    experiment["scoped_obstruction_candidate"] = True
    return experiment


def default_manifest(*, experiments: bool, lean: bool) -> dict[str, Any]:
    return {
        "tools": [
            "literature_search",
            "fetch_source",
            "read_source_page",
            "search_source",
            "read_artifact",
            "read_claim",
            "record_note",
            *(["experiment"] if experiments else []),
            *(["formalize"] if lean else []),
        ],
        "experiment_profiles": ["stdlib"] if experiments else [],
        "formal_targets": ["lean"] if lean else [],
        "image_support": "requires_renderer_and_provider_support",
        "limits": {"experiments": experiments},
        "verified": False,
        "availability": "configured_actions; runtime and provider capability checked at execution",
        "connector": MetadataConnector.name,
        "connector_coverage": MetadataConnector().coverage(),
    }
