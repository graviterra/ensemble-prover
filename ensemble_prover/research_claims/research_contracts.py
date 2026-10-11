"""Exact helper references and proposed research bridges without proof authority."""
from __future__ import annotations

from dataclasses import asdict
import hashlib
from typing import Any

from .model import MathematicalContract, Obligation, json_text, object_fields, text

RELATIONS = {"equivalent", "sufficient", "necessary", "diagnostic", "unknown"}
REQUEST_FIELDS = {"contract", "cited_helpers", "relation_to_root", "route_id", "obligation_id",
                  "question_revision", "quantitative_budget", "parameter_dependencies"}


def helper_inventory(dossier: Any) -> dict[str, dict[str, Any]]:
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    if isinstance(helpers, dict):
        helpers = helpers.values()
    result = {}
    for helper in helpers:
        name = str(getattr(helper, "name", ""))
        source = str(getattr(helper, "source", ""))
        if not name or not source:
            continue
        result[name] = {
            "name": name, "source_hash": hashlib.sha256(source.encode()).hexdigest(),
            "contract_identity": str(getattr(helper, "contract_identity", "")),
            "environment_hash": str(getattr(helper, "verification_environment_hash", "")),
            "display_statement": str(getattr(helper, "contract_display_statement", "")),
            "open_premises": list(getattr(helper, "open_premise_statements", ()) or ()),
            "binder_sorts": list(getattr(helper, "contract_binder_sorts", ()) or ()),
            "proof_binder_types": list(getattr(helper, "contract_proof_binder_types", ()) or ()),
            "evidence_level": "local_helper_reference_not_root_reduction",
        }
    return result


def bind_request(payload: dict[str, Any], inventory: dict[str, dict[str, Any]], *,
                 root_statement: str, context_binding: str) -> dict[str, Any]:
    """Validate claimed identities; record every proposed bridge as unresolved."""
    contract = MathematicalContract.from_dict(payload.get("contract", {
        "statement": payload["statement"], "domain": "native research advisory obligation"}))
    if contract.statement != payload["statement"]:
        raise ValueError("contract.statement must equal the exact research statement")
    relation = payload.get("relation_to_root", "unknown")
    if relation not in RELATIONS:
        raise ValueError("unknown relation_to_root")
    for key in ("route_id", "obligation_id", "quantitative_budget"):
        if key in payload:
            text(payload[key], key)
    if "question_revision" in payload and (type(payload["question_revision"]) is not int or payload["question_revision"] < 0):
        raise ValueError("question_revision must be a nonnegative integer")
    dependencies = payload.get("parameter_dependencies", [])
    if not isinstance(dependencies, list) or any(not isinstance(item, str) or not item.strip() for item in dependencies):
        raise ValueError("parameter_dependencies must be nonempty strings")
    references = payload.get("cited_helpers", [])
    if not isinstance(references, list) or len(references) > 16:
        raise ValueError("cited_helpers must contain at most 16 helper references")
    bound, obligations = [], []
    for reference in references:
        object_fields(reference, {"name", "source_hash", "contract_identity", "environment_hash",
                                  "instantiation", "claimed_premise"}, {"name", "source_hash"}, "helper reference")
        for key, value in reference.items():
            text(value, "helper reference " + key)
        helper = inventory.get(reference["name"])
        if helper is None:
            raise ValueError("cited helper is absent from the active helper inventory")
        for key in ("source_hash", "contract_identity", "environment_hash"):
            if key in reference and reference[key] != helper[key]:
                raise ValueError("cited helper has stale or mismatched " + key)
        bound.append({**helper, "instantiation": reference.get("instantiation"),
                      "claimed_premise": reference.get("claimed_premise"), "relation_verified": False})
        premise = reference.get("claimed_premise") or "the cited helper's exact instantiated open premise"
        identity = hashlib.sha256(json_text([context_binding, contract.statement, helper, reference]).encode()).hexdigest()
        obligation = Obligation("compatibility-" + identity, "native-research", MathematicalContract(
            f"The proposed estimate ({contract.statement}) implies ({premise}) in the pinned context.",
            "Compatibility of the proposed estimate with the cited helper",
            hypotheses=contract.hypotheses, quantifiers=contract.quantifiers))
        obligations.append({**asdict(obligation), "status": "unresolved", "kernel_verified": False,
                            "helper_name": helper["name"], "authority": "advisory_obligation",
                            "instruction": "Check coefficients, quantifier order and parameter dependence before pursuing this estimate. Formal discharge requires the existing owner-validated reduction/export receipt."})
    return {"version": 1, "root_statement": root_statement, "context_binding": context_binding,
            "research_contract": asdict(contract), "cited_helpers": bound,
            "compatibility_obligations": obligations, "relation_to_root": relation,
            "relation_evidence_level": "proposed" if relation != "unknown" else "unknown",
            "quantitative_budget": payload.get("quantitative_budget"), "parameter_dependencies": dependencies,
            "route_id": payload.get("route_id"), "obligation_id": payload.get("obligation_id"),
            "question_revision": payload.get("question_revision"), "kernel_verified": False}


def diagnostic_proposal(store: Any, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any]:
    """Queue only a bounded existing-tool proposal; do not execute experiments."""
    text(action["scope"], "diagnostic scope")
    text(action["expected_outcomes"], "diagnostic outcomes")
    query = action["queries"]
    if (not isinstance(query, list) or not 1 <= len(query) <= 8
            or any(not isinstance(item, str) or not item.strip() or len(item) > 320 for item in query)
            or sum(map(len, query)) > 1800):
        raise ValueError("diagnostic queries exceed compute_examples limits")
    mode = action.get("mode", "eval")
    if mode not in {"eval", "reduce", "check"}:
        raise ValueError("invalid compute_examples mode")
    contract = MathematicalContract.from_dict(action["contract"])
    proposal = {"target_tool": "compute_examples", "scope": action["scope"],
                "contract": asdict(contract), "expected_outcomes": action["expected_outcomes"],
                "parameters": {"queries": query, "mode": mode, "purpose": action["scope"]},
                "status": "proposed_for_proof_owner", "kernel_verified": False,
                "authority": "finite_diagnostic_not_root_disproof"}
    artifact = store.put_artifact(json_text(proposal).encode(), name="diagnostic-proposal.json")
    proposals = job.setdefault("diagnostic_proposals", [])
    if artifact not in proposals:
        proposals.append(artifact)
    store.save_job(job)
    return {**proposal, "artifact_id": artifact,
            "instruction": "The proof owner may submit these parameters through its enabled compute_examples tool and existing budget. That executor validates admissibility; this proposal does not authorize execution."}


def scoped_obstruction(store: Any, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any]:
    contract = MathematicalContract.from_dict(action["contract"])
    text(action["reason"], "scoped obstruction")
    sources = action["evidence_artifact_ids"]
    if not isinstance(sources, list) or not sources or any(not isinstance(aid, str) for aid in sources):
        raise ValueError("scoped obstruction requires evidence artifact references")
    for aid in sources:
        store.read_artifact(aid)
    record = {"contract": asdict(contract), "reason": action["reason"], "evidence_artifact_ids": sources,
              "status": "advisory_obstruction", "kernel_verified": False,
              "scope": "only_the_named_auxiliary_contract", "root_status_changed": False}
    artifact = store.put_artifact(json_text(record).encode(), name="scoped-obstruction.json")
    job.setdefault("scoped_obstructions", []).append(artifact)
    store.save_job(job)
    return {**record, "artifact_id": artifact}
