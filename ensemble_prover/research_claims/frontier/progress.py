"""Route relevance, evidence identity, and single-use continuation credit.

Search priority never becomes mathematical authority. A checked chain is the
only formal contribution to the root; everything else is research evidence.
"""

from __future__ import annotations

from typing import Any

from .records import (
    AUTHORITY_TIERS,
    EVIDENCE_CLASSES,
    PERMIT_KINDS,
    REDUCTION_LEVELS,
    FrontierRefusal,
    digest,
    new_id,
)


def _approach(state: dict[str, Any], approach_id: str) -> dict[str, Any]:
    try:
        return state["approaches"][approach_id]
    except KeyError as exc:
        raise FrontierRefusal("unknown_approach") from exc


def _permit(state: dict[str, Any], permit_id: str) -> dict[str, Any]:
    try:
        return state["permits"][permit_id]
    except KeyError as exc:
        raise FrontierRefusal("unknown_permit") from exc


def add_obligation(
    state: dict[str, Any],
    *,
    proposition: str,
    context: str,
    source_revision: str,
    assumptions: list[str] | None = None,
    obligation_id: str | None = None,
) -> dict[str, Any]:
    if not isinstance(proposition, str) or not proposition.strip():
        raise FrontierRefusal("obligation_requires_proposition")
    record = {
        "obligation_id": obligation_id or new_id("obligation"),
        "proposition": proposition.strip(),
        "context": context,
        "source_revision": source_revision,
        "assumptions": list(assumptions or []),
        "consumers": [],
        "dispatch": "unassigned",
        "identity": digest({
            "proposition": proposition.strip(),
            "context": context,
            "assumptions": list(assumptions or []),
        }),
    }
    state["obligations"][record["obligation_id"]] = record
    if state["root_obligation"] is None:
        state["root_obligation"] = record["obligation_id"]
    return record


def _reduction_graph(state: dict[str, Any]) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for reduction in state["reductions"].values():
        graph.setdefault(reduction["consequent"], set())
        for antecedent in reduction["antecedents"]:
            graph.setdefault(antecedent, set()).add(reduction["consequent"])
    return graph


def _has_cycle(graph: dict[str, set[str]]) -> bool:
    visiting: set[str] = set()
    visited: set[str] = set()
    for root in graph:
        stack = [(root, False)]
        while stack:
            node, leaving = stack.pop()
            if leaving:
                visiting.discard(node)
                visited.add(node)
            elif node in visiting:
                return True
            elif node not in visited:
                visiting.add(node)
                stack.append((node, True))
                stack.extend((child, False) for child in sorted(graph.get(node, ())))
    return False


def add_reduction(
    state: dict[str, Any],
    *,
    antecedents: list[str],
    consequent: str,
    level: str,
    quantitative: str = "",
    certificate: str | None = None,
    well_founded: bool = False,
    route_id: str | None = None,
) -> dict[str, Any]:
    if level not in REDUCTION_LEVELS:
        raise FrontierRefusal("unknown_reduction_level")
    if not antecedents or consequent in antecedents:
        raise FrontierRefusal("reduction_requires_distinct_obligations")
    known = state["obligations"]
    if consequent not in known or any(item not in known for item in antecedents):
        raise FrontierRefusal("unknown_obligation")
    if level == "checked" and not certificate:
        raise FrontierRefusal("checked_reduction_requires_certificate")
    if level == "checked" and not _checked_certificate_matches(state, certificate, antecedents, consequent):
        raise FrontierRefusal("checked_reduction_requires_verified_receipt")
    record = {
        "reduction_id": new_id("reduction"),
        "antecedents": list(antecedents),
        "consequent": consequent,
        "level": level,
        "quantitative": quantitative,
        "certificate": certificate,
        "well_founded": bool(well_founded),
        "route_id": route_id,
    }
    state["reductions"][record["reduction_id"]] = record
    if _has_cycle(_reduction_graph(state)) and not well_founded:
        del state["reductions"][record["reduction_id"]]
        raise FrontierRefusal("cyclic_dependency")
    return record


def _checked_certificate_matches(
    state: dict[str, Any], certificate: str | None, antecedents: list[str], consequent: str
) -> bool:
    record = state.get("checked_reduction_receipts", {}).get(certificate or "", {})
    return bool(
        record.get("root_binding") == state["root"]["binding"]
        and record.get("antecedents") == [state["obligations"][item]["identity"] for item in antecedents]
        and record.get("consequent") == state["obligations"][consequent]["identity"]
        and record.get("receipt_digest")
    )


def _checked_fact_matches(state: dict[str, Any], obligation_id: str, artifacts: list[str] | None = None) -> bool:
    record = state.get("checked_facts", {}).get(obligation_id, {})
    obligation = state["obligations"].get(obligation_id, {})
    return bool(
        record.get("root_binding") == state["root"]["binding"]
        and record.get("identity") == obligation.get("identity")
        and record.get("receipt_digest")
        and (artifacts is None or record.get("artifact_id") in artifacts)
    )


def _checked_implications(state: dict[str, Any]) -> list[dict[str, Any]]:
    """Checked, non-well-founded implications. A joint antecedent list is a conjunction."""
    return [
        reduction for reduction in state["reductions"].values()
        if reduction.get("level") == "checked"
        and not reduction.get("well_founded")
        and reduction.get("certificate")
        and reduction.get("antecedents")
        and _checked_certificate_matches(
            state, reduction["certificate"], reduction["antecedents"], reduction["consequent"]
        )
    ]


def _established_by_checked(state: dict[str, Any], start: str) -> set[str]:
    """Obligations implied by start. Every antecedent of a reduction must already be established."""
    established = {start}
    changed = True
    while changed:
        changed = False
        for reduction in _checked_implications(state):
            consequent = reduction["consequent"]
            if consequent in established:
                continue
            if all(item in established for item in reduction["antecedents"]):
                established.add(consequent)
                changed = True
    return established


def certificates_on_checked_path(state: dict[str, Any], start: str, goal: str) -> list[str]:
    """Certificates of checked reductions that establish a path from start to goal.

    One premise of a joint reduction does not carry its certificate. A
    well-founded back-edge can make another obligation reachable after the
    root, but that edge is not evidence that the credited obligation implies
    the root.
    """
    if not start or not goal or start == goal:
        return []
    established = _established_by_checked(state, start)
    if goal not in established:
        return []
    supporting = [
        reduction for reduction in _checked_implications(state)
        if all(item in established for item in reduction["antecedents"])
    ]
    needed = {goal}
    changed = True
    while changed:
        changed = False
        for reduction in supporting:
            if reduction["consequent"] not in needed:
                continue
            for antecedent in reduction["antecedents"]:
                if antecedent not in needed:
                    needed.add(antecedent)
                    changed = True
    return sorted({
        reduction["certificate"]
        for reduction in supporting
        if reduction["consequent"] in needed
    })


def reaches_via_checked(state: dict[str, Any], start: str, goal: str) -> bool:
    """True when checked reductions carry start to goal. Proposed edges do not.

    A reduction fires only after every antecedent is established. Different
    reductions remain alternatives.
    """
    if start == goal:
        return True
    if not start or not goal:
        return False
    return goal in _established_by_checked(state, start)


def _route_joint_premise_held(state: dict[str, Any], approach: dict[str, Any], obligation_id: str) -> bool:
    """True when this route's reduction still depends on a held co-premise."""
    route = state["routes"].get(approach.get("route_id") or "", {})
    held = {
        item["obligation_id"]
        for item in state.get("scoped_holds", [])
        if item.get("active") and item.get("obligation_id")
    }
    if not held:
        return False
    for reduction_id in route.get("reductions", []):
        reduction = state["reductions"].get(reduction_id, {})
        antecedents = reduction.get("antecedents") or []
        if obligation_id not in antecedents:
            continue
        if any(item != obligation_id and item in held for item in antecedents):
            return True
    return False


def route_requires(state: dict[str, Any], route_id: str, obligation_id: str) -> bool:
    route = state["routes"].get(route_id)
    if route is None:
        return False
    if obligation_id in {route.get("bottleneck"), route.get("root_obligation")}:
        return True
    for reduction_id in route.get("reductions", []):
        reduction = state["reductions"].get(reduction_id, {})
        if obligation_id in reduction.get("antecedents", []) or obligation_id == reduction.get("consequent"):
            return True
    return False


def add_route(
    state: dict[str, Any],
    *,
    approach_id: str,
    bottleneck: str,
    reduction_ids: list[str],
    viability: str = "exploratory",
) -> dict[str, Any]:
    if bottleneck not in state["obligations"]:
        raise FrontierRefusal("unknown_obligation")
    if any(item not in state["reductions"] for item in reduction_ids):
        raise FrontierRefusal("unknown_reduction")
    record = {
        "route_id": new_id("route"),
        "revision": 1,
        "approach_id": approach_id,
        "root_binding": state["root"]["binding"],
        "bottleneck": bottleneck,
        "root_obligation": state["root_obligation"],
        "reductions": list(reduction_ids),
        "viability": viability,
    }
    state["routes"][record["route_id"]] = record
    return record


def classify_contribution(
    state: dict[str, Any],
    *,
    approach_id: str,
    obligation_id: str | None,
    proposed_class: str,
) -> str:
    """Map a candidate onto an evidence class without inventing root progress."""
    if proposed_class not in EVIDENCE_CLASSES | {"retained_certificate"}:
        raise FrontierRefusal("unknown_evidence_class")
    if proposed_class in {"root_verified", "root_refuted", "operational_failure", "observation_only", "route_obstruction"}:
        return proposed_class
    approach = _approach(state, approach_id)
    if obligation_id is not None and obligation_id not in state["obligations"]:
        raise FrontierRefusal("unknown_obligation")
    bottleneck = approach.get("bottleneck_obligation")
    if proposed_class == "formal_advance":
        if obligation_id is None or obligation_id != bottleneck:
            return "observation_only"
        if not _checked_fact_matches(state, obligation_id):
            return "research_advance"
        route_id = approach.get("route_id")
        route = state["routes"].get(route_id or "", {})
        root = route.get("root_obligation") or state["root_obligation"]
        if root and not reaches_via_checked(state, obligation_id, root):
            if _route_joint_premise_held(state, approach, obligation_id):
                return "observation_only"
            return "research_advance"
        return "formal_advance"
    if proposed_class == "research_advance":
        if obligation_id is not None and bottleneck is not None and obligation_id != bottleneck:
            return "observation_only"
        return "research_advance"
    return proposed_class


def register_event(
    state: dict[str, Any],
    *,
    subject: str,
    context: str,
    operation_id: str,
    artifacts: list[str],
    claim: str,
    evidence_class: str,
    location: str = "",
) -> tuple[dict[str, Any], bool]:
    """One mathematical conclusion. Labels, routes, and reviewers are not identity."""
    if evidence_class not in EVIDENCE_CLASSES:
        raise FrontierRefusal("unknown_evidence_class")
    if not isinstance(artifacts, list) or any(not isinstance(item, str) or not item for item in artifacts):
        raise FrontierRefusal("artifacts_required")
    artifacts = sorted(set(artifacts))
    identity = digest({
        "subject": subject,
        "context": context,
        "artifacts": artifacts,
        "location": location,
    })
    for event in state["evidence_events"].values():
        if event["identity"] == identity:
            return event, False
    event = {
        "event_id": new_id("evidence"),
        "identity": identity,
        "group": "",
        "subject": subject,
        "context": context,
        "operation_id": operation_id,
        "artifacts": list(artifacts),
        "claim": claim,
        "location": location,
        "evidence_class": evidence_class,
        "distinctness": "distinct",
        "formal_certificate": evidence_class == "formal_advance",
    }
    event["group"] = event["event_id"]
    state["evidence_events"][event["event_id"]] = event
    return event, True


def _live_entitlement(state: dict[str, Any], group: str, tier: str) -> dict[str, Any] | None:
    found = [
        item for item in state["entitlements"].values()
        if item["group"] == group and item["tier"] == tier and item["status"] == "live"
    ]
    if len(found) > 1:
        raise FrontierRefusal("duplicate_live_entitlement")
    return found[0] if found else None


def _formal_entitlement_current(state: dict[str, Any], entitlement: dict[str, Any]) -> bool:
    for decision in state.get("decisions", []):
        event = state["evidence_events"].get(decision["event_id"], {})
        obligation = decision.get("obligation_id") or ""
        if event.get("group") != entitlement["group"] or decision["evidence_class"] != "formal_advance":
            continue
        if _checked_fact_matches(state, obligation, event.get("artifacts", [])) and reaches_via_checked(state, obligation, state["root_obligation"]):
            return True
    return False


def issue_entitlement(state: dict[str, Any], event_id: str, tier: str) -> dict[str, Any] | None:
    """One continuation entitlement per root, equivalence group, and authority tier."""
    if tier not in AUTHORITY_TIERS:
        raise FrontierRefusal("unknown_authority_tier")
    event = state["evidence_events"].get(event_id)
    if event is None:
        raise FrontierRefusal("unknown_evidence_event")
    if event.get("distinctness") == "unresolved":
        return None
    existing = _live_entitlement(state, event["group"], tier)
    if existing is not None:
        return existing
    record = {
        "entitlement_id": new_id("entitlement"),
        "group": event["group"],
        "tier": tier,
        "event_id": event_id,
        "spent": False,
        "generation": 1,
        "permit_id": None,
        "status": "live",
        "over_credit": False,
    }
    state["entitlements"][record["entitlement_id"]] = record
    return record


def _invalidate_permit(state: dict[str, Any], permit_id: str | None) -> None:
    if not permit_id or permit_id not in state["permits"]:
        return
    permit = state["permits"][permit_id]
    if permit["status"] == "spent":
        return
    permit["status"] = "invalidated"
    claim_id = permit.get("claim_id")
    claim = state["claims"].get(claim_id or "")
    if claim is not None and claim["status"] == "held" and claim["generation"] == permit["generation"]:
        claim["status"] = "released"


def merge_groups(state: dict[str, Any], event_a: str, event_b: str, tier: str) -> None:
    """Union credit groups. Spent cost stays; unused duplicates are invalidated."""
    if tier not in AUTHORITY_TIERS:
        raise FrontierRefusal("unknown_authority_tier")
    first = state["evidence_events"][event_a]
    second = state["evidence_events"][event_b]
    survivor = min(first["group"], second["group"])
    groups = {first["group"], second["group"]}
    for event in state["evidence_events"].values():
        if event["group"] in groups:
            event["group"] = survivor
    for item in state["entitlements"].values():
        if item["group"] in groups:
            item["group"] = survivor
    for tier_name in AUTHORITY_TIERS:
        matching = [
            item for item in state["entitlements"].values()
            if item["tier"] == tier_name and item["group"] == survivor and item["status"] == "live"
        ]
        spent = [item for item in matching if item["spent"]]
        unspent = [item for item in matching if not item["spent"]]
        if len(spent) >= 2:
            for item in spent:
                item["over_credit"] = True
        keeper = spent[0] if spent else (unspent[0] if unspent else None)
        for item in matching:
            if keeper is not None and item is not keeper:
                if not item["spent"]:
                    _invalidate_permit(state, item.get("permit_id"))
                    item["status"] = "invalidated"
                else:
                    item["over_credit"] = True
                    item["status"] = "merged_spent"


def _operation_lineage(state: dict[str, Any], approach: dict[str, Any]) -> str:
    """Retries of one operation share one lineage, even before its first admission."""
    lineage = approach.get("operation_lineage")
    if not isinstance(lineage, str) or not lineage:
        from .retry import _budget

        lineage = new_id("lineage-op")
        approach["operation_lineage"] = lineage
        _budget(state, lineage)
    return lineage


def issue_permit(
    state: dict[str, Any],
    *,
    kind: str,
    approach_id: str,
    question_id: str,
    question_revision: int,
    route_revision: int,
    operation: str,
    expires_at: float,
    entitlement_id: str | None = None,
    lineage_id: str | None = None,
    ceiling: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if kind not in PERMIT_KINDS:
        raise FrontierRefusal("unknown_permit_kind")
    approach = _approach(state, approach_id)
    generation = 1
    if entitlement_id is not None:
        entitlement = state["entitlements"].get(entitlement_id)
        if entitlement is None or entitlement["status"] != "live":
            raise FrontierRefusal("unknown_entitlement")
        if entitlement["spent"]:
            raise FrontierRefusal("entitlement_spent")
        if entitlement.get("permit_id"):
            current = state["permits"].get(entitlement["permit_id"])
            if current and current["generation"] == entitlement["generation"] and current["status"] in {"usable", "claimed"}:
                return current
        generation = entitlement["generation"]
    elif kind == "initial_exploration":
        lineage = lineage_id or approach["lineage_id"]
        flags = state["lineage_flags"].setdefault(lineage, {"initial_issued": False})
        if flags["initial_issued"]:
            raise FrontierRefusal("initial_permit_already_issued")
        flags["initial_issued"] = True
    permit = {
        "permit_id": new_id("permit"),
        "kind": kind,
        "approach_id": approach_id,
        "question_id": question_id,
        "question_revision": question_revision,
        "route_revision": route_revision,
        "route_id": approach["route_id"],
        "operation": operation,
        "ceiling": dict(ceiling or {}),
        "expires_at": expires_at,
        "status": "usable",
        "generation": generation,
        "entitlement_id": entitlement_id,
        "claim_id": None,
        "lineage_id": lineage_id or approach["lineage_id"],
        "operation_lineage": _operation_lineage(state, approach) if kind == "operational_retry" else None,
        "provenance_entitlement": entitlement_id,
    }
    state["permits"][permit["permit_id"]] = permit
    if entitlement_id is not None:
        state["entitlements"][entitlement_id]["permit_id"] = permit["permit_id"]
    if kind in {"formal_followthrough", "research_followthrough"}:
        approach["unconsumed_followthrough"] = True
    return permit


def claim_permit(
    state: dict[str, Any],
    permit_id: str,
    *,
    owner: str,
    now: float,
    lease_seconds: float,
) -> dict[str, Any]:
    """Exclusive preparation. This does not admit work or spend credit."""
    permit = _permit(state, permit_id)
    if permit["status"] == "claimed" and permit.get("claim_id"):
        claim = state["claims"][permit["claim_id"]]
        if claim["status"] == "held" and claim["owner"] == owner and now < claim["expires_at"]:
            return claim
        raise FrontierRefusal("permit_claimed_by_other")
    if permit["status"] != "usable":
        raise FrontierRefusal("permit_not_usable")
    if now >= permit["expires_at"]:
        raise FrontierRefusal("permit_expired")
    claim = {
        "claim_id": new_id("claim"),
        "permit_id": permit_id,
        "generation": permit["generation"],
        "owner": owner,
        "status": "held",
        "expires_at": now + lease_seconds,
    }
    permit["status"] = "claimed"
    permit["claim_id"] = claim["claim_id"]
    state["claims"][claim["claim_id"]] = claim
    return claim


def release_claim(state: dict[str, Any], claim_id: str, *, now: float | None = None) -> None:
    claim = state["claims"].get(claim_id)
    if claim is None or claim["status"] != "held":
        return
    if now is not None and now < claim["expires_at"]:
        return
    claim["status"] = "released"
    permit = state["permits"].get(claim["permit_id"])
    if permit and permit["status"] == "claimed" and permit.get("claim_id") == claim_id:
        if permit["generation"] == claim["generation"]:
            permit["status"] = "usable"
            permit["claim_id"] = None


def expire_claims(state: dict[str, Any], now: float) -> int:
    released = 0
    for claim in list(state["claims"].values()):
        if claim["status"] == "held" and now >= claim["expires_at"]:
            release_claim(state, claim["claim_id"], now=now)
            released += 1
    return released


def replace_stale_permit(
    state: dict[str, Any],
    permit_id: str,
    *,
    now: float,
    still_relevant: bool,
    expires_at: float,
) -> dict[str, Any] | None:
    """Replace one unused generation. Spent credit is not restored."""
    permit = _permit(state, permit_id)
    entitlement = None
    if permit.get("entitlement_id"):
        entitlement = state["entitlements"][permit["entitlement_id"]]
        if entitlement["spent"] or permit["status"] == "spent":
            raise FrontierRefusal("spent_entitlement_cannot_be_restored")
        if entitlement.get("status") == "invalidated":
            raise FrontierRefusal("invalidated_entitlement_cannot_be_replaced")
        if entitlement["tier"] == "formal_checked" and not _formal_entitlement_current(state, entitlement):
            raise FrontierRefusal("formal_authority_revoked")
        event = state["evidence_events"].get(entitlement.get("event_id") or "")
        if event and event.get("distinctness") == "unresolved":
            raise FrontierRefusal("distinctness_unresolved")
    elif permit["status"] == "spent":
        raise FrontierRefusal("spent_permit_cannot_be_replaced")
    stale = permit["status"] in {"invalidated", "usable", "claimed"} and (
        now >= permit["expires_at"] or permit.get("stale") or permit["status"] == "invalidated"
    )
    if not stale and not permit.get("stale"):
        raise FrontierRefusal("permit_still_current")
    _invalidate_permit(state, permit_id)
    if not still_relevant:
        return None
    generation = permit["generation"] + 1
    if entitlement is not None:
        entitlement["generation"] = generation
    approach = _approach(state, permit["approach_id"])
    question = state["questions"][approach["question_id"]]
    route = state["routes"][approach["route_id"]]
    replacement = {
        **permit,
        "permit_id": new_id("permit"),
        "generation": generation,
        "status": "usable",
        "claim_id": None,
        "expires_at": expires_at,
        "stale": False,
        "question_id": question["question_id"],
        "question_revision": question["revision"],
        "route_revision": route["revision"],
        "route_id": route["route_id"],
    }
    state["permits"][replacement["permit_id"]] = replacement
    if entitlement is not None:
        entitlement["permit_id"] = replacement["permit_id"]
    return replacement


def mark_permits_stale(state: dict[str, Any], approach_id: str) -> None:
    for permit in state["permits"].values():
        if permit["approach_id"] == approach_id and permit["status"] in {"usable", "claimed"}:
            permit["stale"] = True


def consume_permit(
    state: dict[str, Any],
    permit_id: str,
    *,
    now: float,
    approach_id: str,
    question_revision: int,
    route_revision: int,
    provider: bool,
    owner: str | None = None,
) -> dict[str, Any]:
    """First real admission. Rolls back with the surrounding ledger transaction."""
    permit = _permit(state, permit_id)
    if permit["status"] != "claimed":
        raise FrontierRefusal("permit_not_prepared")
    if permit["approach_id"] != approach_id:
        raise FrontierRefusal("permit_approach_mismatch")
    if permit.get("stale"):
        raise FrontierRefusal("stale_permit_basis")
    approach = _approach(state, approach_id)
    if permit["question_id"] != approach["question_id"] or permit.get("route_id") != approach["route_id"]:
        raise FrontierRefusal("stale_permit_basis")
    if permit["question_revision"] != question_revision or permit["route_revision"] != route_revision:
        raise FrontierRefusal("stale_permit_basis")
    if now >= permit["expires_at"]:
        raise FrontierRefusal("permit_expired")
    if permit.get("entitlement_id"):
        entitlement = state["entitlements"].get(permit["entitlement_id"])
        if entitlement and entitlement.get("status") == "invalidated":
            raise FrontierRefusal("entitlement_invalidated")
        if entitlement and entitlement["tier"] == "formal_checked" and not _formal_entitlement_current(state, entitlement):
            raise FrontierRefusal("formal_authority_revoked")
        event = state["evidence_events"].get((entitlement or {}).get("event_id", ""))
        if event and event.get("distinctness") == "unresolved":
            raise FrontierRefusal("distinctness_unresolved")
    claim = state["claims"].get(permit.get("claim_id") or "")
    if claim is None or claim["status"] != "held" or claim["generation"] != permit["generation"]:
        raise FrontierRefusal("missing_preparation_claim")
    if owner is not None and claim["owner"] != owner:
        raise FrontierRefusal("permit_claimed_by_other")
    if now >= claim["expires_at"]:
        raise FrontierRefusal("claim_expired")
    if approach["status"] == "held" and permit["kind"] != "review":
        raise FrontierRefusal("approach_held")
    permit["status"] = "spent"
    claim["status"] = "spent"
    if permit["kind"] in {"formal_followthrough", "research_followthrough"} and permit.get("entitlement_id"):
        entitlement = state["entitlements"][permit["entitlement_id"]]
        if entitlement["spent"]:
            raise FrontierRefusal("entitlement_already_spent")
        entitlement["spent"] = True
        approach["unconsumed_followthrough"] = False
    elif permit["kind"] == "operational_retry":
        # Provenance stays on the permit. The evidence entitlement was already spent.
        pass
    approach["status"] = "active"
    approach["admitted_open"] = True
    costs = state["history"]["costs_by_approach"].setdefault(approach_id, {"provider_requests": 0, "tool_admissions": 0})
    if provider:
        state["history"]["provider_requests"] += 1
        costs["provider_requests"] += 1
    else:
        costs["tool_admissions"] += 1
    return permit


def active_permit(state: dict[str, Any], approach_id: str) -> dict[str, Any] | None:
    permits = [
        item for item in state["permits"].values()
        if item["approach_id"] == approach_id and item["status"] in {"usable", "claimed"}
    ]
    if not permits:
        return None
    limit = state["policy"]["max_operation_execution_admissions"]

    def retry_exhausted(item: dict[str, Any]) -> bool:
        if item.get("kind") != "operational_retry":
            return False
        budget = state["retries"].get(item.get("operation_lineage") or "")
        if not budget:
            return False
        return bool(budget.get("paused") or budget.get("execution_admissions", 0) >= limit)

    approach = _approach(state, approach_id)
    question = state["questions"][approach["question_id"]]
    route = state["routes"][approach["route_id"]]
    usable = [item for item in permits if not retry_exhausted(item) and not item.get("stale")
              and item["question_id"] == question["question_id"]
              and item.get("route_id") == route["route_id"]
              and item["question_revision"] == question["revision"]
              and item["route_revision"] == route["revision"]]
    return sorted(usable or permits, key=lambda item: item["permit_id"])[0]


def apply_contribution(
    state: dict[str, Any],
    *,
    approach_id: str,
    obligation_id: str | None,
    proposed_class: str,
    subject: str,
    context: str,
    operation_id: str,
    artifacts: list[str],
    claim: str,
    explanation: str,
    now: float,
    location: str = "",
    distinctness: str = "distinct",
) -> dict[str, Any]:
    """Record the event once and issue at most one matching entitlement."""
    evidence_class = classify_contribution(
        state,
        approach_id=approach_id,
        obligation_id=obligation_id,
        proposed_class=proposed_class,
    )
    if evidence_class == "formal_advance" and not _checked_fact_matches(state, obligation_id or "", artifacts):
        evidence_class = "research_advance"
    fact = state.get("checked_facts", {}).get(obligation_id or "", {})
    if evidence_class == "formal_advance" and fact.get("artifact_id"):
        artifacts = [fact["artifact_id"]]
    if evidence_class == "formal_advance":
        stored_class = "formal_advance"
    elif evidence_class == "research_advance":
        stored_class = "research_advance"
    elif proposed_class == "formal_advance":
        stored_class = "observation_only"
    else:
        stored_class = evidence_class if evidence_class in EVIDENCE_CLASSES else "observation_only"
    event, created = register_event(
        state,
        subject=subject,
        context=context,
        operation_id=operation_id,
        artifacts=artifacts,
        claim=claim,
        evidence_class=stored_class if stored_class in EVIDENCE_CLASSES else "observation_only",
        location=location,
    )
    approach = _approach(state, approach_id)
    root_obligation = state["routes"].get(approach["route_id"], {}).get("root_obligation") or state["root_obligation"] or ""
    certificates = certificates_on_checked_path(state, obligation_id or "", root_obligation)
    if evidence_class == "formal_advance" and fact.get("receipt_digest"):
        certificates.append("fact:" + fact["receipt_digest"])
    if created:
        event["checked_basis"] = certificates
        if distinctness == "unresolved":
            event["distinctness"] = "unresolved"
    else:
        fresh = [item for item in certificates if item not in event.get("checked_basis", [])]
        if distinctness == "unresolved":
            event["distinctness"] = "unresolved"
        if fresh and evidence_class == "formal_advance":
            event["checked_basis"] = certificates
            event["evidence_class"] = "formal_advance"
        elif event["evidence_class"] != "formal_advance" or evidence_class == "formal_advance":
            evidence_class = event["evidence_class"]
        else:
            # Historical verification is retained, but cannot replace a failed
            # current authority check or purchase weaker credit on revocation.
            evidence_class = "observation_only"
    for existing_entitlement in state["entitlements"].values():
        if (existing_entitlement["group"] == event["group"] and existing_entitlement["tier"] == "formal_checked"
                and not existing_entitlement["spent"] and not _formal_entitlement_current(state, existing_entitlement)):
            _invalidate_permit(state, existing_entitlement.get("permit_id"))
    if event.get("distinctness") == "unresolved":
        for permit in state["permits"].values():
            entitlement_id = permit.get("entitlement_id")
            entitlement = state["entitlements"].get(entitlement_id or "")
            if entitlement and entitlement.get("event_id") == event["event_id"] and permit["status"] in {"usable", "claimed"}:
                _invalidate_permit(state, permit["permit_id"])
    if proposed_class == "formal_advance" and obligation_id and _checked_fact_matches(state, obligation_id, artifacts):
        event["formal_certificate"] = True
    entitlement = None
    permit = None
    tier = None
    known_entitlements = set(state["entitlements"])
    if evidence_class == "formal_advance":
        tier = "formal_checked"
    elif evidence_class == "research_advance":
        tier = "research_significance"
    if event.get("distinctness") == "unresolved":
        tier = None
    if tier is not None:
        entitlement = issue_entitlement(state, event["event_id"], tier)
        if entitlement is not None and not entitlement["spent"] and entitlement.get("permit_id"):
            existing_permit = state["permits"][entitlement["permit_id"]]
            if existing_permit["status"] == "invalidated" and tier == "formal_checked" and _formal_entitlement_current(state, entitlement):
                permit = replace_stale_permit(state, existing_permit["permit_id"], now=now, still_relevant=True,
                                              expires_at=now + state["policy"]["permit_lease_seconds"])
        if entitlement is not None and not entitlement["spent"] and entitlement.get("permit_id") is None:
            approach = _approach(state, approach_id)
            question_id = approach["question_id"]
            question = state["questions"][question_id]
            permit = issue_permit(
                state,
                kind="formal_followthrough" if tier == "formal_checked" else "research_followthrough",
                approach_id=approach_id,
                question_id=question_id,
                question_revision=question["revision"],
                route_revision=state["routes"][approach["route_id"]]["revision"],
                operation=approach.get("next_operation") or question["uncertainty"],
                expires_at=now + state["policy"]["permit_lease_seconds"],
                entitlement_id=entitlement["entitlement_id"],
            )
    decision = {
        "decision_id": new_id("decision"),
        "approach_id": approach_id,
        "obligation_id": obligation_id,
        "event_id": event["event_id"],
        "created": created,
        "evidence_class": evidence_class if evidence_class in EVIDENCE_CLASSES else "observation_only",
        "certificate_retained": bool(event.get("formal_certificate")) and evidence_class != "formal_advance",
        "entitlement_id": None if entitlement is None else entitlement["entitlement_id"],
        "permit_id": None if permit is None else permit["permit_id"],
        "explanation": explanation,
        "credit_minted": bool(
            entitlement is not None
            and entitlement["entitlement_id"] not in known_entitlements
            and not entitlement.get("over_credit")
        ),
    }
    state.setdefault("decisions", []).append(decision)
    if decision["credit_minted"] and evidence_class == "formal_advance":
        state["history"]["formal_advances"] += 1
        _approach(state, approach_id)["inconclusive_extensions"] = 0
    elif decision["credit_minted"] and evidence_class == "research_advance":
        state["history"]["research_advances"] += 1
        _approach(state, approach_id)["inconclusive_extensions"] = 0
    if decision["credit_minted"] and approach["status"] == "paused":
        from .approaches import request_readmission

        request_readmission(state, approach_id, now=now)
    if decision["credit_minted"]:
        for provisional in state["permits"].values():
            if (provisional["approach_id"] == approach_id and provisional["kind"] == "inconclusive_extension"
                    and provisional["status"] in {"usable", "claimed"}):
                _invalidate_permit(state, provisional["permit_id"])
    return decision


def settle_mathematical(
    state: dict[str, Any],
    approach_id: str,
    outcome: str,
    *,
    now: float,
    explanation: str,
) -> dict[str, Any]:
    """Attention and eligibility change. Historical cost does not reset."""
    approach = _approach(state, approach_id)
    state["history"]["intervals"].append({
        "approach_id": approach_id,
        "lineage_id": approach["lineage_id"],
        "outcome": outcome,
        "time": now,
        "explanation": explanation,
        "bottleneck": approach.get("bottleneck_obligation"),
    })
    approach["admitted_open"] = False
    approach["latest_result"] = explanation
    if outcome != "operational_failure":
        approach.pop("operation_lineage", None)
    if outcome == "operational_failure":
        state["history"]["operational_failures"] += 1
        question = state["questions"][approach["question_id"]]
        permit = issue_permit(
            state,
            kind="operational_retry",
            approach_id=approach_id,
            question_id=question["question_id"],
            question_revision=question["revision"],
            route_revision=state["routes"][approach["route_id"]]["revision"],
            operation=question["uncertainty"],
            expires_at=now + state["policy"]["permit_lease_seconds"],
        )
        approach["status"] = "runnable"
        return {"eligibility": "retry_within_budget", "permit_id": permit["permit_id"]}
    if outcome == "route_obstruction":
        approach["status"] = "held"
        approach["resume_condition"] = "appeal_or_route_revision"
        if approach_id in state["resident"]:
            state["resident"].remove(approach_id)
        return {"eligibility": "none"}
    if outcome == "inconclusive":
        approach["inconclusive_extensions"] += 1
        allowance = state["policy"]["max_no_progress"]
        if approach["inconclusive_extensions"] <= allowance:
            question = state["questions"][approach["question_id"]]
            permit = issue_permit(
                state,
                kind="inconclusive_extension",
                approach_id=approach_id,
                question_id=question["question_id"],
                question_revision=question["revision"],
                route_revision=state["routes"][approach["route_id"]]["revision"],
                operation=question["uncertainty"],
                expires_at=now + state["policy"]["permit_lease_seconds"],
            )
            approach["status"] = "runnable"
            return {"eligibility": "inconclusive_extension", "permit_id": permit["permit_id"]}
        approach["status"] = "paused"
        approach["resume_condition"] = "changed_investigation"
        if approach_id in state["resident"]:
            state["resident"].remove(approach_id)
        return {"eligibility": "paused"}
    if outcome in {"formal_advance", "research_advance"}:
        approach["status"] = "runnable"
        return {"eligibility": outcome}
    if outcome in {"root_verified", "root_refuted"}:
        approach["status"] = "completed"
        if approach_id in state["resident"]:
            state["resident"].remove(approach_id)
        return {"eligibility": "completed", "result": outcome}
    approach["status"] = "runnable"
    return {"eligibility": "none"}


def restore_unused_after_dismiss(state: dict[str, Any], approach_id: str, *, now: float) -> dict[str, Any] | None:
    """A dismissed hold can revive an unspent stale permit without new credit."""
    approach = _approach(state, approach_id)
    was_held = approach["status"] == "held"
    if approach["status"] == "held":
        approach["status"] = "runnable"
        approach["resume_condition"] = None
    from .approaches import approach_is_held, request_readmission

    if approach_is_held(state, approach_id):
        approach["status"] = "held"
        return None
    restored = None
    for permit in list(state["permits"].values()):
        if permit["approach_id"] != approach_id or permit["status"] == "spent":
            continue
        if permit.get("entitlement_id") and state["entitlements"][permit["entitlement_id"]]["spent"]:
            continue
        if permit.get("stale") or permit["status"] == "invalidated" or now >= permit["expires_at"]:
            restored = replace_stale_permit(
                state,
                permit["permit_id"],
                now=now,
                still_relevant=True,
                expires_at=now + state["policy"]["permit_lease_seconds"],
            )
            break
    if was_held and approach_id not in state["resident"] and active_permit(state, approach_id) is not None:
        request_readmission(state, approach_id, now=now)
    return restored
