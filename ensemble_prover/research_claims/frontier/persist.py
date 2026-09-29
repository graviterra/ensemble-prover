"""Frontier records share the research ledger's writer transaction.

The campaign row is the source of truth. Other rows are an indexed projection
rebuilt in the same transaction. A crash rolls both back together.
"""

from __future__ import annotations

import json
from typing import Any

from ..model import json_text
from ..store import ResearchStoreError, RevisionConflict
from .config import SUPPORTED_PROGRESS_POLICY, SUPPORTED_TOOL_POLICY
from .investigation import default_manifest

CAMPAIGN_KIND = "campaign"


def campaign_id(owner_id: str) -> str:
    return "campaign:" + owner_id


def new_campaign(policy: dict[str, Any], root: dict[str, Any], *, experiments: bool, lean: bool) -> dict[str, Any]:
    if type(policy.get("progress_policy_version")) is not int or policy["progress_policy_version"] != SUPPORTED_PROGRESS_POLICY:
        raise ResearchStoreError("unsupported frontier progress policy version")
    if type(policy.get("tool_policy_version")) is not int or policy["tool_policy_version"] != SUPPORTED_TOOL_POLICY:
        raise ResearchStoreError("unsupported frontier tool policy version")
    return {
        "schema": 1,
        "revision": 0,
        "policy": policy,
        "root": root,
        "root_obligation": None,
        "routes": {},
        "obligations": {},
        "reductions": {},
        "approaches": {},
        "questions": {},
        "evidence_events": {},
        "entitlements": {},
        "permits": {},
        "claims": {},
        "lineage_flags": {},
        "scoped_holds": [],
        "service_queue": [],
        "admission_queue": [],
        "resident": [],
        "last_served": None,
        "consecutive": {},
        "admission_sequence": 0,
        "phase": {
            "reviews_since_work": 0,
            "frozen_receipts": [],
            "acknowledged": [],
            "pending_review": [],
            "open": True,
            "tails": {},
        },
        "history": {
            "intervals": [],
            "formal_advances": 0,
            "research_advances": 0,
            "operational_failures": 0,
            "provider_requests": 0,
            "deferred_dispatches": 0,
            "costs_by_approach": {},
        },
        "retries": {},
        "lanes": {},
        "operations": {},
        "observations": {},
        "source_applications": {},
        "experiments": {},
        "hypotheticals": [],
        "decisions": [],
        "manifest": default_manifest(experiments=experiments, lean=lean),
        "review_authorizations": {},
    }


def _check_versions(state: dict[str, Any]) -> None:
    if not isinstance(state, dict) or type(state.get("schema")) is not int or state["schema"] != 1:
        raise ResearchStoreError("unsupported frontier campaign schema")
    policy = state.get("policy")
    if not isinstance(policy, dict):
        raise ResearchStoreError("missing frontier campaign policy")
    if type(policy.get("progress_policy_version")) is not int or policy["progress_policy_version"] != SUPPORTED_PROGRESS_POLICY:
        raise ResearchStoreError("refusing to reinterpret frontier progress policy")
    if type(policy.get("tool_policy_version")) is not int or policy["tool_policy_version"] != SUPPORTED_TOOL_POLICY:
        raise ResearchStoreError("refusing to reinterpret frontier tool policy")
    if type(state.get("revision")) is not int or state["revision"] < 0:
        raise ResearchStoreError("invalid frontier campaign revision")


def load_campaign(store: Any, owner_id: str) -> dict[str, Any] | None:
    row = store._connection.execute(
        "SELECT revision, record FROM frontier_records WHERE record_id = ?",
        (campaign_id(owner_id),),
    ).fetchone()
    if row is None:
        return None
    state = json.loads(row["record"])
    _check_versions(state)
    if type(row["revision"]) is not int or state["revision"] != row["revision"]:
        raise ResearchStoreError("frontier campaign revision diverged from its row")
    return state


def _projection_rows(state: dict[str, Any], owner_id: str, target_id: str) -> list[tuple[str, str, str, int, str]]:
    rows: list[tuple[str, str, str, int, str]] = []

    def add(kind: str, record_id: str, status: str, revision: int, record: dict[str, Any]) -> None:
        rows.append((record_id, kind, status, revision, json_text(record)))

    for approach in state["approaches"].values():
        add("approach", approach["approach_id"], approach["status"], approach["status_revision"], {
            "approach_id": approach["approach_id"],
            "route_id": approach["route_id"],
            "question_id": approach["question_id"],
            "status": approach["status"],
            "fingerprint": approach["fingerprint"],
        })
    for route in state["routes"].values():
        add("route", route["route_id"], route["viability"], route["revision"], route)
    for question in state["questions"].values():
        add("question", question["question_id"], "open", question["revision"], {
            "question_id": question["question_id"],
            "approach_id": question["approach_id"],
            "revision": question["revision"],
        })
    for decision in state["decisions"]:
        add("contribution", decision["decision_id"], decision["evidence_class"], 1, decision)
    for operation_id, operation in state["operations"].items():
        add("operation", operation_id, "admitted", int(operation["epoch"]), operation)
    return rows


def save_campaign(store: Any, owner_id: str, target_id: str, state: dict[str, Any]) -> None:
    _check_versions(state)
    expected = int(state["revision"])
    state["revision"] = expected + 1
    payload = json_text(state)
    record_id = campaign_id(owner_id)
    if expected == 0:
        store._connection.execute(
            "INSERT INTO frontier_records(record_id, kind, owner_id, target_id, status, revision, record) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (record_id, CAMPAIGN_KIND, owner_id, target_id, "active", state["revision"], payload),
        )
    else:
        cursor = store._connection.execute(
            "UPDATE frontier_records SET revision = ?, record = ? "
            "WHERE record_id = ? AND revision = ? AND kind = ?",
            (state["revision"], payload, record_id, expected, CAMPAIGN_KIND),
        )
        if cursor.rowcount != 1:
            state["revision"] = expected
            raise RevisionConflict("frontier campaign changed; reread it")
    store._connection.execute(
        "DELETE FROM frontier_records WHERE owner_id = ? AND kind != ?",
        (owner_id, CAMPAIGN_KIND),
    )
    for record_id, kind, status, revision, record in _projection_rows(state, owner_id, target_id):
        store._connection.execute(
            "INSERT INTO frontier_records(record_id, kind, owner_id, target_id, status, revision, record) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (record_id, kind, owner_id, target_id, status, revision, record),
        )


def install_campaign(store: Any, strategy_state: dict[str, Any], run: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    claim = store.get_claim(run["target_id"])
    environment = ""
    closed = run.get("closed_loop")
    if isinstance(closed, dict):
        environment = str((closed.get("environment") or {}).get("id", ""))
    # The source question can be prose or use context-sensitive notation. Once
    # the strategy owner has validated an original Lean capture, its elaborated
    # statement and exact pinned context are the formal target identity.
    pin = strategy_state.get("original_lean")
    if not isinstance(pin, dict):
        pin = None
    root = {
        "target_id": run["target_id"],
        "binding": strategy_state["root_binding"],
        "proposition": pin["statement"] if pin else claim["spec"]["contract"]["statement"],
        "context": pin["pin_source"] if pin else "",
        "environment": pin["environment_id"] if pin else environment,
        "formal_binding": pin["binding"] if pin else None,
        "alignment": "formal_target" if pin else "source_question",
    }
    state = new_campaign(
        policy,
        root,
        experiments=bool(run.get("experiments")),
        lean=bool(closed),
    )
    save_campaign(store, strategy_state["owner_id"], run["target_id"], state)
    run["frontier_schema"] = 8
    return state
