"""Read-only adoption of stopped Mini artifacts into a new research ledger."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from .model import json_text


def _read(path: Path, limit: int = 32 * 1024 * 1024) -> bytes:
    if path.stat().st_size > limit:
        raise ValueError("Mini adoption artifact exceeds 32 MiB")
    with path.open("rb") as handle:
        result = handle.read(limit + 1)
    if len(result) > limit:
        raise ValueError("Mini adoption artifact exceeds 32 MiB")
    return result


def _statements(value: Any) -> set[str]:
    statements: set[str] = set()
    frontier = [value]
    while frontier:
        value = frontier.pop()
        if isinstance(value, dict):
            frontier.extend(value.values())
            for key in ("root_statement", "statement", "goal_statement"):
                if isinstance(value.get(key), str) and value[key].strip():
                    statements.add(value[key])
        elif isinstance(value, list):
            if (
                len(value) == 2
                and isinstance(value[0], str)
                and value[0] in {"root_statement", "statement", "goal_statement"}
                and isinstance(value[1], str)
            ):
                if value[1].strip():
                    statements.add(value[1])
            else:
                frontier.extend(value)
    return statements


def _unknown_context(checkpoint: str, session_id: str) -> str:
    return "Unavailable Mini formal context; provenance: " + json_text(
        {"checkpoint_sha256": checkpoint, "session_id": session_id}
    )


def _saved_contracts(snapshot: dict[str, Any], checkpoint: str) -> list[dict[str, Any]]:
    """Keep context provenance local to the session that actually saved it."""
    contracts: dict[tuple[str, str], dict[str, Any]] = {}
    sessions = snapshot.get("sessions", {})
    if not isinstance(sessions, dict):
        raise ValueError("Mini sessions must be an object")
    for session_id, session in sessions.items():
        if not isinstance(session, dict):
            raise ValueError("Mini session must be an object")
        conv = session.get("conversation", {})
        if not isinstance(conv, dict):
            raise ValueError("Mini conversation must be an object")
        if isinstance(conv.get("items"), list):
            items = conv["items"]
            if any(
                not isinstance(item, list) or len(item) != 2 or not isinstance(item[0], str)
                for item in items
            ):
                raise ValueError("Mini conversation items must be key/value pairs")
            conv = dict(items)
        for statement in _statements(session):
            context = conv.get("lean_preamble") if conv.get("goal_statement") == statement else None
            context = context if isinstance(context, str) else None
            # An absent context is not the empty Lean preamble, and two absent
            # contexts provide no evidence of equality across saved sessions.
            formal_context = context if context is not None else _unknown_context(checkpoint, session_id)
            contract = contracts.setdefault(
                (statement, formal_context),
                {
                    "statement": statement,
                    "formal_context": formal_context,
                    "context_coverage": "saved_conversation" if context is not None else "unknown",
                    "session_ids": [],
                },
            )
            contract["session_ids"].append(session_id)
            if len(contracts) > 1024:
                raise ValueError("Mini adoption has more than 1024 distinct contracts")
    return sorted(contracts.values(), key=lambda item: (item["statement"], item["formal_context"]))


def read_mini_run(directory: Path) -> dict[str, Any]:
    from ..theorem_project import TheoremProjectRequest, resolve_theorem_project

    directory = directory.resolve(strict=True)
    metadata_bytes = _read(directory / "attempt_checkpoint.json")
    metadata = json.loads(metadata_bytes)
    identity = metadata["identity"]
    original = identity["input"]
    source = Path(original["source_path"]).resolve(strict=True)
    source_bytes = _read(source)
    if hashlib.sha256(source_bytes).hexdigest() != original["source_sha256"]:
        raise ValueError("original Mini source changed; adoption refused")
    head = metadata["head"]
    checkpoint = Path(head["snapshot_path"]).resolve(strict=True)
    if not checkpoint.is_relative_to(directory):
        raise ValueError("Mini checkpoint escapes the selected run")
    data = _read(checkpoint)
    if hashlib.sha256(data).hexdigest() != head["snapshot_hash"]:
        raise ValueError("Mini checkpoint hash changed")
    config = identity["cli_config"]
    problem = resolve_theorem_project(
        TheoremProjectRequest(
            source,
            original["theorem_name"],
            Path(config["lean_project_dir"]),
            imports=tuple(config.get("theorem_project_imports") or ()),
            source_dirs=tuple(
                Path(path) for path in (config.get("theorem_project_source_dirs") or ())
            ),
        )
    )
    snapshot = json.loads(data)  # Data only: never deserialize checkpoint objects.
    expanded_checkpoint = None
    if snapshot.get("schema_version") == 2:
        from ..mini_session.attempt_checkpoint import (
            AttemptCheckpointRegistry, expand_completed_children,
        )

        manifest = AttemptCheckpointRegistry._load_manifest(directory)
        if manifest != metadata:
            raise ValueError("Mini checkpoint metadata changed during adoption")
        snapshot = expand_completed_children(snapshot, Path(manifest["registry_root"]))
        expanded_checkpoint = json_text(snapshot).encode()
    contracts = _saved_contracts(snapshot, head["snapshot_hash"])
    statements = {contract["statement"] for contract in contracts}
    # Retain the old convenience fields only where their statement-only key is
    # unambiguous. New imports consume complete context-sensitive contracts.
    contexts = {
        statement: matching[0]["formal_context"]
        for statement in statements
        if len(matching := [item for item in contracts if item["statement"] == statement]) == 1
        and matching[0]["context_coverage"] == "saved_conversation"
    }
    result = {
        "directory": str(directory),
        "problem": problem,
        "metadata": metadata_bytes,
        "checkpoint": data,
        "statements": sorted(statements),
        "contexts": contexts,
        "contracts": contracts,
        "previous_accounting": snapshot.get("cost_ledger", {}),
        "elapsed_s": snapshot.get("recorder", {}).get("elapsed_s"),
    }
    if expanded_checkpoint is not None:
        result["expanded_checkpoint"] = expanded_checkpoint
    return result


def import_artifacts(store: Any, adoption: dict[str, Any]) -> None:
    from .strategy import StrategyController

    controller = StrategyController(store)
    with store.atomic():
        metadata = store.put_artifact(
            adoption["metadata"], name="original-mini-checkpoint-metadata.json"
        )
        checkpoint = store.put_artifact(
            adoption["checkpoint"], name="original-mini-checkpoint.json"
        )
        expanded_checkpoint = None
        if "expanded_checkpoint" in adoption:
            expanded_checkpoint = store.put_artifact(
                adoption["expanded_checkpoint"], name="expanded-mini-checkpoint.json"
            )
        inspection_checkpoint = expanded_checkpoint or checkpoint
        inventory = []
        contracts = adoption.get("contracts")
        if contracts is None:
            contracts = [
                {
                    "statement": statement,
                    "formal_context": adoption.get("contexts", {}).get(statement, _unknown_context(checkpoint, "legacy-unavailable")),
                    "context_coverage": "saved_conversation" if statement in adoption.get("contexts", {}) else "unknown",
                    "session_ids": [],
                }
                for statement in adoption["statements"]
            ]
        for contract in contracts:
            subject = controller.register_subject(
                contract["statement"],
                parent_id=controller.root_id,
                formal_context=contract["formal_context"],
            )
            contract_artifact = store.put_artifact(
                json_text(
                    {
                        "subject": subject,
                        "context_coverage": contract["context_coverage"],
                        "session_ids": contract["session_ids"],
                        "checkpoint_artifact": checkpoint,
                        **({"expanded_checkpoint_artifact": expanded_checkpoint}
                           if expanded_checkpoint else {}),
                    }
                ).encode(),
                name="adopted-contract.json",
            )
            with controller._edit() as (state, _):
                state["subjects"][subject["subject_id"]]["adoption_artifact"] = (
                    contract_artifact
                )
            inventory.append(subject["subject_id"])
        record = {
            "directory": adoption["directory"],
            "metadata_artifact": metadata,
            "checkpoint_artifact": checkpoint,
            "subjects": inventory,
            "elapsed_s": adoption["elapsed_s"],
            "previous_accounting_artifact": store.put_artifact(
                json_text(adoption["previous_accounting"]).encode(),
                name="previous-mini-accounting.json",
            ),
            "mode": "new_research_with_revalidated_artifacts",
            "kernel_verified": False,
        }
        if expanded_checkpoint:
            record["expanded_checkpoint_artifact"] = expanded_checkpoint
        record["inventory_artifact"] = store.put_artifact(
            json_text(record).encode(), name="adoption-inventory.json"
        )
        run = store.run_record()
        run["adopted_mini_run"] = record
        store.save_run(run)
        job = store.jobs()[0]
        job["question"] = (
            "First audit the imported attempt's strategy and exact bottlenecks. Read its saved evidence and search for known obstructions. "
            "Then execute a promising route toward the pinned original root. Prior helper claims and proof text are candidates requiring fresh checking. "
            "Do not replay the stopped scheduler or read its entire checkpoint sequentially. "
            "Start with the named problem/source documents; use lookup_strategy_subject to locate an exact bottleneck. "
            f"There are {len(inventory)} imported contracts. Complete adoption inventory artifact: "
            + record["inventory_artifact"]
            + ". Checkpoint artifact for targeted inspection: " + inspection_checkpoint
        )
        store.save_job(job)
