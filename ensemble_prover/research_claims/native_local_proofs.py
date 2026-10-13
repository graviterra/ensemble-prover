"""Durable local proof requests owned by the existing Mini proof scheduler.

A request is an unproved proposition, not an extra hypothesis or a root route.
Its mathematical contract describes intent; only the exact Lean proposition is
certified by the ordinary graph/helper verification path.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict
import hashlib
import sqlite3
from typing import Any

from .model import INTERNAL_JSON_NESTING, MathematicalContract, json_text, load_json, text


def _digest(value: Any) -> str:
    return hashlib.sha256(json_text(value).encode()).hexdigest()


def _task_identity(request: dict[str, Any]) -> str:
    origin = request["origin"]
    fields = ("job_id", "claim_id", "revision", "context_binding")
    if request.get("schema", 1) == 1:
        fields += ("context_artifact",)
    return "local-proof-" + _digest({
        "lean_statement": request["lean_statement"],
        "origin": {key: origin[key] for key in fields},
    })


def _task_scope(request: dict[str, Any]) -> str:
    return _task_identity({**request, "schema": 2})


def record_dispatch_context(owner: Any, session: Any, job_id: str, run: dict[str, Any]) -> None:
    """Freeze the host's context, never a preamble supplied by research text."""
    binding = owner._target_context_binding(session.conv)
    if binding != run.get("native_job_contexts", {}).get(job_id):
        return
    context = {
        "binding": binding, "target_statement": owner._target(session.conv),
        "model_preamble": str(getattr(session.conv, "preamble", owner.pin["preamble"])),
        # Checker-only definitions can contain an intentionally hidden answer.
        # The proof checkpoint retains their text; research receives only its
        # exact identity, alongside the authorized model-facing context.
        "checker_preamble_sha256": hashlib.sha256(str(getattr(
            session.conv, "lean_preamble", getattr(owner.problem, "lean_preamble", owner.pin["preamble"]),
        )).encode()).hexdigest(),
        "statement_environment": (session.dossier.statement_environment_metadata()
                                  if callable(getattr(session.dossier, "statement_environment_metadata", None)) else {}),
    }
    artifact = owner.store.put_artifact(json_text(context).encode(), name="native-local-proof-context.json")
    run.setdefault("native_job_formal_contexts", {})[job_id] = artifact


def request_local_proof(store: Any, job: dict[str, Any], action: dict[str, Any]) -> dict[str, Any]:
    statement = text(action["lean_statement"], "closed Lean statement").strip()
    plan = text(action["proof_plan"], "local proof plan")
    contract = asdict(MathematicalContract.from_dict(action["contract"]))
    run = store.run_record()
    context_id = run.get("native_job_formal_contexts", {}).get(job["job_id"])
    if not context_id:
        raise ValueError("local proof request requires its dispatched formal context")
    context = _validated_context(store, context_id)
    binding = run.get("native_job_contexts", {}).get(job["job_id"])
    if not binding or context["binding"] != binding:
        raise ValueError("local proof request has a stale dispatched context")
    origin = {
        "job_id": job["job_id"], "claim_id": job["claim_id"], "revision": job["revision"],
        "claim": store.get_claim(job["claim_id"]), "approach_id": job.get("frontier_approach_id"),
        "context_binding": binding, "context_artifact": context_id,
        "proof_checkpoint": job.get("native_proof_checkpoint"),
    }
    request = {"schema": 2, "lean_statement": statement, "contract": contract,
               "proof_plan": plan, "origin": origin}
    # Different hints about the same exact proposition retain its existing
    # attempts and quota. Return address and formal context remain immutable.
    task_id = _task_identity(request)
    tasks = run.setdefault("native_local_proof_tasks", {})
    # Older ledgers included the dispatch environment in the identifier. Keep
    # that identifier and its immutable request when continuing the same task.
    if task_id not in tasks:
        for candidate_id, candidate in tasks.items():
            try:
                previous, _ = _validated_request(store, candidate)
            except (ValueError, KeyError, TypeError, OSError):
                continue
            if _task_scope(previous) == task_id:
                task_id = candidate_id
                break
    if task_id in tasks:
        _validated_request(store, tasks[task_id])
        if tasks[task_id]["status"] == "invalid_request":
            raise ValueError("stored local proof request is invalid")
    artifact = store.put_artifact(json_text(request).encode(), name="native-local-proof-request.json")
    if task_id not in tasks:
        tasks[task_id] = {"task_id": task_id, "request": request, "request_artifact": artifact,
                          "status": "queued", "node_id": None, "result_artifact": None,
                          "followup_request_artifacts": []}
        store.save_run(run)
    elif (artifact != tasks[task_id]["request_artifact"]
          and artifact not in tasks[task_id]["followup_request_artifacts"]):
        tasks[task_id]["followup_request_artifacts"].append(artifact)
        store.save_run(run)
    job.setdefault("native_local_proof_task_ids", [])
    if task_id not in job["native_local_proof_task_ids"]:
        job["native_local_proof_task_ids"].append(task_id)
    if not tasks[task_id]["result_artifact"]:
        job["status"] = "waiting"
    elif tasks[task_id]["status"] != "proved":
        # Re-reading an unchanged result must not wait for a second delivery.
        job["status"] = "pending"
    store.save_job(job)
    return {"task_id": task_id, "request_artifact": tasks[task_id]["request_artifact"],
            "result_artifact": tasks[task_id]["result_artifact"],
            "status": tasks[task_id]["status"], "kernel_verified": False,
            "instruction": "The existing proof scheduler owns this local task. Its result returns here; no new proof budget was created."}


def _validated_context(store: Any, artifact: str) -> dict[str, Any]:
    context = load_json(store.read_artifact(artifact).decode(), max_depth=INTERNAL_JSON_NESTING)
    if (not isinstance(context, dict)
            or not isinstance(context.get("statement_environment"), dict)
            or not all(isinstance(context.get(field), str) for field in (
                "target_statement", "model_preamble", "checker_preamble_sha256", "binding"))):
        raise ValueError("invalid local proof context record")
    from ..mini_research import _hash
    from ..proof_dossier import canonical_dossier_statement_key

    binding = _hash({
        "statement": canonical_dossier_statement_key(context["target_statement"]),
        "model_preamble_sha256": hashlib.sha256(context["model_preamble"].encode()).hexdigest(),
        "checker_preamble_sha256": context["checker_preamble_sha256"],
    })
    if binding != context["binding"]:
        raise ValueError("local proof context identity changed")
    return context


def _validated_request(store: Any, task: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    if (not isinstance(task, dict) or not isinstance(task.get("request"), dict)
            or not isinstance(task.get("followup_request_artifacts"), list)
            or not all(isinstance(item, str) for item in task["followup_request_artifacts"])
            or not isinstance(task.get("request_artifact"), str)
            or not isinstance(task.get("status"), str)
            or "node_id" not in task or "result_artifact" not in task
            or task["node_id"] is not None and not isinstance(task["node_id"], str)
            or task["result_artifact"] is not None and not isinstance(task["result_artifact"], str)):
        raise ValueError("invalid local proof task record")
    request = load_json(store.read_artifact(task["request_artifact"]).decode(), max_depth=INTERNAL_JSON_NESTING)
    if (not isinstance(request, dict) or request.get("schema") not in {1, 2}
            or not isinstance(request.get("origin"), dict) or request != task["request"]
            or task["task_id"] != _task_identity(request)):
        raise ValueError("local proof request identity changed")
    origin = request["origin"]
    context = _validated_context(store, origin["context_artifact"])
    if context["binding"] != origin["context_binding"]:
        raise ValueError("local proof context identity changed")
    job = store.job(origin["job_id"])
    if (job["claim_id"] != origin["claim_id"] or job["revision"] != origin["revision"]
            or task["task_id"] not in job.get("native_local_proof_task_ids", [])):
        raise ValueError("local proof return address changed")
    return request, context


def _validated_hints(store: Any, task: dict[str, Any], request: dict[str, Any]) -> list[dict[str, Any]]:
    hints = []
    for artifact in task["followup_request_artifacts"]:
        followup = load_json(store.read_artifact(artifact).decode(), max_depth=INTERNAL_JSON_NESTING)
        if (not isinstance(followup, dict) or not isinstance(followup.get("origin"), dict)
                or _task_scope(followup) != _task_scope(request)):
            raise ValueError("local proof hint changed its task")
        hints.append({"request_artifact": artifact,
                      "proof_plan": text(followup["proof_plan"], "local proof plan"),
                      "authority": "unproved_candidate_guidance"})
    return hints


def _context_matches(owner: Any, session: Any, request: dict[str, Any], context: dict[str, Any]) -> bool:
    return (owner._target_context_binding(session.conv) == request["origin"]["context_binding"]
            and str(getattr(session.dossier, "current_lean_environment_hash", "") or "")
            == str(context["statement_environment"].get("statement_environment_hash") or ""))


def work_item_context_matches(session: Any, item: Any) -> bool:
    """Fence task dispatch using its ledger receipt, including saved selections."""
    record = item if isinstance(item, dict) else getattr(item, "graph_record", {}) or {}
    node_id = record.get("obligation_id") or record.get("node_id") or getattr(item, "node_id", "")
    graph = getattr(getattr(session, "dossier", None), "proof_graph", None)
    node = graph.nodes.get(node_id) if graph is not None else None
    if getattr(node, "kind", "") == "replan_queue_item":
        node = graph.nodes.get(graph._replan_queue_item_obligation_id(node))
    task_id = (getattr(node, "metadata", {}) or {}).get("native_local_proof_task_id")
    if not task_id:
        return True
    owner = getattr(session, "_native_local_proof_owner", None)
    if owner is None or not owner.active or owner.store is None:
        return False
    try:
        task = owner.store.run_record()["native_local_proof_tasks"][task_id]
        if task["status"] == "invalid_request":
            return False
        request, context = _validated_request(owner.store, task)
        return (task["node_id"] == node.node_id and node.statement == request["lean_statement"]
                and node.metadata.get("native_local_proof_request_artifact") == task["request_artifact"]
                and _context_matches(owner, session, request, context))
    except (ValueError, KeyError, TypeError, OSError, sqlite3.Error):
        return False


def _checked_result(session: Any, node: Any, request: dict[str, Any], context: dict[str, Any]) -> dict[str, Any] | None:
    if (node.status != "proved" or node.statement != request["lean_statement"]
            or node.metadata.get("statement_environment_hash", "")
            != context["statement_environment"].get("statement_environment_hash", "")):
        return None
    dossier = session.dossier
    graph = dossier.proof_graph
    helper_node = graph._proved_helper_for_statement(
        node.statement, require_replayable_source=True, consumer_node=node,
    )
    if helper_node is None:
        return None
    helper = dossier.verified_helpers.get(helper_node.name)
    if helper is None:
        return None
    try:
        sources = dossier.root_replay_helper_closure(support_helper_names=[helper.name])
        dossier.validate_helper_context(sources)
    except ValueError:
        return None
    if helper.source not in sources:
        return None
    return {"status": "proved", "kernel_verified": True, "helper_name": helper.name,
            "source": helper.source, "source_hash": helper.source_hash,
            "replay_sources": sources, "verification_environment_hash": helper.verification_environment_hash,
            "contract_identity": helper.contract_identity,
            "authority": "checked_exact_local_lean_statement_only"}


def _attempt_feedback(store: Any, graph: Any, attempt: Any) -> dict[str, Any] | None:
    if attempt is None:
        return None
    operational = (graph._is_operational_attempt_failure(attempt.verdict, attempt.error_type)
                   or attempt.verdict == "recursive_decomposition_llm_deferred")
    artifact = store.put_artifact(json_text(asdict(attempt)).encode(), name="native-local-proof-attempt.json")
    return {"status": "service_unavailable" if operational else "inconclusive",
            "kernel_verified": False, "mathematical_refutation": False,
            "attempt_artifact": artifact, "verdict": attempt.verdict,
            "error_type": attempt.error_type,
            "instruction": "The exact local task remains available under its existing proof allocation. This feedback does not refute the statement or discard partial proof work."}


def _retire_job_result_notifications(job: dict[str, Any], task_id: str | None) -> bool:
    changed = False
    for channel in ("messages", "inbox"):
        for message in job[channel]:
            try:
                payload = load_json(message.get("content", ""), max_depth=INTERNAL_JSON_NESTING)
            except (ValueError, TypeError):
                continue
            if not isinstance(payload, dict):
                continue
            result = payload.get("local_proof_result")
            if (not isinstance(result, dict) or task_id is not None and result.get("task_id") != task_id
                    or not result.get("kernel_verified")):
                continue
            message["content"] = json_text({
                "prior_context_notification": payload,
                "context_reaudit_required": True,
                "authority": "advisory_prior_context_history",
                "kernel_verified": False,
                "requires_response": payload.get("requires_response", False),
            })
            changed = True
    return changed


def _retire_result_notifications(store: Any, task_id: str) -> None:
    """Retain delivered proof text as history when its checked support is absent."""
    for job in store.jobs():
        if _retire_job_result_notifications(job, task_id):
            store.save_job(job)


def prepare_local_proof_notifications(store: Any, job: dict[str, Any]) -> None:
    """Fence uncommitted withdrawals in this job's ordinary dispatch transaction."""
    if getattr(store, "_local_proof_scan_pending", False):
        _retire_job_result_notifications(job, None)
    for task_id in getattr(store, "_local_proof_pending_withdrawals", ()):
        _retire_job_result_notifications(job, task_id)


def _fence_task_nodes(graph: Any, task_id: str) -> None:
    for node in graph.nodes.values():
        if node.metadata.get("native_local_proof_task_id") == task_id:
            node.metadata["schedulable"] = False


def _stored_notifier(owner: Any) -> Any:
    if owner.loop is not None:
        return owner.loop
    from .discovery import DiscoveryLoop

    def unavailable_provider(worker: str) -> Any:
        raise RuntimeError("stored notification delivery cannot dispatch a provider")

    return DiscoveryLoop(owner.store, unavailable_provider, unavailable_provider, native_mode=True)


def _notify_invalid_task(owner: Any, task_id: str, task: dict[str, Any]) -> bool:
    """Use job-owned task references when the request's return address is damaged."""
    store = owner.store
    recipients = [job for job in store.jobs()
                  if isinstance(job.get("native_local_proof_task_ids"), list)
                  and task_id in job["native_local_proof_task_ids"]
                  and task_id not in job.get("native_local_proof_invalid_task_ids", [])]
    if not recipients:
        return False
    result = {
        "task_id": task_id, "status": "invalid_request", "kernel_verified": False,
        "root_proved": False, "mathematical_refutation": False,
        "instruction": "Stored evidence for this local proof request is damaged. The task is fenced. "
                       "Continue the investigation or request a revised local statement; no mathematical "
                       "refutation or proof authority follows from this operational failure.",
    }
    artifact = store.put_artifact(json_text(result).encode(), name="native-local-proof-result.json")
    if task.get("result_artifact"):
        task["prior_context_result_artifact"] = task["result_artifact"]
    task["result_artifact"] = artifact
    notifier = _stored_notifier(owner)
    for recipient in recipients:
        notifier._notify(recipient["job_id"], {"local_proof_result": {
            "task_id": task_id, "artifact_id": artifact, "status": "invalid_request",
            "kernel_verified": False, "root_proved": False,
        }}, requires_response=True)
        # Notification routing can update the same job or its successor.
        current = store.job(recipient["job_id"])
        current.setdefault("native_local_proof_invalid_task_ids", []).append(task_id)
        store.save_job(current)
    return True


def reconcile_local_proofs(owner: Any, session: Any) -> bool:
    """Project open tasks and deliver results without spending/resetting budgets."""
    if owner.store is None or getattr(getattr(session, "dossier", None), "proof_graph", None) is None:
        return False
    session._native_local_proof_owner = owner
    store = owner.store
    graph = session.dossier.proof_graph
    changed = False
    storage_error: OSError | sqlite3.Error | None = None
    notifier = owner.loop
    pending = getattr(store, "_local_proof_pending_withdrawals", None)
    if pending is None:
        pending = store._local_proof_pending_withdrawals = set()
    try:
        tasks = store.run_record().get("native_local_proof_tasks", {})
    except (OSError, sqlite3.Error):
        # No individual task can be revalidated without its ledger snapshot.
        # Keep delivered proof text advisory until a later scan succeeds.
        store._local_proof_scan_pending = True
        raise
    if getattr(store, "_local_proof_scan_pending", False):
        pending.update(tasks)
        store._local_proof_scan_pending = False
    latest_attempts = {attempt.node_id: attempt for attempt in graph.attempts} if tasks else {}
    for task_id, previous in tasks.items():
        node = None
        withdraw_result = isinstance(previous, dict) and previous.get("status") == "proved"
        pending_validation = task_id in pending
        committed = True
        try:
            # Each task owns a transaction: damaged evidence cannot roll back
            # its siblings' ledger records or previously delivered results.
            with store.atomic():
                if pending_validation:
                    _retire_result_notifications(store, task_id)
                run = store.run_record()
                task = run["native_local_proof_tasks"][task_id]
                before = deepcopy(task)
                if isinstance(task, dict) and task.get("status") == "invalid_request":
                    withdraw_result = True
                    _fence_task_nodes(graph, task_id)
                    _retire_result_notifications(store, task_id)
                    if _notify_invalid_task(owner, task_id, task):
                        current = store.run_record()
                        current["native_local_proof_tasks"][task_id] = task
                        store.save_run(current)
                        changed = True
                    continue
                try:
                    request, context = _validated_request(store, task)
                    if task["task_id"] != task_id:
                        raise ValueError("local proof ledger key changed")
                    hints = _validated_hints(store, task, request)
                except (ValueError, KeyError, TypeError, FileNotFoundError) as exc:
                    withdraw_result = True
                    if not isinstance(task, dict):
                        task = {"task_id": task_id, "invalid_record": task}
                    task.update(status="invalid_request", invalid_request={
                        "error_type": type(exc).__name__,
                        "instruction": "Stored local proof evidence is invalid. The task is fenced; sibling tasks remain available.",
                    })
                    _fence_task_nodes(graph, task_id)
                    _retire_result_notifications(store, task_id)
                    _notify_invalid_task(owner, task_id, task)
                    current = store.run_record()
                    current["native_local_proof_tasks"][task_id] = task
                    store.save_run(current)
                    changed = True
                    continue
                matches = _context_matches(owner, session, request, context)
                node = graph.nodes.get(task["node_id"])
                if node is None and matches:
                    node = graph.record_missing_obligation(
                        statement=request["lean_statement"], reason=request["proof_plan"],
                        phase="native_local_proof", turn_index=getattr(session, "iteration", 0),
                        metadata={**context["statement_environment"],
                                  "identity_key": task_id,
                                  "formalization_obligation_key": task_id,
                                  "formalization_required": True,
                                  "allow_structurally_vacuous_helper": True,
                                  "native_local_proof_task_id": task_id,
                                  "native_local_proof_request_artifact": task["request_artifact"],
                                  "schedulable": False,
                                  "obligation_trust": "unproved_local_research_request"},
                    )
                    task["node_id"] = node.node_id
                if not matches:
                    withdraw_result = True
                    if task["status"] != "waiting_for_context":
                        task["prior_context_result_artifact"] = task["result_artifact"]
                        _retire_result_notifications(store, task_id)
                    result = {"status": "waiting_for_context", "kernel_verified": False,
                              "context_reaudit_required": True,
                              "prior_result_artifact": task.get("prior_context_result_artifact"),
                              "mathematical_refutation": False,
                              "instruction": "The original local task and attempts are retained. Its exact context must return before further proof work or current proof authority is available."}
                else:
                    result = _checked_result(session, node, request, context) if node is not None else None
                    if result is not None:
                        withdraw_result = False
                    if result is None and task["status"] == "proved":
                        withdraw_result = True
                        task["prior_context_result_artifact"] = task["result_artifact"]
                        _retire_result_notifications(store, task_id)
                    if result is None and node is not None:
                        result = _attempt_feedback(store, graph, latest_attempts.get(node.node_id))
                    if result is None and node is not None and node.status in {"rejected", "failed", "abandoned"}:
                        result = {"status": "inconclusive", "kernel_verified": False,
                                  "reason": str(node.metadata.get("reason") or node.status),
                                  "mathematical_refutation": False,
                                  "instruction": "This attempt did not establish the local statement. A service failure or exhausted attempt is not a mathematical refutation."}
                    if result is None and node is not None and node.statement != request["lean_statement"]:
                        result = {"status": "inconclusive", "kernel_verified": False,
                                  "reason": "graph statement changed; the original local request remains frozen",
                                  "mathematical_refutation": False}
                    if result is None and task["status"] == "proved":
                        result = {"status": "inconclusive", "kernel_verified": False,
                                  "context_reaudit_required": True,
                                  "prior_result_artifact": task["prior_context_result_artifact"],
                                  "mathematical_refutation": False,
                                  "instruction": "The checked local helper is no longer available. Prior proof text and attempts remain as history; fresh checked support is required to restore proof authority."}
                if result is not None:
                    result.update(task_id=task_id, lean_statement=request["lean_statement"],
                                  origin=request["origin"], contract=request["contract"], root_proved=False)
                    artifact = store.put_artifact(json_text(result).encode(), name="native-local-proof-result.json")
                    if (task["result_artifact"] != artifact
                            or pending_validation and result["kernel_verified"]):
                        if notifier is None:
                            notifier = _stored_notifier(owner)
                        notifier._notify(request["origin"]["job_id"], {
                            "local_proof_result": {"task_id": task_id, "artifact_id": artifact,
                                                   "status": result["status"], "origin": request["origin"],
                                                   "kernel_verified": result["kernel_verified"], "root_proved": False},
                        }, requires_response=True)
                        task["result_artifact"] = artifact
                    task["status"] = result["status"]
                elif task["status"] != "inconclusive":
                    task["status"] = "scheduled"
                if before != task:
                    # Notification routing may update other fields in the run.
                    current = store.run_record()
                    current["native_local_proof_tasks"][task_id] = task
                    store.save_run(current)
                    changed = True
            # Graph work becomes dispatchable only after its ledger transaction
            # commits. A failed transaction leaves any provisional node fenced.
            if node is not None:
                node.metadata["native_local_proof_followup_artifacts"] = list(task["followup_request_artifacts"])
                node.metadata["native_local_proof_hints"] = hints
                node.metadata["schedulable"] = matches and node.statement == request["lean_statement"]
        except (OSError, sqlite3.Error) as exc:
            committed = False
            # The failed transaction has rolled back. Still reconcile siblings:
            # their previously delivered proof authority may need withdrawal.
            # Report the storage failure after independent transactions finish.
            _fence_task_nodes(graph, task_id)
            if storage_error is None:
                storage_error = exc
            if withdraw_result:
                pending.add(task_id)
                # Withdrawal has no dependence on committing the failed task
                # update. Preserve it even when quarantine/result bookkeeping
                # rolled back the first transaction's notification changes.
                try:
                    with store.atomic():
                        _retire_result_notifications(store, task_id)
                except (OSError, sqlite3.Error):
                    # A store-wide outage can also prevent withdrawal. Keep
                    # reporting it while allowing independent siblings to run.
                    storage_error.add_note("Local proof notification withdrawal was also unavailable.")
        except BaseException:
            committed = False
            _fence_task_nodes(graph, task_id)
            raise
        finally:
            if committed:
                pending.discard(task_id)
    if storage_error is not None:
        raise storage_error
    return changed


def task_inventory(store: Any) -> list[dict[str, Any]]:
    if store is None:
        return []
    result = []
    for task_id, task in store.run_record().get("native_local_proof_tasks", {}).items():
        if not isinstance(task, dict) or task.get("status") == "invalid_request":
            result.append({"task_id": task_id, "status": "invalid_request", "kernel_verified": False})
            continue
        result.append({"task_id": task["task_id"], "status": task["status"], "node_id": task["node_id"],
                       "request_artifact": task["request_artifact"], "result_artifact": task["result_artifact"],
                       "followup_request_artifacts": list(task["followup_request_artifacts"]),
                       "lean_statement": task["request"]["lean_statement"], "origin": task["request"]["origin"]})
    return result
