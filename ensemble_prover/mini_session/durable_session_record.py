"""Lossless session data projection with fresh verification on disk restore.

Only explicitly known value classes are decoded. Runtime services and sibling
sessions remain owned by the attempt coordinator. No saved Python object or
serialized proof certificate is treated as a live verifier capability.
"""

from __future__ import annotations

import asyncio
from collections import deque
import copy
from dataclasses import fields
import hashlib
import inspect
import json
import math
from pathlib import Path
import time
from typing import Any, Callable
import uuid

from ensemble_prover.proof_dossier import (
    ProofDossier, helper_decl_name, text_hash,
)
from ensemble_prover.verified_helper_contract import (
    analyze_verified_helper_source_contract, analyze_verified_helper_declarations,
    helper_contract_context_is_plain, helper_source_contract_is_context_sensitive,
    helper_source_requires_contract_analysis,
    refresh_verified_helper_contract,
)
from ensemble_prover.proof_state import ProofSearchState, ProofStateWorkItem
from ensemble_prover.root_finalization import RootFinalizationCandidate
from ensemble_prover.state_data import clone_json_value
from ensemble_prover.mini_theory.model import TheoryNeed
from ensemble_prover.formalization.environment import runtime_selector_snapshot

from .action import ActionBudget, MiniOutcome, RepairTicket
from .capability_policy import field_is_runtime_capability
from .durable_lean_environment import material_environment_hash
from .replay import _action_specs, apply_scheduler_snapshot, scheduler_snapshot
from .turn.extract import TurnExtraction
from .turn.post_failure import PostFailureResult

SCHEMA_VERSION = 1
_VALUE_CLASSES = {value.__name__: value for value in (
    ActionBudget, MiniOutcome, RepairTicket, RootFinalizationCandidate,
    ProofStateWorkItem, TurnExtraction, PostFailureResult, TheoryNeed,
)}
_RUNTIME_FIELDS = frozenset({
    "problem", "dossier", "proof_state", "conv", "actions", "budgets",
    "cost_controller", "parent", "checkpoint_registry", "checkpoint_lane_key",
    "theory_context_pair", "session_activation_id", "_mini_planner_job_broker",
    "_pending_isolated_dispatch_tails", "_detached_execution_settlements",
    "_quarantined_lean_runners",
    "_latest_pre_select_snapshot", "_dispatch_generation_resume_snapshot",
    "_dispatch_generation_late_rollback_snapshot", "_run_governor_last_tick_monotonic",
    "_native_research_governor_clock",
    "_applying_action_dispatch_ids", "_duplicate_action_dispatch_events_in_progress",
    "_inflight_action_dispatch_id", "_apply_transition_active",
    "_inflight_provider_exposure_tracker",
    "_mini_recursive_hard_timeout_lease",
    "_checkpoint_initial_theory_context_hash",
    "_acceptance_receipt_flush_active",
})
# The recursive prove/refine handoff reuses its conversation, including this
# parent-bound commit/rollback handle. Only the accompanying theory provenance
# belongs on disk; the factory recreates the handle when a child returns/replays.
_CONVERSATION_RUNTIME_FIELDS = frozenset({
    "mini_theory_commit_promotion", "_unverified_candidate_cancellation_sink",
})
_IDENTITY_CONV_FIELDS = (
    "goal_statement", "lean_signature", "preamble", "lean_preamble", "opaque_mode",
    "allow_official_answer_visibility", "official_answer_payload_present",
    "suppress_solution_placeholders", "allow_helper_decomposition",
)


def _encode(value: Any, *, path: str = "value") -> Any:
    """Encode an allowlisted value union, never application reduction hooks."""
    from ensemble_prover.lean_parser import LeanOutput

    kind = type(value)
    if kind is LeanOutput:
        return str.__str__(value)
    if value is None or kind in {str, bool, int}:
        return value
    if kind is float:
        if not math.isfinite(value):
            raise ValueError(f"nonfinite checkpoint value at {path}")
        return value
    if kind in {list, tuple, set, frozenset}:
        items = [_encode(item, path=f"{path}[]") for item in value]
        if kind is list:
            return items
        if kind in {set, frozenset}:
            items.sort(key=lambda item: json.dumps(item, sort_keys=True))
        return {"value_type": kind.__name__, "items": items}
    if kind is dict:
        return {"value_type": "dict", "items": [
            [_encode(key, path=path), _encode(item, path=f"{path}.{key}")]
            for key, item in value.items()
        ]}
    if kind.__name__ in _VALUE_CLASSES and _VALUE_CLASSES[kind.__name__] is kind:
        # Thaw immutable theory evidence recursively: passing mapping proxies
        # to its constructor would stringify nested evidence.
        payload = value.to_dict() if kind is TheoryNeed else {
            field.name: getattr(value, field.name) for field in fields(kind)
        }
        return {"value_type": kind.__name__, "fields": {
            name: _encode(item, path=f"{path}.{name}")
            for name, item in payload.items()
        }}
    if isinstance(value, BaseException):
        # The settled outcome already contains canonical diagnostic policy.
        # Exception objects, responses, tracebacks and transport handles do not.
        return {"value_type": "settled_exception", "message": str(value)}
    raise ValueError(f"unsupported checkpoint value {kind.__name__} at {path}")


def _decode(value: Any) -> Any:
    if value is None or type(value) in {str, bool, int, float}:
        return value
    if type(value) is list:
        return [_decode(item) for item in value]
    if type(value) is not dict:
        raise ValueError("malformed checkpoint value")
    kind = value.get("value_type")
    if kind in {"tuple", "set", "frozenset", "dict"}:
        if set(value) != {"value_type", "items"} or type(value["items"]) is not list:
            raise ValueError("malformed checkpoint container")
        items = [_decode(item) for item in value["items"]]
        try:
            if kind == "dict":
                result = dict(items)
                if len(result) != len(items):
                    raise ValueError("duplicate checkpoint mapping key")
                return result
            return {"tuple": tuple, "set": set, "frozenset": frozenset}[kind](items)
        except (TypeError, ValueError) as error:
            raise ValueError("malformed checkpoint container items") from error
    if kind == "settled_exception" and set(value) == {"value_type", "message"}:
        if type(value["message"]) is not str:
            raise ValueError("malformed settled exception")
        return RuntimeError(value["message"])
    cls = _VALUE_CLASSES.get(kind)
    if cls is not None and set(value) == {"value_type", "fields"}:
        payload = value["fields"]
        if type(payload) is not dict or set(payload) != {item.name for item in fields(cls)}:
            raise ValueError("malformed checkpoint value fields")
        return cls(**{key: _decode(item) for key, item in payload.items()})
    raise ValueError("unknown checkpoint value type")


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                     allow_nan=False, separators=(",", ":")).encode()).hexdigest()


def _checkpoint_import_config(lean: Any) -> dict[str, Any]:
    config = getattr(lean, "cfg", None)
    return {
        name: clone_json_value(getattr(config, name, default))
        for name, default in (
            ("project_imports", []), ("project_import_sources", {}),
            ("support_project_builds", {}), ("extra_imports", []),
            ("module_search_paths", []), ("preamble_import", ""),
            ("preamble_tactics", ""),
        )
    }


def _checkpoint_runner_context(lean: Any, preamble: str = "") -> tuple[Any, ...]:
    """Track mutable verifier inputs without rescanning its imported files."""
    from ensemble_prover.lean_runner import LeanREPL

    project = getattr(lean, "project_dir", None)
    project_key = str(Path(project).resolve()) if project is not None else ""
    import_config = _checkpoint_import_config(lean)
    return (
        id(lean), project_key, _digest(import_config),
        getattr(lean, "_execution_environment_generation", 0),
        LeanREPL._GLOBAL_ENV_EPOCH.get(project_key, 0),
        runtime_selector_snapshot(),
        (material_environment_hash(lean, Path(project_key), import_config, preamble)
         if project is not None else ""),
    )


def initialize_theory_checkpoint_context(session: Any) -> None:
    """Bind the initial configured theory before a durable session can evolve."""
    pair = getattr(session, "theory_context_pair", None)
    if pair is not None and not hasattr(session, "_checkpoint_initial_theory_context_hash"):
        session._checkpoint_initial_theory_context_hash = pair.snapshot_hash


def _theory_checkpoint_context(session: Any) -> dict[str, Any] | None:
    pair = getattr(session, "theory_context_pair", None)
    if pair is None:
        return None
    if pair.lean.bundle_ids and not hasattr(session, "_checkpoint_initial_theory_context_hash"):
        raise ValueError("Initial theory context must be bound before installing bundles")
    initialize_theory_checkpoint_context(session)
    if (tuple(session.theory_imported_bundle_ids) != pair.lean.bundle_ids
            or session.conv.preamble != pair.llm.render()
            or session.conv.lean_preamble != pair.lean.render()):
        raise ValueError("Theory context differs from its live session binding")
    result = {
        "initial_context_hash": session._checkpoint_initial_theory_context_hash,
        "bundle_ids": list(pair.lean.bundle_ids),
        "snapshot": clone_json_value(list(session.theory_snapshot)),
    }
    imports = getattr(session, "_checked_source_imports", ())
    if imports:
        result["source_imports"] = clone_json_value(imports)
    return result


async def _prepare_theory_checkpoint_context(
    session: Any, data: dict[str, Any], values: dict[str, Any],
) -> Any:
    """Regenerate saved imports from the fresh checked library in isolation."""
    saved = data.get("theory_context")
    if saved is None:
        return session
    if (type(saved) is not dict
            or set(saved) not in (
                {"initial_context_hash", "bundle_ids", "snapshot"},
                {"initial_context_hash", "bundle_ids", "snapshot", "source_imports"},
            )
            or type(saved["initial_context_hash"]) is not str
            or type(saved["bundle_ids"]) is not list
            or any(type(item) is not str or not item for item in saved["bundle_ids"])
            or len(set(saved["bundle_ids"])) != len(saved["bundle_ids"])
            or type(saved["snapshot"]) is not list):
        raise ValueError("Invalid durable theory context")
    pair = getattr(session, "theory_context_pair", None)
    if pair is not None and (pair.llm.render() != session.conv.preamble
                             or pair.lean.render() != session.conv.lean_preamble):
        raise ValueError("Fresh theory context differs from its live session binding")
    source_imports = saved.get("source_imports", [])
    if (type(source_imports) is not list
            or source_imports != values.get("_checked_source_imports", [])
            or any(type(item) is not dict
                   or set(item) != {"module", "declaration", "statement"}
                   or any(type(value) is not str or not value for value in item.values())
                   for item in source_imports)):
        raise ValueError("Invalid durable source import admissions")
    if pair is None and source_imports:
        from ensemble_prover.mini_theory.context import TheoryContextPair

        pair = TheoryContextPair.from_preambles(
            llm_preamble=session.conv.preamble,
            lean_preamble=session.conv.lean_preamble,
        )
    initial_hash = getattr(session, "_checkpoint_initial_theory_context_hash", None)
    if (pair is None
            or (saved["bundle_ids"] and getattr(session, "theory_library", None) is None)
            or saved["initial_context_hash"] != (initial_hash or pair.snapshot_hash)
            or saved["bundle_ids"] != data["scheduler"]["session_state"].get("theory_imported_bundle_ids")
            or saved["snapshot"] != list(values.get("theory_snapshot", ()))):
        raise ValueError("Theory checkpoint differs from its configured initial context")
    from .source_imports import source_import_context

    view = copy.copy(session)
    view.conv = copy.copy(session.conv)
    # Reconstruct only checked import commands; saved preamble text never
    # supplies declarations, options or other commands to the fresh verifier.
    for receipt in source_imports:
        pair = source_import_context(pair, receipt["module"])
    view.theory_context_pair = pair
    prepared = (
        await asyncio.to_thread(view.prepare_theory_bundles, saved["bundle_ids"])
        if saved["bundle_ids"]
        else ((), pair, pair, ())
    )
    if prepared is None:
        raise ValueError("Theory checkpoint has no fresh library binding")
    _requested, _previous, selected, snapshot = prepared
    if (list(selected.lean.bundle_ids) != saved["bundle_ids"]
            or clone_json_value(list(snapshot)) != saved["snapshot"]):
        raise ValueError("Theory checkpoint source differs from the fresh verified snapshot")
    view.conv.preamble = selected.llm.render()
    view.conv.lean_preamble = selected.lean.render()
    view.theory_context_pair = selected
    view.theory_snapshot = tuple(snapshot)
    view.theory_imported_bundle_ids = selected.lean.bundle_ids
    return view


def session_checkpoint_identity(session: Any) -> dict[str, Any]:
    """Compute compatibility from the fresh runtime, independently of saved data."""
    conv = session.conv
    context = {key: getattr(conv, key, None) for key in _IDENTITY_CONV_FIELDS}
    project = getattr(session.lean, "project_dir", None)
    project_files: dict[str, str] = {}
    if project is not None:
        directory = Path(project).resolve()
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"):
            path = directory / name
            if path.is_file():
                project_files[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        project_files["project_dir"] = str(directory)
        import_config = _checkpoint_import_config(session.lean)
        project_files["import_config"] = _digest(import_config)
        sources = dict(import_config["project_import_sources"])
        for module in import_config["project_imports"]:
            sources.setdefault(module, str(directory / (module.replace(".", "/") + ".lean")))
        for module, raw_path in sorted(sources.items()):
            path = Path(raw_path)
            if not path.is_absolute():
                path = directory / path
            project_files[f"source:{module}:{path.resolve()}"] = (
                hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "missing"
            )
        project_files["material_environment"] = material_environment_hash(
            session.lean, directory, import_config, str(context["lean_preamble"] or ""),
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "context_hash": _digest(context),
        "actions_hash": _digest(_action_specs(session)),
        "project_hash": _digest(project_files),
        "attempt_identity": clone_json_value(
            getattr(session, "checkpoint_identity", {}), label="checkpoint identity"),
    }


def _require_settled(session: Any) -> None:
    if (getattr(session, "_apply_transition_active", False)
            or getattr(session, "_inflight_action_dispatch_id", "")
            or getattr(session, "_applying_action_dispatch_ids", set())
            or getattr(session, "_pending_isolated_dispatch_tails", set())):
        raise ValueError("checkpoint requires a settled committed action boundary")
    tracker = getattr(session, "_inflight_provider_exposure_tracker", None)
    if getattr(tracker, "provider_dispatches_started", 0):
        # Recovery must charge live exposure into durable scheduler totals
        # before this runtime-only tracker can be omitted from the record.
        raise ValueError("checkpoint requires settled provider exposure")


def _validated_research_governor_coverage(value: Any, elapsed: float) -> dict[str, Any]:
    """Validate historical overlap ceilings before publishing restored state."""
    if (type(value) is not dict or set(value) != {"by_clock", "legacy_elapsed_s"}
            or type(value["by_clock"]) is not dict
            or any(type(key) is not str or not key for key in value["by_clock"])):
        raise ValueError("invalid native research governor coverage")
    for covered in [value["legacy_elapsed_s"], *value["by_clock"].values()]:
        if (type(covered) not in {int, float} or not math.isfinite(covered)
                or not 0 <= covered <= elapsed):
            raise ValueError("invalid native research governor coverage")
    return {"by_clock": dict(value["by_clock"]), "legacy_elapsed_s": value["legacy_elapsed_s"]}


def _capture_research_governor_coverage(session: Any) -> dict[str, Any]:
    """Attribute this snapshot's observation only to its live governor clock."""
    elapsed = float(session.run_governor_elapsed_s or 0.0)
    clock = getattr(session, "_native_research_governor_clock", None)
    by_clock = dict(clock.get("coverage_by_clock", {})) if clock is not None else {}
    legacy = clock.get("restored_elapsed_s") if clock is not None else None
    if clock is not None:
        by_clock[clock["identity"]] = elapsed
    # Before the first restore, this process owns any legacy observations.
    # Thereafter their original ceiling stays fixed across later checkpoints.
    return _validated_research_governor_coverage({
        "by_clock": by_clock,
        "legacy_elapsed_s": elapsed if legacy is None else legacy,
    }, elapsed)


def capture_session_record(session: Any) -> dict[str, Any]:
    """Capture only this settled session; never traverse shared live services."""
    _require_settled(session)
    if not isinstance(session.dossier, ProofDossier) or session.conv is None:
        raise ValueError("checkpoint requires a dossier and conversation")
    theory_context = _theory_checkpoint_context(session)
    scheduler = scheduler_snapshot(session, include_proof_state=False)
    scheduler.pop("cost_budget", None)  # The coordinator owns the shared ledger.
    values = {
        key: _encode(value, path=f"session.{key}")
        for key, value in vars(session).items()
        if key not in _RUNTIME_FIELDS and not field_is_runtime_capability(key)
        and key not in scheduler["session_state"]
    }
    record = {
        "schema_version": SCHEMA_VERSION,
        "clock": {"epoch_s": time.time(), "monotonic_s": time.monotonic()},
        "native_research_governor_coverage": _capture_research_governor_coverage(session),
        "identity": session_checkpoint_identity(session),
        "conversation": _encode({
            key: value for key, value in vars(session.conv).items()
            if key not in _CONVERSATION_RUNTIME_FIELDS
        }, path="conversation"),
        "dossier": session.dossier.to_execution_record(),
        "proof_state": session.proof_state.to_execution_record() if session.proof_state is not None else None,
        "scheduler": scheduler,
        "session_values": values,
        "theory_context": theory_context,
    }
    return clone_json_value(record, label="durable session record")


def _fresh_check_options(lean: Any, preamble: str) -> dict[str, Any]:
    # A restart establishes new authority; a completed execution cache entry
    # must not substitute for the independent reference check.
    options: dict[str, Any] = {"preamble_override": preamble}
    try:
        parameters = inspect.signature(lean.check).parameters
        if "force_reference" in parameters or any(
            item.kind is inspect.Parameter.VAR_KEYWORD for item in parameters.values()
        ):
            options["force_reference"] = True
    except (TypeError, ValueError):
        pass
    return options


async def _verify(lean: Any, *, statement: str, proof: str, helpers: list[str], preamble: str) -> None:
    result = await lean.check(statement, proof, helpers, **_fresh_check_options(lean, preamble))
    if not getattr(result, "ok", False) or getattr(result, "axiom_audit_ok", None) is False:
        raise ValueError("saved proof failed fresh Lean checkpoint verification")


def _checkpoint_helper_order(helpers: dict[str, Any]) -> list[Any]:
    """Order the complete declared replay DAG without Python recursion."""
    remaining = {}
    consumers: dict[str, list[str]] = {}
    for name, helper in helpers.items():
        dependencies = set(helper.support_names or ()) | set(helper.replay_context_names or ())
        if not dependencies <= helpers.keys():
            raise ValueError("checkpoint helper dependency cycle or missing support")
        remaining[name] = len(dependencies)
        for dependency in dependencies:
            consumers.setdefault(dependency, []).append(name)
    ready = deque(name for name in helpers if not remaining[name])
    ordered = []
    while ready:
        name = ready.popleft()
        ordered.append(helpers[name])
        for consumer in consumers.get(name, ()):
            remaining[consumer] -= 1
            if remaining[consumer] == 0:
                ready.append(consumer)
    if len(ordered) != len(helpers):
        raise ValueError("checkpoint helper dependency cycle or missing support")
    return ordered


def _clear_saved_helper_contract(dossier: ProofDossier, helper: Any) -> bool:
    """Discard serialized type observations before obtaining fresh evidence."""
    fields = (
        "contract_identity", "contract_identity_statement_key",
        "contract_identity_environment_hash", "contract_identity_evidence_receipt",
        "contract_display_statement", "contract_binder_evidence_receipt",
        "contract_binder_sorts", "contract_proof_binder_types",
    )
    had_evidence = any(getattr(helper, name) for name in fields)
    for name in fields:
        setattr(helper, name, [] if name in {
            "contract_binder_sorts", "contract_proof_binder_types",
        } else "")
    node_id = dossier.proof_graph.helper_name_to_node_id.get(helper.name)
    node = dossier.proof_graph.nodes.get(node_id)
    if node is not None:
        for name in fields:
            key = "verified_helper_" + name
            if key in node.metadata:
                node.metadata[key] = copy.deepcopy(getattr(helper, name))
    return had_evidence


async def _prepare_dossier(
    session: Any, data: dict[str, Any], *, staged_dossier: ProofDossier | None = None,
    context_is_current: Callable[[], bool] | None = None,
) -> ProofDossier:
    """Freshly verify an imported private dossier before publishing authority.

    Full session restore supplies its already-imported staging object so fresh
    helper evidence updates the graph bound to its validated scheduler/actions.
    Other callers receive an independently imported dossier as before.
    """
    dossier = (staged_dossier if staged_dossier is not None
               else ProofDossier._from_execution_record_for_reverification(data))
    originals = data.get("verified_helpers")
    if type(originals) is not list:
        raise ValueError("checkpoint helper list is malformed")
    expected = {item["name"]: item for item in originals}
    if len(expected) != len(originals) or set(expected) != set(dossier.verified_helpers):
        raise ValueError("checkpoint helper admission rejected saved source")
    ordered = _checkpoint_helper_order(dossier.verified_helpers)
    for helper in ordered:
        saved = expected[helper.name]
        if helper.source != saved.get("source") or text_hash(helper.source) != saved.get("source_hash"):
            raise ValueError("checkpoint helper source hash mismatch")
    environment = str(dossier.current_lean_environment_hash or "")
    preamble = str(session.conv.lean_preamble or "")
    target = str(getattr(session.conv, "goal_statement", dossier.root_statement) or "")
    runner_context = _checkpoint_runner_context(session.lean, preamble)
    if target != str(dossier.root_statement or ""):
        raise ValueError("checkpoint dossier target identity mismatch")

    def current_context() -> bool:
        return (
            preamble == str(session.conv.lean_preamble or "")
            and environment == str(dossier.current_lean_environment_hash or "")
            and target == str(getattr(session.conv, "goal_statement", dossier.root_statement) or "")
            and target == str(dossier.root_statement or "")
            and runner_context == _checkpoint_runner_context(session.lean, preamble)
            and (context_is_current is None or context_is_current())
        )
    if not current_context():
        raise ValueError("checkpoint verification context changed before replay")
    # The checker audits every local declaration, including unused helpers.
    # Publish no restored authority until this whole fresh replay succeeds.
    if ordered:
        await _verify(session.lean, statement="True", proof="by trivial",
                      helpers=[helper.source for helper in ordered], preamble=preamble)
    if not current_context():
        raise ValueError("checkpoint verification context changed during replay")
    refresh_answer_receipts = bool(getattr(dossier, "_checkpoint_pending_answer_receipts", ()))
    saved_contracts = {helper.name: copy.deepcopy(helper) for helper in ordered}
    cleared_contracts = {
        helper.name: _clear_saved_helper_contract(dossier, helper) for helper in ordered
    }
    observed = await analyze_verified_helper_declarations(
        session.lean, [helper.source for helper in ordered], preamble=preamble,
        environment_hash=environment, timeout_s=30.0, context_is_current=current_context,
    )
    if not current_context():
        raise ValueError("checkpoint verification context changed during contract analysis")
    checked: list[str] = []
    prefix_is_plain = helper_contract_context_is_plain(session.lean, preamble=preamble, context=())
    for helper in ordered:
        checked_in_new_environment = helper.verification_environment_hash != environment
        observation_required = helper_source_contract_is_context_sensitive(
            helper.source, context_is_plain=prefix_is_plain,
        )
        analysis_required = helper_source_requires_contract_analysis(
            helper.source, context_is_plain=prefix_is_plain,
        )
        observation_requirement_changed = (
            bool(getattr(helper, "contract_observation_required", False)) != observation_required
        )
        # This staging object has no authority yet. A saved marker cannot
        # replace classification of the context just checked by this runner.
        helper.contract_observation_required = observation_required
        contract_fields = observed.get(helper.source) or (
            await analyze_verified_helper_source_contract(
                session.lean, helper.source,
                preamble=preamble, context=checked,
                environment_hash=environment, timeout_s=30.0,
                context_is_current=current_context,
            ) if analysis_required else {}
        )
        if not current_context():
            raise ValueError("checkpoint verification context changed during contract analysis")
        if checked_in_new_environment or cleared_contracts[helper.name] or observation_requirement_changed:
            # Only the fresh body replay above authorizes rebinding an
            # ancestor-verified declaration to the checked environment.
            # Ordinary same-source imports still reject this change.
            # Saved type receipts establish internal consistency only. An
            # unavailable fresh observation leaves this checked source with
            # conservative metadata, including in an unchanged environment.
            rebound_fields = dict(contract_fields)
            rebound_fields["_verification_environment_hash"] = environment
            rebound = dossier.record_verified_helper(
                helper.source, phase=helper.phase, turn_index=helper.turn_index,
                support_names=helper.support_names,
                replay_context_names=helper.replay_context_names,
                provenance_tags=helper.provenance_tags,
                visibility_policy=helper.visibility_policy,
                contract_observation_required=observation_required,
                replace_existing_same_name=True,
                _progress_anchor_from=saved_contracts[helper.name],
                **rebound_fields,
            )
            if rebound is None:
                raise ValueError("checkpoint helper environment rebinding rejected")
            # Rebinding the environment does not replace historical source
            # obligations with hashes read from today's helper registry.
            rebound.support_source_hashes = copy.deepcopy(helper.support_source_hashes)
            rebound.replay_context_source_hashes = copy.deepcopy(helper.replay_context_source_hashes)
        else:
            refresh_verified_helper_contract(dossier, helper, contract_fields)
        checked.append(helper.source)
        prefix_is_plain = prefix_is_plain and helper_contract_context_is_plain(
            session.lean, preamble="", context=(helper.source,),
        )
    if refresh_answer_receipts:
        # The exact whole source context passed fresh independent Lean checking.
        # Rebuild current parser receipts only after serialized type authority
        # is replaced by fresh observations or conservative missing-type policy.
        del dossier._checkpoint_pending_answer_receipts
        dossier._sync_legacy_helpers_to_graph()
        dossier.reconcile_verified_facts(trigger="checkpoint_fresh_helper_replay")
    if dossier.final_proof:
        if text_hash(dossier.final_proof) != data.get("final_proof_hash"):
            raise ValueError("checkpoint root proof hash mismatch")
        # Export and root handoff consume the certificate, while replay uses
        # the dossier artifact. They must identify the same ordered source
        # before fresh checking can authorize either representation. Raw
        # verifier provenance may differ after diagnostic sanitization; these
        # artifact fields always describe the saved, sanitized Lean source.
        replay_helpers = list(dossier.final_replay_helpers)
        certificate = dossier.root_proof_certificate
        artifact_fields = {
            "theorem_name": dossier.theorem_name,
            "root_statement": dossier.root_statement,
            "root_statement_hash": text_hash(dossier.root_statement),
            "proof": dossier.final_proof,
            "proof_hash": text_hash(dossier.final_proof),
            "replay_helpers": replay_helpers,
            "replay_helper_names": [
                name for block in replay_helpers if (name := helper_decl_name(block))
            ],
            "replay_helper_source_hashes": [text_hash(block) for block in replay_helpers],
            "replay_helper_count": len(replay_helpers),
        }
        if not isinstance(certificate, dict) or any(
            type(certificate.get(key)) is not type(value) or certificate.get(key) != value
            for key, value in artifact_fields.items()
        ):
            raise ValueError("checkpoint root certificate artifact mismatch")
        await _verify(session.lean, statement=target,
                      proof=dossier.final_proof, helpers=replay_helpers,
                      preamble=preamble)
        if not current_context():
            raise ValueError("checkpoint verification context changed during root replay")
        # Fresh checking above, not the JSON hash, establishes this receipt.
        dossier.record_root_proof_finalization_receipt()
    return dossier


def _prepare_bound_publication(session: Any, staged: Any) -> tuple[Any, ...]:
    """Copy validated values while keeping every factory-bound object live."""
    bindings = [
        (staged, session), (staged.conv, session.conv),
        (staged.dossier, session.dossier),
        (staged.dossier.proof_graph, session.dossier.proof_graph),
        *zip(staged.actions, session.actions, strict=True),
    ]
    if staged.proof_state is not None:
        bindings.append((staged.proof_state, session.proof_state))
    memo = {id(prepared): live for prepared, live in bindings}
    for owner in (staged, *staged.actions):
        for key, value in vars(owner).items():
            if field_is_runtime_capability(key) or (owner is staged and key in _RUNTIME_FIELDS):
                memo.setdefault(id(value), value)
    values = copy.deepcopy({
        key: value for key, value in vars(staged).items()
        if key not in _RUNTIME_FIELDS and not field_is_runtime_capability(key)
    }, memo)
    return (
        values, copy.deepcopy(staged.budgets, memo),
        copy.deepcopy(vars(staged.conv), memo),
        copy.deepcopy(vars(staged.dossier), memo),
        copy.deepcopy(vars(staged.dossier.proof_graph), memo),
        copy.deepcopy(vars(staged.proof_state), memo) if staged.proof_state is not None else None,
        [copy.deepcopy(vars(action), memo) for action in staged.actions],
    )


def _release_obsolete_negation_conflict(session: Any) -> None:
    """Let saved conflicts from older negation verifiers reach fresh replay."""
    from ..mini_falsification.model import KERNEL_NEGATION_VERIFIER_VERSION

    dossier = session.dossier
    conflicts = dossier.mini_falsification_trust_boundary_conflict_certificate_hashes
    legacy_hashes = {
        str(certificate.get("certificate_hash") or "")
        for report in dossier.mini_falsification_ledger
        for finding in report.get("findings") or ()
        if isinstance(finding, dict)
        for certificate in [finding.get("certificate")]
        if isinstance(certificate, dict)
        and certificate.get("verifier_version") != KERNEL_NEGATION_VERIFIER_VERSION
    }
    if (not conflicts or not conflicts <= legacy_hashes
            or bool(getattr(dossier, "_mini_falsification_trust_boundary_conflict_certificate_hashes", set()))):
        return
    # The public conflict history remains intact. Release only the terminal
    # latch attributable entirely to those obsolete certificates; unrelated
    # failures and current-verifier conflicts keep their existing treatment.
    reason = "falsification_trust_boundary_conflict"
    for owner, reason_field, kind_field in (
        (session, "terminal_failure_reason", "terminal_failure_kind"),
        (session.conv, "_last_llm_failure_reason", "_last_llm_failure_kind"),
        (dossier, "session_failure_reason", "session_failure_kind"),
    ):
        if getattr(owner, reason_field, "") == reason:
            setattr(owner, reason_field, "")
            setattr(owner, kind_field, "")
    if getattr(session, "last_failure_reason", "") == reason:
        session.last_failure_reason = ""


async def restore_session_record(session: Any, record: dict[str, Any], *, expected_identity: dict[str, Any]) -> None:
    """Validate in isolation, recheck proofs, then install into bound objects."""
    _require_settled(session)
    if getattr(session, "_detached_execution_settlements", ()):
        # Capture can preserve an incomplete tail, but replacing a live owner
        # would strand its callback on the old budget and observation map.
        raise ValueError("checkpoint restore requires settled detached execution resources")
    live_context = tuple(getattr(session.conv, key, None) for key in _IDENTITY_CONV_FIELDS)
    live_runner_context = _checkpoint_runner_context(session.lean, str(session.conv.lean_preamble or ""))

    def live_context_is_current() -> bool:
        return (
            live_context == tuple(getattr(session.conv, key, None) for key in _IDENTITY_CONV_FIELDS)
            and live_runner_context == _checkpoint_runner_context(session.lean, str(session.conv.lean_preamble or ""))
        )

    data = clone_json_value(record, label="durable session restore")
    if type(data) is not dict or type(data.get("schema_version")) is not int or data["schema_version"] != SCHEMA_VERSION:
        raise ValueError("unsupported durable session checkpoint schema")
    if data.get("identity") != expected_identity:
        raise ValueError("checkpoint identity differs from the fresh target, environment or policy")
    conversation = _decode(data["conversation"])
    if type(conversation) is not dict or any(type(key) is not str for key in conversation):
        raise ValueError("malformed checkpoint conversation")
    if _CONVERSATION_RUNTIME_FIELDS.intersection(conversation):
        raise ValueError("checkpoint conversation cannot restore runtime capabilities")
    values = {key: _decode(value) for key, value in data["session_values"].items()}
    if values.get("_acceptance_receipt_flush_active") is False:
        values.pop("_acceptance_receipt_flush_active")
    # Older settled records could contain the inactive None default. It is
    # data-free and must not overwrite the fresh runtime tracker on restore.
    if values.get("_inflight_provider_exposure_tracker") is None:
        values.pop("_inflight_provider_exposure_tracker", None)
    verifier_view = await _prepare_theory_checkpoint_context(session, data, values)
    if not live_context_is_current():
        raise ValueError("checkpoint verification context changed during theory preparation")
    if expected_identity != session_checkpoint_identity(verifier_view):
        raise ValueError("checkpoint identity differs from the fresh target, environment or policy")
    verifier_context = tuple(getattr(verifier_view.conv, key, None) for key in _IDENTITY_CONV_FIELDS)
    verifier_runner_context = _checkpoint_runner_context(verifier_view.lean, str(verifier_view.conv.lean_preamble or ""))

    def verification_context_is_current() -> bool:
        return (
            live_context_is_current()
            and verifier_context == tuple(
                getattr(verifier_view.conv, key, None) for key in _IDENTITY_CONV_FIELDS
            )
            and verifier_runner_context == _checkpoint_runner_context(verifier_view.lean, str(verifier_view.conv.lean_preamble or ""))
        )

    verifier_preamble = str(verifier_view.conv.lean_preamble or "")
    # The identity above includes fresh source/compiled inputs for the complete
    # import closure. Re-establish each declaration admission independently,
    # before publishing any context or retrieval availability to the session.
    for receipt in values.get("_checked_source_imports", ()):
        admitted = await verifier_view.lean.check(
            receipt["statement"], f"by exact @{receipt['declaration']}", [],
            **_fresh_check_options(verifier_view.lean, verifier_preamble),
        )
        if not verification_context_is_current():
            raise ValueError("checkpoint verification context changed during source admission")
        if not getattr(admitted, "ok", False) or getattr(admitted, "axiom_audit_ok", None) is not True:
            raise ValueError("saved source import failed fresh Lean admission")
    clock = data.get("clock")
    if (type(clock) is not dict or set(clock) != {"epoch_s", "monotonic_s"}
            or any(type(value) not in {int, float} or not math.isfinite(value)
                   for value in clock.values())):
        raise ValueError("Invalid durable checkpoint clock origin")
    downtime = max(0.0, time.time() - clock["epoch_s"])
    now_monotonic = time.monotonic()

    def rebase_deadline(deadline: Any) -> float:
        if type(deadline) not in {int, float} or not math.isfinite(deadline) or deadline < 0:
            raise ValueError("Invalid durable scheduler backoff deadline")
        if not deadline:
            return 0.0
        return now_monotonic + max(0.0, deadline - clock["monotonic_s"] - downtime)

    ready = values.get("_dispatch_generation_action_ready_monotonic", {})
    if type(ready) is not dict or any(type(key) is not str for key in ready):
        raise ValueError("Invalid durable scheduler backoff map")
    values["_dispatch_generation_action_ready_monotonic"] = {
        key: rebase_deadline(deadline) for key, deadline in ready.items()
    }
    values["_falsification_backend_timeout_recycle_retry_monotonic"] = rebase_deadline(
        values.get("_falsification_backend_timeout_recycle_retry_monotonic", 0.0)
    )
    if any(key in _RUNTIME_FIELDS or field_is_runtime_capability(key) for key in values):
        raise ValueError("checkpoint cannot restore runtime capabilities")
    if set(values) & set(data["scheduler"]["session_state"]):
        raise ValueError("duplicate session fields overlap scheduler authority")
    saved_context = {key: conversation.get(key) for key in _IDENTITY_CONV_FIELDS}
    if _digest(saved_context) != expected_identity["context_hash"]:
        raise ValueError("checkpoint conversation changed its environment identity")
    if str(data["dossier"].get("root_statement") or "") != session.conv.goal_statement:
        raise ValueError("checkpoint dossier target identity mismatch")

    # Prepare every bound mutable object before an action synchronizer can
    # write into it. Invalid later graph data must leave the live runtime alone.
    staged = copy.copy(verifier_view)
    staged.conv = copy.copy(session.conv)
    staged.conv.__dict__ = copy.deepcopy(conversation)
    staged.dossier = ProofDossier._from_execution_record_for_reverification(data["dossier"])
    graph = staged.dossier.proof_graph
    saved_state = data["proof_state"]
    if (saved_state is None) != (session.proof_state is None):
        raise ValueError("checkpoint proof-state binding identity mismatch")
    staged.proof_state = (ProofSearchState.from_execution_record(
        saved_state, graph=graph, theorem_name=staged.dossier.theorem_name,
        root_statement=session.conv.goal_statement,
    ) if saved_state is not None else None)
    # Action-owned provider cursors authenticate against saved formal evidence
    # and selected-work context. Install those values into the private view
    # before its scheduler synchronizers validate any continuation.
    for key, value in values.items():
        setattr(staged, key, value)
    memo = {id(session): staged, id(session.conv): staged.conv,
            id(session.dossier): staged.dossier, id(session.dossier.proof_graph): graph}
    if session.proof_state is not None:
        memo[id(session.proof_state)] = staged.proof_state
    for key, value in vars(session).items():
        if key in _RUNTIME_FIELDS or field_is_runtime_capability(key):
            memo.setdefault(id(value), value)
    staged.actions = []
    for action in session.actions:
        cloned_action = copy.copy(action)
        memo[id(action)] = cloned_action
        for key, value in vars(action).items():
            if field_is_runtime_capability(key):
                memo.setdefault(id(value), value)
        cloned_action.__dict__ = copy.deepcopy(vars(action), memo)
        staged.actions.append(cloned_action)
    staged.recorder = staged.on_event = staged.checkpoint_registry = None
    apply_scheduler_snapshot(staged, data["scheduler"], allow_local_execution_cursors=False)
    research_governor_coverage = _validated_research_governor_coverage(
        data.get("native_research_governor_coverage", {
            "by_clock": {}, "legacy_elapsed_s": staged.run_governor_elapsed_s,
        }),
        float(staged.run_governor_elapsed_s or 0.0),
    )
    # Enrich the same private dossier/graph that owns the validated cursors.
    # Preparing a second dossier and copying only root receipts would discard
    # fresh typed helper evidence and its corresponding visibility metadata.
    await _prepare_dossier(
        verifier_view, data["dossier"], staged_dossier=staged.dossier,
        context_is_current=verification_context_is_current,
    )
    _release_obsolete_negation_conflict(staged)
    from ensemble_prover.mini_accepted_progress import validate_restored_acceptance_records

    validate_restored_acceptance_records(staged, checkpoint_monotonic=clock["monotonic_s"])
    if not staged.dossier.final_proof:
        staged.dossier.clear_solved()
    if staged.proof_state is not None:
        staged.proof_state.reconcile_with_dossier(staged.dossier)
        # Reconciliation can annotate an already-open root. Preserve the
        # exact saved cognition when that redundant label was absent, while
        # retaining every proof/status repair and every explicit saved label.
        saved_graph = data["dossier"]["proof_graph"]
        saved_root = next((node for node in saved_graph["nodes"]
                           if node["node_id"] == saved_graph["root_node_id"]), None)
        graph_root = graph.nodes.get(graph.root_node_id)
        state_root = staged.proof_state.nodes.get(staged.proof_state.root_node_id)
        if (saved_root is not None and saved_root["status"] == "open"
                and "proof_state_root_status" not in saved_root["metadata"]
                and graph_root is not None and graph_root.status == "open"
                and state_root is not None and state_root.status == "open"
                and not staged.dossier.final_proof
                and graph_root.metadata.get("proof_state_root_status") == "open"):
            graph_root.metadata.pop("proof_state_root_status")
    if bool(getattr(staged, "root_finalized", False)) != bool(staged.dossier.final_proof):
        raise ValueError("checkpoint root authority and scheduler status disagree")
    (published_values, published_budgets, published_conversation,
     published_dossier, published_graph, published_proof_state,
     published_actions) = _prepare_bound_publication(session, staged)
    # Runtime handles stay outside staging and come only from the destination.
    # Never copy an old parent's authority or restore its transaction state.
    published_conversation.update({
        key: value for key, value in vars(session.conv).items()
        if key in _CONVERSATION_RUNTIME_FIELDS
    })

    # No awaits follow publication. Preserve all objects bound by factory
    # callbacks while installing independently prepared value state.
    if verifier_view is not session:
        set_active = getattr(session.searcher, "set_active_bundle_ids", None)
        if callable(set_active):
            try:
                set_active(verifier_view.theory_imported_bundle_ids)
            except BaseException:
                set_active(session.theory_imported_bundle_ids)
                raise
    # The private scheduler already validated and synchronized all cursors.
    # Calling it again on the fresh runtime would authenticate saved lanes
    # against its old context and could fail after retrieval was published.
    live_graph = session.dossier.proof_graph
    live_graph.__dict__.clear()
    live_graph.__dict__.update(published_graph)
    session.dossier.__dict__.clear()
    session.dossier.__dict__.update(published_dossier)
    if session.proof_state is not None:
        session.proof_state.__dict__.clear()
        session.proof_state.__dict__.update(published_proof_state)
    session.conv.__dict__.clear()
    session.conv.__dict__.update(published_conversation)
    for action, action_values in zip(session.actions, published_actions, strict=True):
        action.__dict__.clear()
        action.__dict__.update(action_values)
    session.__dict__.update(published_values)
    session.budgets = published_budgets
    if verifier_view is not session:
        if not hasattr(session, "_checkpoint_initial_theory_context_hash"):
            session._checkpoint_initial_theory_context_hash = data["theory_context"]["initial_context_hash"]
        session.theory_context_pair = verifier_view.theory_context_pair
        session.theory_snapshot = verifier_view.theory_snapshot
    session._run_governor_last_tick_monotonic = time.monotonic()
    session._native_research_governor_clock = {
        "identity": uuid.uuid4().hex,
        "restored_elapsed_s": research_governor_coverage["legacy_elapsed_s"],
        "coverage_by_clock": research_governor_coverage["by_clock"],
    }
