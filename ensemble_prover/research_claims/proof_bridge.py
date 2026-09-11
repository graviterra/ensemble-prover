"""Connect durable research jobs to the existing formalizer and Mini Prover.

Only a freshly checked export can create a proof receipt. Research arguments,
review votes and provider output never constitute that receipt.
"""

from __future__ import annotations

import hashlib
import math
import os
import re
import tempfile
import time
from contextlib import AsyncExitStack
from dataclasses import asdict
from pathlib import Path
from types import TracebackType
from typing import Any, Callable, Literal

from .model import INTERNAL_JSON_NESTING, json_text, load_json, positive_int
from .store import RevisionConflict


class _ProofExitStack(AsyncExitStack):
    """Close every resource without replacing cancellation or a proof failure."""

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> Literal[False]:
        try:
            await super().__aexit__(exc_type, exc, traceback)
        except BaseException:
            if exc is None:
                raise
            # AsyncExitStack has attempted every callback. Let the with
            # statement propagate its original exception, not a close error.
            return False
        # This stack owns resources, never permission to suppress a failure.
        return False


def configure(
    project_path: Path | None,
    *,
    imports: tuple[str, ...] = (),
    proof_quantum_s: float = 600,
    formalization_steps: int = 8,
    lean_timeout_s: float = 300,
) -> dict[str, Any] | None:
    if project_path is None:
        if imports:
            raise ValueError("trusted imports require a closed-loop project path")
        return None
    from ..formalization.environment import EnvironmentSnapshot

    positive_int(formalization_steps, "formalization_steps")
    for value in (proof_quantum_s, lean_timeout_s):
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value <= 0
        ):
            raise ValueError("proof and Lean timeouts must be finite and positive")
    environment = EnvironmentSnapshot.capture(project_path, trusted_imports=imports)
    return {
        "schema": 1,
        "environment": environment.to_dict(),
        "proof_quantum_s": proof_quantum_s,
        "formalization_steps": formalization_steps,
        "lean_timeout_s": lean_timeout_s,
    }


def configuration(run: dict[str, Any]) -> dict[str, Any] | None:
    if "closed_loop" not in run:
        raise ValueError(
            "missing closed-loop authorization; explicit ledger upgrade required"
        )
    config = run["closed_loop"]
    if config is None:
        return None
    from ..formalization.environment import EnvironmentSnapshot

    if (
        not isinstance(config, dict)
        or set(config)
        != {
            "schema",
            "environment",
            "proof_quantum_s",
            "formalization_steps",
            "lean_timeout_s",
        }
        or type(config["schema"]) is not int
        or config["schema"] != 1
    ):
        raise ValueError("invalid closed-loop authorization")
    positive_int(config["formalization_steps"], "formalization_steps")
    for key in ("proof_quantum_s", "lean_timeout_s"):
        value = config[key]
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value <= 0
        ):
            raise ValueError("invalid closed-loop timeout")
    EnvironmentSnapshot.from_dict(config["environment"])
    return config


def _campaign_path(store: Any, job: dict[str, Any]) -> Path:
    if not re.fullmatch(r"job-[0-9a-f]{32}", job["job_id"]):
        raise ValueError("invalid formalization program identity")
    return store.directory.resolve() / "campaigns" / job["job_id"]


def handoff_bundle(store: Any, job: dict[str, Any]) -> dict[str, Any]:
    run = store.run_record()
    aid = job["handoff_artifact"]
    if aid not in run["handoffs"]:
        raise ValueError("unrecorded proof handoff")
    bundle = load_json(
        store.read_artifact(aid).decode(), max_depth=INTERNAL_JSON_NESTING
    )
    if (
        bundle.get("schema") != 2
        or bundle["claim"]["claim_id"] != job["claim_id"]
        or bundle["claim"]["revision"] != job["revision"]
    ):
        raise ValueError("proof handoff binding mismatch")
    if job["polarity"] not in {"prove", "refute"}:
        raise ValueError("invalid proof polarity")
    if store.get_claim(job["claim_id"]) != bundle["claim"]:
        raise RevisionConflict("formalization claim changed")
    if store.get_claim(run["target_id"])["spec"] != bundle["original_target"]:
        raise RevisionConflict("original research target changed")
    for saved in bundle["ledger"]["claims"]:
        if store.get_claim(saved["claim_id"]) != {
            key: saved[key] for key in ("claim_id", "revision", "spec")
        }:
            raise RevisionConflict("a shared handoff claim changed")
    return bundle


def binding(store: Any, job: dict[str, Any]) -> dict[str, Any]:
    config = configuration(store.run_record())
    if config is None:
        raise ValueError("closed-loop proving is not authorized")
    bundle = handoff_bundle(store, job)
    contract = bundle["claim"]["spec"]["contract"]
    goal = (
        json_text(contract)
        if job["polarity"] == "prove"
        else json_text(
            {
                "objective": "Prove the logical negation of this exact original proposition, retaining its domain and quantifier scope; a counterexample must satisfy the original hypotheses and violate its conclusion.",
                "original_proposition": contract,
            }
        )
    )
    return {
        "schema": 1,
        "handoff_artifact": job["handoff_artifact"],
        "claim": bundle["claim"],
        "polarity": job["polarity"],
        "environment_id": config["environment"]["id"],
        "goal": goal,
    }


def _check_campaign(
    store: Any, job: dict[str, Any], campaign_store: Any
) -> dict[str, Any]:
    expected = binding(store, job)
    metadata = campaign_store.get_metadata()
    root = campaign_store.get_task(metadata["root_id"])
    if (
        metadata.get("research_binding") != expected
        or metadata.get("goal") != expected["goal"]
        or root.description != expected["goal"]
        or metadata["environment"]["id"] != expected["environment_id"]
    ):
        raise ValueError(
            "campaign target or environment differs from its research binding"
        )
    return expected


def validate_receipt(store: Any, job: dict[str, Any], receipt: Any) -> dict[str, Any]:
    """Revalidate files and the frozen target; a stored boolean grants no trust."""
    from ..formalization.lean import ModuleArtifact, ModuleCompiler
    from ..formalization.environment import EnvironmentSnapshot
    from ..formalization.store import ProjectStore

    if not isinstance(receipt, dict) or set(receipt) != {
        "binding",
        "export_name",
        "files",
        "root_result",
    }:
        raise ValueError("missing or invalid verified export receipt")
    directory = _campaign_path(store, job)
    with ProjectStore(directory) as campaign:
        expected = _check_campaign(store, job, campaign)
        if receipt["binding"] != expected:
            raise ValueError("verified export binding changed")
        root = campaign.get_task(campaign.get_metadata("root_id"))
        if (
            root.state != "verified"
            or root.result != receipt["root_result"]
            or not root.result
            or root.result.get("kind") != "theorem"
        ):
            raise ValueError("verified export root changed")
        frozen = root.session.get("frozen_statement", {})
        if (
            frozen.get("name") != root.result.get("name")
            or frozen.get("statement") != root.result.get("statement")
            or frozen.get("review_verdict", {}).get("decision") != "accept"
        ):
            raise ValueError("verified export lacks the reviewed frozen target")
        if not isinstance(receipt["export_name"], str) or not re.fullmatch(
            r"verified-[0-9a-f]{32}", receipt["export_name"]
        ):
            raise ValueError("invalid export location")
        output = directory / receipt["export_name"]
        if (
            not isinstance(receipt["files"], dict)
            or "export.json" not in receipt["files"]
            or "Root.lean" not in receipt["files"]
        ):
            raise ValueError("incomplete verified export receipt")
        for name, digest in receipt["files"].items():
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("invalid export file path")
            path = output / relative
            if (
                path.is_symlink()
                or not path.is_file()
                or path.resolve().is_relative_to(output.resolve()) is False
                or hashlib.sha256(path.read_bytes()).hexdigest() != digest
            ):
                raise ValueError("verified export artifact changed")
        environment = EnvironmentSnapshot.from_dict(
            campaign.get_metadata("environment")
        )
        environment.validate()
        compiler = ModuleCompiler(
            environment.project_path,
            directory / "modules",
            trusted_imports=environment.trusted_imports,
            environment=environment,
        )
        compiler.validate_closure([ModuleArtifact.from_dict(root.result["artifact"])])
    return receipt


class ProofBridge:
    def __init__(
        self,
        store: Any,
        client_factory: Callable[[str, str], Any],
        *,
        mini_options: dict[str, Any] | None = None,
        owns_clients: bool = False,
    ):
        self.store = store
        self.client_factory = client_factory
        self.mini_options = dict(mini_options or {})
        # Embedded callers may lend shared clients; the CLI instead supplies
        # fresh clients whose lifetime is exactly one proof interval.
        self.owns_clients = owns_clients

    def _initialize(self, job: dict[str, Any], directory: Path) -> None:
        from ..formalization.documents import _sync_directory
        from ..formalization.environment import EnvironmentSnapshot
        from ..formalization.store import ProjectStore
        from .discovery import create_formalization_handoff

        expected = binding(self.store, job)
        if directory.exists():
            with ProjectStore(directory) as campaign:
                _check_campaign(self.store, job, campaign)
            return
        config = configuration(self.store.run_record())
        assert config is not None
        environment = EnvironmentSnapshot.from_dict(config["environment"])
        environment.validate()
        directory.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix=".initialize-", dir=directory.parent
        ) as temporary:
            stage = Path(temporary) / "campaign"
            create_formalization_handoff(
                self.store.directory,
                job["handoff_artifact"],
                output=stage,
                project_path=environment.project_path,
                imports=environment.trusted_imports,
            )
            with ProjectStore(stage) as campaign:
                if job["polarity"] == "refute":
                    # No request or reviewed target exists yet. Set the explicit
                    # negation goal before the formalizer/reviewer first sees it.
                    root = campaign.get_task(campaign.get_metadata("root_id"))
                    campaign.revise(root.id, description=expected["goal"])
                    campaign.set_metadata("goal", expected["goal"])
                campaign.set_metadata("research_binding", expected)
                _check_campaign(self.store, job, campaign)
            os.rename(stage, directory)
            _sync_directory(directory.parent)

    def _feedback(self, campaign_store: Any, result: dict[str, Any]) -> dict[str, Any]:
        tasks, artifacts = [], {}
        after = ""
        while page := campaign_store.list_tasks(after=after):
            for task in page:
                tasks.append(asdict(task))
                cursor = 0
                while events := campaign_store.events(task.id, after=cursor):
                    for event in events:
                        for key, value in event["payload"].items():
                            if key.endswith("_blob") and isinstance(value, str):
                                aid = self.store.put_artifact(
                                    campaign_store.read_blob(value),
                                    name=f"campaign-{key}.json",
                                )
                                artifacts[aid] = {
                                    "artifact_id": aid,
                                    "task_id": task.id,
                                    "event_id": event["id"],
                                    "kind": event["kind"],
                                    "field": key,
                                }
                    cursor = events[-1]["id"]
            after = page[-1].id
        return {
            "campaign_status": result,
            "tasks": tasks,
            "complete_artifacts": list(artifacts.values()),
            "semantic_status": "machine_reviewed_not_certified",
        }

    def feedback(self, job: dict[str, Any]) -> dict[str, Any]:
        """Recover exact stored diagnostics after a cancelled proof quantum."""
        from ..formalization.store import ProjectStore

        with ProjectStore(_campaign_path(self.store, job)) as campaign:
            _check_campaign(self.store, job, campaign)
            return self._feedback(campaign, {"status": "paused"})

    async def advance(self, job: dict[str, Any]) -> dict[str, Any]:
        from ..formalization.campaign import Campaign
        from ..formalization.environment import EnvironmentSnapshot
        from ..formalization.export import export_project
        from ..formalization.lean import ModuleCompiler
        from ..formalization.prover import MiniProver

        config = configuration(self.store.run_record())
        assert config is not None
        directory = _campaign_path(self.store, job)
        self._initialize(job, directory)
        bundle = handoff_bundle(self.store, job)
        environment = EnvironmentSnapshot.from_dict(config["environment"])
        required = {
            "claim": bundle["claim"],
            "original_target": bundle["original_target"],
            "proof_plan": bundle["proof_plan"],
            "polarity": job["polarity"],
            "sources": {
                name: self.store.read_artifact(aid).decode()
                for name, aid in bundle["sources"].items()
            },
            "artifact_inventory": bundle["ledger"]["artifacts"],
            "polarity_policy": "Translate the exact claim for prove. For refute, independently check that the formal target is the logical negation of the original claim, including domain, hypotheses and quantifier scope. Neither research text nor proof plan may change that target.",
        }
        async with _ProofExitStack() as cleanup:
            compiler = ModuleCompiler(
                environment.project_path,
                directory / "modules",
                timeout_s=config["lean_timeout_s"],
                trusted_imports=environment.trusted_imports,
                environment=environment,
            )
            cleanup.push_async_callback(compiler.close)
            run = self.store.run_record()
            remaining = max(0, run["deadline"] - time.time())
            stop_reason = self.store.stop_reason(run)
            local_only = stop_reason in {"deadline_exhausted", "budget_exhausted"}
            roles = ("formalizer", "semantic_reviewer", "prover", "refiner")
            clients: dict[str, Any] = dict.fromkeys(roles)
            prover = None
            if not local_only:
                for role in roles:
                    client = self.client_factory(role, job["job_id"] + ":" + role)
                    if self.owns_clients:
                        cleanup.push_async_callback(client.close)
                    if not getattr(
                        client, "supports_transport_dispatch_authorization", False
                    ):
                        raise ValueError(
                            "closed-loop clients require transport authorization"
                        )
                    clients[role] = client
                prover = MiniProver(
                    environment.project_path,
                    directory / "modules",
                    clients["prover"],
                    clients["refiner"],
                    options={
                        **self.mini_options,
                        "lean_timeout_s": config["lean_timeout_s"],
                        "run_wall_clock_budget_s": min(
                            remaining, config["proof_quantum_s"]
                        ),
                    },
                )
                cleanup.push_async_callback(prover.close)
            campaign = cleanup.enter_context(
                Campaign(
                    directory,
                    formalizer=clients["formalizer"],
                    reviewer=clients["semantic_reviewer"],
                    compiler=compiler,
                    prover=prover,
                    required_context=required,
                )
            )
            _check_campaign(self.store, job, campaign.store)
            result = campaign.status()
            if result["status"] != "proved":
                # Already-produced source may still need local admission after
                # authorization ends. This mode cannot start models or Mini;
                # it preserves the frozen source binding and fresh Lean checks.
                result = await campaign.run(
                    max_steps=config["formalization_steps"], local_only=local_only
                )
                if local_only and result["status"] != "proved":
                    result.setdefault("stop_reason", stop_reason)
            feedback = self._feedback(campaign.store, result)
            if result["status"] != "proved":
                return {
                    "status": "incomplete",
                    "stop_reason": result.get("stop_reason"),
                    "feedback": feedback,
                }
            _check_campaign(self.store, job, campaign.store)
            # A fresh, unique destination means crash leftovers are never
            # mistaken for authority and existing exports are never overwritten.
            import uuid

            output = directory / ("verified-" + uuid.uuid4().hex)
            await export_project(directory, output)
            _check_campaign(self.store, job, campaign.store)
            receipt = {
                "binding": binding(self.store, job),
                "export_name": output.name,
                "files": {
                    str(path.relative_to(output)): hashlib.sha256(
                        path.read_bytes()
                    ).hexdigest()
                    for path in output.rglob("*")
                    if path.is_file()
                },
                "root_result": campaign.store.get_task(
                    campaign.store.get_metadata("root_id")
                ).result,
            }
            validate_receipt(self.store, job, receipt)
            return {"status": "proved", "receipt": receipt, "feedback": feedback}
