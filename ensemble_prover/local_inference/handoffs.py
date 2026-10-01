"""Preserve local authority when research exports an executable campaign."""

from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Iterator, Mapping

from .config import RoleSelection, load_private_worker_snapshot, resolve_run
from .errors import LocalInferenceError
from .network_policy import (
    apply_network_policy,
    current_network_policy,
    network_policy_scope,
    persist_network_policy,
    restore_network_policy,
)
from .roles import load_run_bundle, local_inference_binding, persist_local_inference
from .runtime import prepare_resources


@contextmanager
def formalization_handoff_scope(
    source: Path, run: Mapping[str, Any], output: Path, project_path: Path
) -> Iterator[None]:
    """Continue research with its exact deployments and conserved allocation.

    Research's generating role becomes the formalizer and prover; its reviewer
    remains the reviewer. A partial local/cloud pair needs explicit campaign
    role selection and cannot be converted through this implicit handoff.
    """
    from ..research_claims.discovery_store import provider_routes
    from ..workflow_roles import _preparation

    pair = provider_routes(run)
    local = "local" in pair or (source / "local_inference").exists()
    if not local:
        if run.get("offline") is True or (source / "network_policy.json").exists():
            raise LocalInferenceError("network_policy_marker_mismatch")
        yield
        return
    if pair != ("local", "local"):
        raise ValueError(
            "A mixed local/cloud research handoff requires explicit campaign roles. "
            "Initialize a campaign with the saved research artifacts and select "
            "--formalizer-provider, --reviewer-provider, and --prover-provider; "
            "the handoff will not choose cloud defaults."
        )
    parent = load_run_bundle(source)
    resolved = load_private_worker_snapshot(parent.snapshot)
    if set(resolved.roles) != {"research", "review"}:
        raise LocalInferenceError("unknown_role")
    if run.get("inference_policy", parent.inference_policy) != parent.inference_policy:
        raise LocalInferenceError("profile_conflict")
    for role, model_key in (("research", "model"), ("review", "review_model")):
        if run.get(model_key) != resolved.roles[role].model:
            raise LocalInferenceError("model_conflict")
    if run.get("offline") is True and not (source / "network_policy.json").is_file():
        raise LocalInferenceError("network_policy_marker_mismatch")
    selections = []
    for target, donor in (
        ("formalizer", "research"), ("reviewer", "review"), ("prover", "research")
    ):
        selected = resolved.roles[donor]
        selections.append(RoleSelection(
            target, selected.deployment_id, selected.model,
            selected.reasoning_mode, selected.reasoning_effort,
        ))
    campaign = _preparation(
        resolve_run(resolved.document, selections, inference_policy=parent.inference_policy),
        inference_policy=parent.inference_policy,
        coordinator=parent.coordinator_root,
        budget_id=parent.budget_id,
    )
    # Reopen only: an exported continuation never replenishes the parent's grant.
    for role in campaign.roles:
        prepare_resources(local_inference_binding(campaign, role), allow_create=False)
    if output.exists() and any(output.iterdir()):
        raise ValueError("formalization handoff output already exists")
    with network_policy_scope(current_network_policy()):
        policy = restore_network_policy(source, parent)
        apply_network_policy(
            SimpleNamespace(network_policy=policy.mode, project_path=project_path),
            campaign, project_path,
        )
        # Publish policy before a runnable campaign database can exist. A
        # interrupted export therefore fails closed instead of choosing OpenAI.
        persist_local_inference(output, campaign, include_binding=True)
        persist_network_policy(output)
        yield
