"""Construct optional independent native research transports using Mini policy."""

from __future__ import annotations

from typing import Any


def validate_research_inference_policy(args: Any) -> None:
    """Apply transport restrictions before setup or any provider preflight."""
    if getattr(args, "inference_policy", "mixed") == "local-only" and any(
        getattr(args, role + "_provider", None) not in (None, "", "local")
        for role in ("research", "research_review")
    ):
        from .local_inference.errors import LocalInferenceError

        raise LocalInferenceError("hosted_upstream_forbidden")


def validate_research_role_config(args: Any) -> None:
    """Reject inconsistent optional roles before publishing or opening clients."""
    validate_research_inference_policy(args)
    for role in ("research", "research_review"):
        provider = getattr(args, role + "_provider", None)
        model = getattr(args, role + "_model", None)
        if model and not provider:
            raise ValueError(f"--{role.replace('_', '-')}-model requires its provider option")
        if provider and not getattr(args, "autonomous_research", True):
            raise ValueError("Independent research roles require autonomous research")


def build_research_role_clients(
    args: Any, clients: dict[str, Any], *, provider_lane_health_registry: Any = None,
) -> None:
    """Publish each owned client immediately so partial setup can be cleaned up."""
    from .mini_prover import (
        _apply_reasoning_cli_override, _apply_subscription_control_requirements,
        _make_mini_role_client, _make_role_cfg, _reasoning_role_cli_settings,
        _resolve_llm_request_timeout_setting,
    )

    validate_research_role_config(args)
    for role in ("research", "research_review"):
        provider = getattr(args, role + "_provider", None)
        if not provider:
            continue
        timeout, disabled = _resolve_llm_request_timeout_setting(
            getattr(args, "llm_request_timeout_s", None), role_name=role,
        )
        cfg = _make_role_cfg(
            provider, getattr(args, role + "_model", None), role_name=role,
            timeout_s=getattr(args, "llm_timeout_s", None),
            llm_deadline_policy=getattr(args, "llm_deadline_policy", "soft"),
            request_timeout_s=timeout, request_timeout_disabled=disabled, cli_args=args,
        )
        _apply_subscription_control_requirements(args, cfg, role_name=role)
        mode, effort = _reasoning_role_cli_settings(args, role)
        _apply_reasoning_cli_override(cfg, mode=mode, effort=effort)
        cfg.codex_binary = getattr(args, "codex_bin", "codex")
        cfg.claude_code_binary = getattr(args, "claude_code_bin", "claude")
        cfg.cursor_binary = getattr(args, "cursor_bin", "agent")
        clients[role] = _make_mini_role_client(
            cfg, provider_lane_health_registry=provider_lane_health_registry,
        )
