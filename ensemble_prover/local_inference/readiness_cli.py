"""Operator commands for local readiness, recovery, and conformance.

``show`` reads a private snapshot and an optional saved receipt. It does not
contact an endpoint or create a budget. ``probe`` is the explicit check and
owns its finite setup ledger. ``inspect``, ``reconcile``, and ``settle-wall``
read existing coordinator and budget directories. Paths belong on this operator
command; a browser request cannot supply them.
"""

from __future__ import annotations

import argparse
import asyncio
from pathlib import Path
import sys
import time
from typing import Any, Sequence

from .config import load_private_worker_snapshot
from .errors import LocalInferenceError
from .readiness import (
    inspect_resources,
    project_readiness,
    reconcile_unresolved,
    run_conformance_probe,
    settle_clear_response,
)
from .strictload import canonical_json, read_json_object

_MAX_BYTES = 1024 * 1024


def main(argv: Sequence[str] | None = None, *, probe: Any = None) -> int:
    parser = argparse.ArgumentParser(prog="local-inference-readiness")
    commands = parser.add_subparsers(dest="command", required=True)
    show = commands.add_parser("show")
    show.add_argument("--snapshot", type=Path, required=True)
    show.add_argument("--receipt", type=Path)
    show.add_argument("--now", type=int)
    listed = commands.add_parser("inspect")
    _coordinator(listed)
    listed.add_argument("--group", required=True)
    listed.add_argument("--budget-root", type=Path)
    reconcile = commands.add_parser("reconcile")
    _coordinator(reconcile)
    reconcile.add_argument("--dispatch-id", required=True)
    reconcile.add_argument("--operator-id", required=True)
    reconcile.add_argument("--budget-root", type=Path, required=True)
    reconcile.add_argument(
        "--reason",
        choices=("retain_unknown", "completion_evidence_lost"),
        required=True,
    )
    reconcile.add_argument("--now", type=int)
    settle = commands.add_parser("settle-wall")
    _coordinator(settle)
    settle.add_argument("--dispatch-id", required=True)
    settle.add_argument("--budget-root", type=Path, required=True)
    settle.add_argument("--milliseconds", type=int, required=True)
    settle.add_argument("--wall-receipt", required=True)
    settle.add_argument("--now", type=int)
    check = commands.add_parser("probe")
    check.add_argument("--snapshot", type=Path, required=True)
    check.add_argument("--role", required=True)
    check.add_argument("--coordinator-root", type=Path, required=True)
    check.add_argument("--budget-root", type=Path, required=True)
    check.add_argument("--budget-id", required=True)
    check.add_argument("--coordinator-id")
    check.add_argument("--max-output-tokens", type=int, required=True)
    check.add_argument("--max-dispatches", type=int, required=True)
    check.add_argument("--max-requested-output-tokens", type=int, required=True)
    check.add_argument("--max-observed-request-wall-s", type=int, required=True)
    check.add_argument("--request-timeout-s", type=int, required=True)
    check.add_argument("--now", type=int, required=True)
    check.add_argument("--expires-at", type=int, required=True)
    check.add_argument("--require", action="append", default=None)
    try:
        args = parser.parse_args(list(argv) if argv is not None else None)
        payload = _run(args, probe)
    except LocalInferenceError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(canonical_json(payload))
    if args.command == "probe" and payload.get("result") != "bounded_pass":
        return 1
    return 0


def _coordinator(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--coordinator-root", type=Path, required=True)
    parser.add_argument("--installation-id", required=True)
    parser.add_argument("--scope-id", required=True)


def _run(args: argparse.Namespace, probe: Any) -> dict[str, Any]:
    now = int(time.time()) if getattr(args, "now", None) is None else args.now
    if args.command == "show":
        snapshot = read_json_object(
            args.snapshot, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
        )
        receipt = (
            None
            if args.receipt is None
            else read_json_object(
                args.receipt, max_bytes=_MAX_BYTES, corrupt_code="invalid_field"
            )
        )
        return project_readiness(
            load_private_worker_snapshot(snapshot), now_s=now, receipt=receipt
        )
    if args.command == "inspect":
        return inspect_resources(
            coordinator_root=args.coordinator_root,
            installation_id=args.installation_id,
            scope_id=args.scope_id,
            group=args.group,
            budget_root=args.budget_root,
        )
    if args.command == "reconcile":
        return reconcile_unresolved(
            coordinator_root=args.coordinator_root,
            budget_root=args.budget_root,
            installation_id=args.installation_id,
            scope_id=args.scope_id,
            dispatch_id=args.dispatch_id,
            operator_id=args.operator_id,
            reason=args.reason,
            now_s=now,
        )
    if args.command == "settle-wall":
        return settle_clear_response(
            coordinator_root=args.coordinator_root,
            budget_root=args.budget_root,
            installation_id=args.installation_id,
            scope_id=args.scope_id,
            dispatch_id=args.dispatch_id,
            milliseconds=args.milliseconds,
            wall_receipt=args.wall_receipt,
            now_s=now,
        )
    runner = probe if probe is not None else _probe
    return runner(
        snapshot=read_json_object(
            args.snapshot, max_bytes=_MAX_BYTES, corrupt_code="snapshot_mismatch"
        ),
        role=args.role,
        coordinator_root=args.coordinator_root,
        budget_root=args.budget_root,
        budget_id=args.budget_id,
        coordinator_id=args.coordinator_id,
        max_output_tokens=args.max_output_tokens,
        max_dispatches=args.max_dispatches,
        max_requested_output_tokens=args.max_requested_output_tokens,
        max_observed_request_wall_s=args.max_observed_request_wall_s,
        request_timeout_s=args.request_timeout_s,
        now_s=args.now,
        expires_at_s=args.expires_at,
        allow_create=True,
        required_controls=tuple(args.require or ("native_tool_call",)),
    )


def _probe(**kwargs: Any) -> dict[str, Any]:
    import httpx

    budget_id = kwargs.pop("budget_id")
    spec = {
        "snapshot": kwargs.pop("snapshot"),
        "role": kwargs.pop("role"),
        "coordinator_root": str(kwargs.pop("coordinator_root")),
        "budget_root": str(kwargs.pop("budget_root")),
        "budget_id": budget_id,
    }
    coordinator_id = kwargs.pop("coordinator_id")
    if coordinator_id is not None:
        spec["coordinator_id"] = coordinator_id

    async def run() -> dict[str, Any]:
        async with httpx.AsyncClient(
            trust_env=False, follow_redirects=False, timeout=kwargs["request_timeout_s"]
        ) as client:
            return await run_conformance_probe(spec, http_client=client, **kwargs)

    return asyncio.run(run())


if __name__ == "__main__":
    raise SystemExit(main())
