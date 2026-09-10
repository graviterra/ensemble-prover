"""Record and coordinate mathematical research with revision-bound evidence."""

from __future__ import annotations

import argparse
import json
import sqlite3
import sys
from pathlib import Path
from typing import Any, Sequence

from .model import ClaimSpec, load_json, object_fields
from .scheduler import ResearchScheduler
from .store import ResearchStore


_SUBMISSIONS = {
    "add-evidence": (
        "add_evidence",
        "claim_id",
        {"claim_id", "expected_revision", "kind", "author", "artifact_ids", "details"},
    ),
    "add-review": (
        "add_review",
        "claim_id",
        {
            "claim_id",
            "expected_revision",
            "evidence_id",
            "reviewer",
            "verdict",
            "rationale",
        },
    ),
    "assess-obligation": (
        "assess_contribution",
        "parent_id",
        {
            "parent_id",
            "expected_revision",
            "obligation_id",
            "expected_supplier_revision",
            "reviewer",
            "decision",
            "costs_acceptable",
            "rationale",
        },
    ),
    "record-operation": (
        "record_operation",
        "claim_id",
        {"claim_id", "expected_revision", "outcome", "details"},
    ),
    "finish-assignment": (
        "finish_assignment",
        "assignment_id",
        {"assignment_id", "outcome", "details"},
    ),
    "assign": (
        "assign",
        "target_id",
        {
            "target_id",
            "assignment_id",
            "round_id",
            "worker",
            "question",
            "owned_output",
            "work_kind",
            "claim_id",
            "max_steps",
            "max_seconds",
        },
    ),
}

_OPTIONAL_FIELDS = {
    "add-review": {"supersedes_review_ids"},
    "assess-obligation": {
        "supersedes_contribution_ids",
        "expected_supplier_state_token",
    },
    "assign": {"additional_checks"},
}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    commands = parser.add_subparsers(dest="command", required=True)
    descriptions = {
        "init": "Create a new research ledger",
        "upgrade": "Explicitly upgrade a legacy ledger, preserving its records",
        "add-claim": "Add an exact research claim from JSON",
        "revise-claim": "Revise a claim and invalidate dependent assessments",
        "add-artifact": "Snapshot complete file bytes and return their SHA-256",
        "read-artifact": "Restore the exact bytes of a stored artifact",
        "add-evidence": "Record revision-bound mathematical evidence",
        "add-review": "Record an independent correctness review",
        "assess-obligation": "Assess a helper's contribution to an exact obligation",
        "record-operation": "Record an operational outcome without changing mathematics",
        "assign": "Create a bounded research assignment and its complete context",
        "finish-assignment": "Record assignment completion or operational failure",
        "show": "Show claims and their three separate assessments",
        "history": "Show immutable revisions and complete evidence history",
        "frontier": "Show consequential remaining obligations and research priorities",
        "assignments": "Show durable assignment packets",
        "export": "Export ledger records and artifact hashes as JSON",
    }
    for name, description in descriptions.items():
        command = commands.add_parser(name, help=description, allow_abbrev=False)
        command.add_argument("directory", type=Path)
        if name in _SUBMISSIONS or name in {
            "add-claim",
            "revise-claim",
            "add-artifact",
        }:
            command.add_argument("--file", type=Path, required=True)
        if name in {"revise-claim", "history", "frontier"}:
            command.add_argument("claim_id")
        if name == "show":
            command.add_argument("claim_id", nargs="?")
        if name == "revise-claim":
            command.add_argument("--expected-revision", type=int, required=True)
        if name == "add-artifact":
            command.add_argument("--name")
        if name == "read-artifact":
            command.add_argument("artifact_id")
            command.add_argument("--output", type=Path, required=True)
        if name == "export":
            command.add_argument("--output", type=Path)
    from .discovery_cli import register
    register(commands)
    return parser


def _read(path: Path) -> Any:
    return load_json(path.read_bytes().decode("utf-8"))


def _report(store: ResearchStore, claim_id: str) -> dict[str, Any]:
    with store.read_snapshot():
        return {
            **store.get_claim(claim_id),
            "assessment": store.assessment(claim_id),
            "progress": ResearchScheduler(store).progress(claim_id),
        }


def _dispatch(args: argparse.Namespace) -> Any:
    if args.command == "discovery":
        from .discovery_cli import dispatch
        return dispatch(args)
    with ResearchStore(
        args.directory, create=args.command == "init", upgrade=args.command == "upgrade"
    ) as store:
        if args.command == "init":
            return {"status": "initialized", "directory": str(args.directory.resolve())}
        if args.command == "upgrade":
            return {"status": "upgraded", "directory": str(args.directory.resolve())}
        if args.command == "add-claim":
            return store.create_claim(ClaimSpec.from_dict(_read(args.file)))
        if args.command == "revise-claim":
            return store.revise_claim(
                args.claim_id,
                ClaimSpec.from_dict(_read(args.file)),
                expected_revision=args.expected_revision,
            )
        if args.command == "add-artifact":
            content = args.file.read_bytes()
            digest = store.put_artifact(content, name=args.name or args.file.name)
            return {"artifact_id": digest, "size_bytes": len(content)}
        if args.command == "read-artifact":
            content = store.read_artifact(args.artifact_id)
            with args.output.open("xb") as output:
                output.write(content)
            return {"artifact_id": args.artifact_id, "output": str(args.output)}
        if args.command in _SUBMISSIONS:
            method, subject, fields = _SUBMISSIONS[args.command]
            data = object_fields(
                _read(args.file),
                fields | _OPTIONAL_FIELDS.get(args.command, set()),
                fields,
                args.command,
            )
            owner = ResearchScheduler(store) if args.command == "assign" else store
            subject_id = data.pop(subject)
            return getattr(owner, method)(subject_id, **data)
        if args.command == "show":
            with store.read_snapshot():
                if args.claim_id:
                    return _report(store, args.claim_id)
                return {
                    "claims": [
                        _report(store, item["claim_id"]) for item in store.list_claims()
                    ]
                }
        if args.command == "history":
            return store.history(args.claim_id)
        if args.command == "frontier":
            scheduler = ResearchScheduler(store)
            with store.read_snapshot():
                return {
                    "progress": scheduler.progress(args.claim_id),
                    "frontier": scheduler.frontier(args.claim_id),
                }
        if args.command == "assignments":
            return {"assignments": store.list_assignments()}
        if args.command == "export":
            result = store.export()
            if args.output is not None:
                with args.output.open("x", encoding="utf-8", newline="\n") as output:
                    json.dump(
                        result, output, ensure_ascii=False, allow_nan=False, indent=2
                    )
                    output.write("\n")
                return {"output": str(args.output)}
            return result
    raise ValueError("unknown command")


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        result = _dispatch(args)
        print(json.dumps(result, ensure_ascii=False, allow_nan=False, indent=2))
        if args.command == "discovery" and args.discovery_command == "run":
            if result["status"] not in {"idle", "budget_exhausted", "deadline_exhausted"}:
                return 2
        return 0
    except (ValueError, OSError, KeyError, sqlite3.Error) as exc:
        print(f"research_claims: {exc}", file=sys.stderr)
        return 2
    except RecursionError:
        print(
            "research_claims: ledger data exceeds supported JSON nesting",
            file=sys.stderr,
        )
        return 2
    except KeyboardInterrupt:
        print("research_claims: interrupted; saved results and dispatch reservations retained", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
