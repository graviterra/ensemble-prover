"""Start or resume integrated research with one run directory argument."""

from __future__ import annotations

import argparse
from contextlib import nullcontext
import json
import math
from pathlib import Path
import shlex
import sqlite3
import sys
import tempfile
from typing import Any, Sequence

from .research_claims.cli import main as research_main


DEFAULT_HOURS = 4.0
DEFAULT_REQUESTS = 200
REPOSITORY = Path(__file__).resolve().parents[1]

_ACTION_LABELS = {
    "read_artifact": "Read source",
    "read_claim": "Read claim",
    "search_source": "Searched saved sources",
    "read_source_page": "Read source page",
    "record_note": "Saved research note",
    "submit": "Submitted research finding",
    "investigate": "Started another investigation",
    "formalize": "Queued formalization",
    "continue_formalization": "Resumed formalization",
    "research_reorientation": "Independent review chose a new investigation",
    "review": "Completed independent argument review",
    "strategy_review": "Completed strategy review",
    "alternative_review": "Completed alternative investigation review",
    "progress_review": "Completed progress review",
    "implication_review": "Completed implication review",
    "report_investigation": "Reported investigation results",
    "request_strategy_review": "Requested independent strategy review",
    "record_bottleneck": "Recorded an exact bottleneck",
    "experiment": "Processed finite experiment request",
    "finish": "Finished investigation",
    "wait": "Waiting for related work",
}


def _count(value: Any) -> bool:
    return type(value) is int and 0 <= value <= 10**15


def _memory_counts(store: Any, reference: Any) -> tuple[int, int] | None:
    """Read compact counters, with a size-bounded fallback for older indexes."""
    if not isinstance(reference, dict) or reference.get("version") != 1:
        return None
    reads, repeats = reference.get("retrievals"), reference.get("repeated_retrievals")
    if _count(reads) and _count(repeats) and repeats <= reads:
        return reads, repeats
    artifact_id = reference.get("artifact_id")
    if not isinstance(artifact_id, str):
        return None
    row = store._connection.execute(
        "SELECT length(content) FROM artifacts WHERE artifact_id = ?", (artifact_id,)
    ).fetchone()
    if row is None or row[0] > 1_000_000:
        return None
    try:
        archived = json.loads(store.read_artifact(artifact_id))
        if not isinstance(archived, dict) or archived.get("version") != 1:
            return None
        reads, repeats = archived.get("retrievals"), archived.get("repeated_retrievals")
    except (ValueError, UnicodeError):
        return None
    return (reads, repeats) if _count(reads) and _count(repeats) and repeats <= reads else None


def observational_progress(store: Any) -> dict[str, Any]:
    """Read operational metadata only; this function confers no proof authority."""
    with nullcontext() if store._connection.in_transaction else store.read_snapshot():
        # SQL projections avoid decoding messages, source pages or old embedded
        # action histories. Only the latest applied action event is consulted.
        rows = list(store._connection.execute(
            "SELECT job_id, status, json_extract(record, '$.role') AS role, "
            "json_extract(record, '$.turn') AS turn, "
            "json_extract(record, '$.research_memory') AS memory, "
            "json_extract(record, '$.research_control.reason') AS reason, "
            "json_extract(record, '$.research_reorientation_for') AS reorientation, "
            "json_extract(record, '$.research_successor') AS successor, "
            "json_extract(record, '$.research_directive.decision') AS decision "
            "FROM discovery_jobs"
        ))
        by_id = {row["job_id"]: row for row in rows}
        totals = {"completed": 0, "pending": 0, "inconclusive": 0}
        result: dict[str, Any] = {
            "last_action": None, "retrievals": 0, "repeated_retrievals": 0,
            "indexed_retrievals": 0, "indexed_repeated_retrievals": 0,
            "unindexed_jobs": 0, "reviews": dict(totals),
            "reorientations": dict(totals), "formalization_jobs": 0,
        }
        for row in rows:
            if row["role"] in {"research", "review"}:
                reference = json.loads(row["memory"]) if row["memory"] else None
                counts = _memory_counts(store, reference)
                if counts is not None:
                    result["indexed_retrievals"] += counts[0]
                    result["indexed_repeated_retrievals"] += counts[1]
                elif row["turn"]:
                    result["unindexed_jobs"] += 1
            if row["role"] == "formalization":
                result["formalization_jobs"] += 1
            elif row["role"] == "review":
                phase = "pending"
                if row["status"] in {"finished", "stale", "superseded"}:
                    phase = "completed" if row["status"] == "finished" and not row["reason"] else "inconclusive"
                    if row["reorientation"]:
                        successor = by_id.get(row["successor"])
                        if successor is None or successor["decision"] != "investigate":
                            phase = "inconclusive"
                result["reviews"][phase] += 1
                if row["reorientation"]:
                    result["reorientations"][phase] += 1
        latest = store._connection.execute(
            "SELECT json_extract(record, '$.action') FROM events "
            "WHERE kind = 'discovery_action_applied' ORDER BY sequence DESC LIMIT 1"
        ).fetchone()
        if latest is not None and isinstance(latest[0], str):
            result["last_action"] = latest[0]
        result["retrievals"] = None if result["unindexed_jobs"] else result["indexed_retrievals"]
        result["repeated_retrievals"] = None if result["unindexed_jobs"] else result["indexed_repeated_retrievals"]
        return result


def progress_lines(progress: dict[str, Any]) -> list[str]:
    """Keep observational activity separate from the checked theorem result."""
    action = progress["last_action"]
    last = _ACTION_LABELS.get(action, "Recorded action") if action else (
        "unavailable" if progress["unindexed_jobs"] else "none yet"
    )
    if progress["retrievals"] is None:
        reading = (
            "Retrievals: unavailable for " + str(progress["unindexed_jobs"]) + " unindexed jobs"
            + f"; indexed reads: {progress['indexed_retrievals']}, repeated/empty: {progress['indexed_repeated_retrievals']}"
        )
    else:
        reading = f"Retrievals: {progress['retrievals']}; repeated/empty: {progress['repeated_retrievals']}"
    lines = ["Last action: " + last, reading]
    for label, key in (("Independent reviews", "reviews"), ("Reorientations", "reorientations")):
        counts = progress[key]
        lines.append(f"{label}: {counts['completed']} completed, {counts['pending']} pending, {counts['inconclusive']} inconclusive")
    lines.append(f"Formalization jobs: {progress['formalization_jobs']}")
    return lines


def format_progress(event: dict[str, Any]) -> str:
    """A bounded human explanation alongside the existing machine event."""
    number = event.get("requests_used")
    prefix = f"[{number} calls] " if _count(number) else ""
    if event.get("event") == "action_applied":
        message = _ACTION_LABELS.get(event.get("action"), "Applied research action")
    else:
        message = {
            "provider_dispatch": "Starting model request",
            "response_saved": "Model response saved",
            "formalization_result": "Formalization result received",
        }.get(event.get("event"), "Research progress updated")
    reads, repeats = event.get("retrievals"), event.get("repeated_retrievals")
    if _count(reads) and _count(repeats) and repeats <= reads:
        message += f"; {reads} retrievals, {repeats} repeated/empty"
    if event.get("checkpoint_reason"):
        message += "; independent review of this allocation is recorded"
    return prefix + message


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Start research from a stopped Mini run, or resume a research run.",
        epilog="New runs use the saved model/provider, 4 hours and 200 model calls. "
        "Existing runs keep their saved settings and remaining budget.",
        allow_abbrev=False,
    )
    parser.add_argument("directory", type=Path, help="Mini run or research run directory")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--status", action="store_true", help="Show saved research progress")
    mode.add_argument("--prepare", action="store_true", help="Set up without starting model work")
    new = parser.add_argument_group("optional settings for a new research run")
    new.add_argument("--output", type=Path, help="New research directory (otherwise generated)")
    new.add_argument("--hours", type=float, help="Total time limit (default: 4 hours)")
    new.add_argument("--requests", type=int, help="Total model call limit (default: 200)")
    new.add_argument("--model", help="Override the saved model for research and reviews")
    new.add_argument("--provider", choices=("codex", "openai"), help="Override saved provider")
    new.add_argument("--source", type=Path, action="append", default=[],
                     help="Add a complete UTF-8 finding or source document (repeatable)")
    return parser


def _location(directory: Path) -> str:
    try:
        return str(directory.relative_to(Path.cwd()))
    except ValueError:
        return str(directory)


def _instructions(directory: Path) -> None:
    executable = "./research" if Path.cwd() == REPOSITORY else str(REPOSITORY / "research")
    command = shlex.join([executable, _location(directory)])
    print(f"Research directory: {directory}", flush=True)
    print(f"Start/resume: {command}", flush=True)
    print(f"Check progress: {command} --status", flush=True)


def _start(args: argparse.Namespace) -> int:
    directory = args.directory.resolve()
    settings = (args.output, args.hours, args.requests, args.model, args.provider)
    if (directory / "ledger.sqlite3").is_file():
        if any(value is not None for value in settings) or args.source:
            raise ValueError("This research run already has saved settings. "
                             "Resume it without new-run options; its budget is preserved.")
        from .research_claims.discovery_store import DiscoveryStore

        with DiscoveryStore(directory) as store:
            # status() validates proof receipts before any result is displayed.
            record = store.status() if args.status else store.run_record()
            progress = observational_progress(store) if args.status else None
        _instructions(directory)
        print(f"Saved model: {record['model']} ({record['provider']}); "
              f"{record['requests_used']}/{record['max_requests']} model calls used. "
              f"Original time limit: {record['max_seconds'] / 3600:g} hours.", flush=True)
        if args.prepare:
            return 0
        if args.status:
            print(f"Saved status: {record['status']}")
            result = "open"
            if record['root_proved']:
                result = "proved (verified Lean export)"
            elif record['root_refuted']:
                result = "refuted (verified Lean export)"
            print(f"Result: {result}")
            print(f"Research/proof jobs: {len(record['jobs'])}")
            for line in progress_lines(progress):
                print(line)
            return 0
        return research_main(["discovery", "run", str(directory)])

    if args.status:
        raise ValueError("Status needs a research run directory, not a Mini attempt.")
    hours = DEFAULT_HOURS if args.hours is None else args.hours
    requests = DEFAULT_REQUESTS if args.requests is None else args.requests
    seconds = hours * 3600
    if not math.isfinite(seconds) or seconds <= 0 or requests <= 0:
        raise ValueError("Hours and requests must be positive finite limits; 0 is not unlimited.")

    from .research_claims.adoption import read_mini_run

    # Validate saved source/checkpoint integrity before allocating an output path.
    adopted = read_mini_run(directory)
    config = json.loads(adopted["metadata"])["identity"]["cli_config"]
    provider = args.provider if args.provider is not None else config.get("prover")
    model = args.model if args.model is not None else config.get("prover_model")
    if provider not in ("codex", "openai"):
        raise ValueError("The saved provider is not supported by research. "
                         "Select --provider codex or --provider openai explicitly.")
    if not isinstance(model, str) or not model.strip():
        raise ValueError("The saved run has no model name. Supply --model MODEL.")
    # Fail before preparing a ledger if a supplied finding cannot be ingested.
    for source in args.source:
        source.read_bytes().decode("utf-8")
    if args.output is not None:
        output = args.output.resolve()
        if output.exists():
            raise ValueError(f"Output already exists: {output}. Pass it as the run directory to resume.")
    else:
        root = REPOSITORY / "runs" / "research"
        root.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix=directory.name[:80] + "_", dir=root))

    _instructions(output)
    print(f"Model: {model} ({provider}). Budget: {hours:g} hours, {requests} model calls.\n"
          "Research, independent reviews and Lean proof search are enabled.\n"
          "Preparing the original Lean target...", flush=True)
    init = [
        "discovery", "init", str(output), "--adopt-mini-run", str(directory),
        "--provider", provider, "--review-provider", provider,
        "--model", model, "--review-model", model,
        "--codex-bin", config.get("codex_bin") or "codex",
        "--max-requests", str(requests), "--max-seconds", str(seconds),
        "--strategy-recovery",
    ]
    for source in args.source:
        init.extend(["--source", str(source.resolve())])
    result = research_main(init)
    if result != 0:
        return result
    if args.prepare:
        print("Ready. No model calls have been made.", flush=True)
        return 0
    return research_main(["discovery", "run", str(output)])


def main(argv: Sequence[str] | None = None) -> int:
    """Delegate to the established discovery CLI, retaining its exit semantics."""
    args = _parser().parse_args(argv)
    try:
        return _start(args)
    except (ValueError, OSError, KeyError, TypeError, sqlite3.Error) as exc:
        print(f"research: {exc}", file=sys.stderr)
        return 2
    except RecursionError:
        print("research: saved data exceeds supported JSON nesting", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("research: interrupted; saved research is retained", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
