"""Discover ordinary Lean problem files before dispatching supervised proof runs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import sys
import threading
import uuid
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Sequence

from .lean_input_io import read_source_bytes
from .theorem_project import _mask_noncode, infer_lake_project, scan_lean_theorems


_ROOT = Path(__file__).resolve().parent.parent
_IGNORED_DIRECTORIES = frozenset({
    ".git", ".lake", ".venv", "venv", "node_modules", "__pycache__", "build", "dist",
})
_OWNED_ARGUMENTS = frozenset({
    "_input_path", "_check_input", "lean_file", "theorem_name", "lean_project_dir",
    "output_dir",
})
_GENERATION_MARKER = ".ensemble-input-generation"


def discover_lean_files(path: Path) -> tuple[Path, ...]:
    """Enumerate source files without following directory or file symlinks."""
    path = path.expanduser().resolve(strict=True)
    if path.is_file():
        if path.suffix != ".lean":
            raise ValueError(f"expected a Lean source file or directory: {path}")
        return (path,)
    if not path.is_dir():
        raise ValueError(f"input is not a file or directory: {path}")
    files: list[Path] = []

    def on_error(error: OSError) -> None:
        raise error

    for directory, subdirectories, names in os.walk(path, onerror=on_error):
        parent = Path(directory)
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in _IGNORED_DIRECTORIES and not (parent / name).is_symlink()
            and not (parent / name / _GENERATION_MARKER).is_file()
        )
        for name in sorted(names):
            candidate = parent / name
            if candidate.suffix == ".lean" and not candidate.is_symlink() and candidate.is_file():
                files.append(candidate)
    return tuple(files)


def input_project(source: Path, explicit: str | None = None) -> Path:
    """Prefer the source's own Lake project over the checkout's Mathlib runtime."""
    owning = infer_lake_project(source)
    mismatched_pin = None
    if explicit:
        candidates = (Path(explicit).expanduser().resolve(strict=True),)
    else:
        candidates = (owning,) if owning is not None else (
            Path.cwd() / "lean_project", _ROOT / "lean_project",
        )
    for project in candidates:
        if not project.is_dir() or not any(
            (project / name).is_file() for name in ("lakefile.lean", "lakefile.toml")
        ):
            continue
        project = project.resolve()
        if not explicit and owning is None:
            # A source-only distribution may pin a toolchain without a Lake
            # file. Do not silently substitute an incompatible runtime.
            pin = None
            for parent in source.parents:
                # An ambient home toolchain is an elan default, not a pin
                # supplied by this corpus. Likewise stop at its checkout.
                if parent == Path.home():
                    break
                if (parent / "lean-toolchain").is_file():
                    pin = parent / "lean-toolchain"
                    break
                if (parent / ".git").exists():
                    break
            if pin is not None and (
                not (project / "lean-toolchain").is_file()
                or pin.read_text().strip() != (project / "lean-toolchain").read_text().strip()
            ):
                mismatched_pin = pin
                continue
        return project
    if mismatched_pin is not None:
        raise ValueError(
            f"input toolchain {mismatched_pin} differs from the available runtimes; "
            "pass --project-path to a compatible Lake project"
        )
    raise ValueError(
        f"could not find a Lake project for {source}; "
        "pass --project-path to an existing compatible Lake project"
    )


def forwarded_arguments(parser: argparse.ArgumentParser, argv: Sequence[str]) -> list[str]:
    """Retain explicit Mini policies while replacing only the input/output fields."""
    retained: list[str] = []
    index = 0
    while index < len(argv):
        token = argv[index]
        if token == "--":
            # The only positional argument is the input path.
            break
        parsed = parser._parse_optional(token)
        if parsed is None:
            index += 1
            continue
        candidates = parsed if isinstance(parsed, list) else [parsed]
        # Patched Python releases include a fourth separator element; the
        # action and optional inline value remain the first and last fields.
        action, value = candidates[0][0], candidates[0][-1]
        if action is None:
            raise ValueError(f"unknown argument: {token}")
        if action.nargs not in (None, 0):
            raise ValueError(f"unsupported forwarding arity: {token}")
        count = 2 if action.nargs is None and value is None else 1
        if index + count > len(argv):
            raise ValueError(f"missing argument value: {token}")
        if action.dest not in _OWNED_ARGUMENTS:
            retained.extend(argv[index:index + count])
        index += count
    return retained


def should_prepare(args: argparse.Namespace) -> bool:
    path = getattr(args, "_input_path", None) or getattr(args, "lean_file", None)
    if getattr(args, "_check_input", False) and not path:
        raise ValueError("--check-input requires a Lean file or directory input")
    if not path or getattr(args, "resume_from", None) or getattr(args, "putnam_file", None):
        return False
    return bool(
        getattr(args, "_input_path", None) or getattr(args, "_check_input", False)
        or Path(path).expanduser().is_dir()
        or not getattr(args, "theorem_name", None)
        or not getattr(args, "lean_project_dir", None)
    )


@contextmanager
def _preparation_interrupts():
    """Let owned Lean checks retire their process groups on termination too."""
    previous = None
    if threading.current_thread() is threading.main_thread():
        def interrupted(_signal, _frame):
            raise KeyboardInterrupt

        previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        yield
    finally:
        if previous is not None:
            signal.signal(signal.SIGTERM, previous)


def run_path_input(args: argparse.Namespace, argv: Sequence[str],
                   parser: argparse.ArgumentParser) -> int:
    try:
        with _preparation_interrupts():
            return _run_path_input(args, argv, parser)
    except KeyboardInterrupt:
        output = getattr(args, "_input_generation", None)
        if output is not None and not (output / "batch_manifest.json").exists():
            from .putnam_sweep import save_manifest

            save_manifest(output / "batch_manifest.json", {
                "schema_version": 1, "kind": "lean_input_batch", "exit_code": 130,
                "metadata": {"input_path": getattr(args, "_input_source", ""),
                             "budget_scope": "per_target"},
                "queue": getattr(args, "_input_queue", []),
            })
        raise


def _run_path_input(args: argparse.Namespace, argv: Sequence[str],
                    parser: argparse.ArgumentParser) -> int:
    """Compile and snapshot discovered inputs before any provider is contacted."""
    from .lean_input_batch import run_prepared_batch
    from .lean_input_preparation import prepare_lean_file

    source = Path(getattr(args, "_input_path", None) or args.lean_file).expanduser().resolve(strict=True)
    files = discover_lean_files(source)
    if not files:
        raise ValueError(f"no Lean source files found in {source}")
    output = (Path(args.output_dir).expanduser().resolve() if args.output_dir else
              _ROOT / "runs" / "mini_prover" / "inputs" /
              (datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:8]))
    # A fresh directory is an immutable input generation. Existing individual
    # attempt checkpoints retain the ordinary --resume-from interface.
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError(f"input output directory is not empty: {output}")
    # The console reserves an empty directory before launch. Claim it with
    # exclusive creation so competing dispatchers cannot share a generation.
    with (output / _GENERATION_MARKER).open("x", encoding="utf-8") as marker:
        marker.write(str(source) + "\n")
    args._input_generation = output
    args._input_source = str(source)
    print(f"Discovering problems in {source}\nInput artifacts: {output}", flush=True)
    records: list[dict] = []
    args._input_queue = records
    source_records: list[dict] = []
    imports = tuple(getattr(args, "theorem_project_imports", ()) or ())
    selected_name = getattr(args, "theorem_name", None)
    if selected_name:
        selected_name = selected_name.removeprefix("_root_.")
    for number, path in enumerate(files, 1):
        file_record = {"source_path": str(path)}
        source_records.append(file_record)
        try:
            raw = read_source_bytes(path)
            file_record["source_sha256"] = hashlib.sha256(raw).hexdigest()
            text = raw.decode("utf-8")
            declarations = scan_lean_theorems(text)
            # The compiler must diagnose declarations outside the lightweight
            # scanner grammar instead of silently losing those problems.
            possible_declarations = len(re.findall(
                r"\b(?:theorem|lemma)(?=\s|«)",
                _mask_noncode(text, mask_quoted_identifiers=True),
            ))
            if not declarations and not possible_declarations:
                file_record["status"] = "no_theorems"
                continue
            if selected_name and possible_declarations <= len(declarations) and not any(
                decl.canonical_name == selected_name or decl.source_name == selected_name
                or decl.canonical_name.endswith("." + selected_name)
                for decl in declarations
            ):
                file_record["status"] = "not_selected"
                continue
            project = input_project(path, getattr(args, "lean_project_dir", None))
            file_record["project_path"] = str(project)
            print(f"Checking {path} (project: {project})", flush=True)
            targets = prepare_lean_file(
                path, project, output / "preparation" / f"{number:04d}",
                theorem_name=selected_name, imports=imports,
                source_dirs=tuple(Path(value) for value in
                                  (getattr(args, "theorem_project_source_dirs", ()) or ())),
                timeout_s=float(getattr(args, "lean_timeout_s", 300) or 300),
                max_heartbeats=int(getattr(args, "lean_max_heartbeats", 1600000)),
            )
            if hashlib.sha256(read_source_bytes(path)).hexdigest() != file_record["source_sha256"]:
                raise ValueError("input changed during preparation; retry with stable source files")
            for target in targets:
                record = target.to_record()
                records.append(record)
                status = "ready" if target.ready else "blocked"
                print(f"  {target.theorem_name}: {status}"
                      + (f" ({target.error})" if target.error else ""), flush=True)
            file_record["status"] = "prepared" if targets else "no_unfinished_theorems"
        except (ValueError, OSError, TimeoutError) as error:
            file_record.update(status="blocked", error=str(error))
            records.append({**file_record, "theorem_name": selected_name or "", "error": str(error)})
            print(f"  Input blocked: {error}", file=sys.stderr, flush=True)
    metadata = {"input_path": str(source), "sources": source_records, "budget_scope": "per_target"}
    if not records:
        metadata["error"] = "no matching unfinished theorems found"
    if getattr(args, "_check_input", False) or not records:
        manifest = {"schema_version": 1, "status": "checked", "metadata": metadata, "targets": records}
        (output / "batch_manifest.json").write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8",
        )
        ready = sum(bool(record.get("prepared_path")) and not record.get("error") for record in records)
        print(f"Input check: {ready} ready, {len(records) - ready} blocked. "
              f"Manifest: {output / 'batch_manifest.json'}", flush=True)
        return 0 if records and ready == len(records) else 2
    print("Starting ready targets sequentially. Search and cost budgets apply independently "
          "to each target; there is no shared batch budget.", flush=True)
    return run_prepared_batch(records, output, forwarded_arguments(parser, argv), metadata=metadata)
