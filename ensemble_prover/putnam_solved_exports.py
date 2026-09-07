"""Read verified Putnam export manifests for local queue selection.

This lightweight scanner preserves the probe selector's artifact checks. It
consumes existing verification receipts; it does not re-run Lean or certify
untrusted artifacts. Both the public sweep and development selector use it.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Iterable


PROBLEM_RE = re.compile(
    r"^(putnam_\d{4}_[ab]\d)(?:_visible)?(?:_v\d+)?(?:\.lean)?$"
)
THEOREM_DECL_RE = re.compile(r"^\s*theorem\s+(putnam_\d{4}_[ab]\d)\b")
NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace(?:\s+([A-Za-z0-9_'.]+))?\b")
SECTION_OPEN_RE = re.compile(r"^\s*section\b")
SCOPE_CLOSE_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?(?:\s|$)")
FORBIDDEN_SOLVED_ARTIFACT_RE = re.compile(
    r"\b(?:sorry|admit|native_decide|axiom|constant|opaque|unsafe)\b"
)

def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return ""


def _problem_from_name(name: str) -> str | None:
    match = PROBLEM_RE.fullmatch(str(name or "").strip())
    if not match:
        return None
    return match.group(1)


def _safe_manifest_output_stem(output_stem: str, problem: str) -> bool:
    stem = str(output_stem or "").strip()
    return bool(
        stem
        and Path(stem).name == stem
        and Path(stem).stem == stem
        and _problem_from_name(stem) == problem
    )


def _manifest_row_output_stem(item: dict[str, Any]) -> str:
    return str(item.get("output_stem") or "").strip()


def _strip_lean_comments(text: str) -> str:
    source = str(text or "")
    out: list[str] = []
    i = 0
    block_depth = 0
    line_comment = False
    while i < len(source):
        pair = source[i : i + 2]
        ch = source[i]
        if line_comment:
            if ch == "\n":
                line_comment = False
                out.append(ch)
            i += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
                continue
            if pair == "-/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append(ch)
            i += 1
            continue
        if pair == "--":
            line_comment = True
            i += 2
            continue
        if pair == "/-":
            block_depth = 1
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _artifact_declares_verified_theorem(text: str, problem: str) -> bool:
    cleaned = _strip_lean_comments(text)
    if not problem or FORBIDDEN_SOLVED_ARTIFACT_RE.search(cleaned):
        return False
    scope_stack: list[tuple[str, str]] = []
    for line in cleaned.splitlines():
        namespace_match = NAMESPACE_OPEN_RE.match(line)
        if namespace_match:
            scope_stack.append(("namespace", str(namespace_match.group(1) or "")))
            continue
        if SECTION_OPEN_RE.match(line):
            scope_stack.append(("section", ""))
            continue
        close_match = SCOPE_CLOSE_RE.match(line)
        if close_match and scope_stack:
            name = str(close_match.group(1) or "")
            if name:
                for index in range(len(scope_stack) - 1, -1, -1):
                    if scope_stack[index] == ("namespace", name):
                        del scope_stack[index:]
                        break
            else:
                scope_stack.pop()
            continue
        match = THEOREM_DECL_RE.match(line)
        if match and any(kind == "namespace" for kind, _name in scope_stack):
            return False
        if match and str(match.group(1) or "").strip() == problem:
            return True
    return False


def scan_solved_artifacts(paths: Iterable[Path]) -> set[str]:
    solved: set[str] = set()
    for root in paths:
        if not root.exists():
            continue
        manifest_path = root / "manifest.json"
        if not manifest_path.exists():
            continue
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except Exception:
            manifest = []
        for item in list(manifest or []):
            if not isinstance(item, dict):
                continue
            output_stem = _manifest_row_output_stem(item)
            if item.get("export_verified") is not True:
                continue
            if (
                str(item.get("export_verification_status") or "verified").strip()
                != "verified"
            ):
                continue
            problem = _problem_from_name(str(item.get("theorem_name") or ""))
            if not problem or not _safe_manifest_output_stem(output_stem, problem):
                continue
            artifact = root / f"{output_stem}.lean"
            if (
                not artifact.exists()
                or artifact.suffix != ".lean"
                or _problem_from_name(artifact.name) != problem
            ):
                continue
            text = _read_text(artifact)
            if not _artifact_declares_verified_theorem(text, problem):
                continue
            solved.add(problem)
    return solved
