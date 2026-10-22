"""Durable operator exclusions for exact helper sources.

Retirement controls reuse, not mathematical truth. A retired implication may
remain a valid theorem even when its premise makes it an unhelpful route.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping

import fcntl


class HelperRetirementError(ValueError):
    """The operator policy cannot safely be read or applied."""


def retirement_path() -> Path:
    override = os.environ.get("ENSEMBLE_HELPER_RETIREMENTS")
    if override:
        return Path(override).expanduser()
    state = Path(os.environ.get("XDG_STATE_HOME") or Path.home() / ".local/state")
    return state / "ensemble_prover/helper_retirements.json"


def _normalized(source: str) -> str:
    return source.replace("\r\n", "\n").replace("\r", "\n").strip()


@lru_cache(maxsize=8192)
def helper_retirement_source_hash(source: str) -> str:
    return hashlib.sha256(_normalized(source).encode("utf-8")).hexdigest()


@lru_cache(maxsize=32)
def _read_snapshot(path: str, stamp: tuple[int, ...]) -> tuple[dict[str, str], ...]:
    del stamp
    try:
        raw = json.loads(Path(path).read_text(encoding="utf-8"))
        if type(raw) is not dict or type(raw.get("schema_version")) is not int or raw["schema_version"] != 1 or type(raw.get("retirements")) is not list:
            raise ValueError("invalid schema")
        records = []
        for row in raw["retirements"]:
            if type(row) is not dict or any(type(row.get(key)) is not str for key in (
                "source", "source_sha256", "theorem_name", "reason",
            )):
                raise ValueError("invalid entry")
            if not row["source"].strip() or not row["reason"].strip() or (
                helper_retirement_source_hash(row["source"]) != row["source_sha256"]
            ):
                raise ValueError("invalid source binding")
            records.append({key: row[key] for key in ("source", "source_sha256", "theorem_name", "reason")})
        return tuple(records)
    except (OSError, ValueError, TypeError) as exc:
        raise HelperRetirementError(f"Cannot read helper retirement policy {path}: {exc}") from exc


def retirement_snapshot(*, path: Path | None = None) -> tuple[dict[str, str], ...]:
    selected = Path(path) if path is not None else retirement_path()
    try:
        stat = selected.stat()
    except FileNotFoundError:
        return ()
    except OSError as exc:
        raise HelperRetirementError(f"Cannot read helper retirement policy {selected}: {exc}") from exc
    stamp = (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
    return tuple(dict(row) for row in _read_snapshot(str(selected.absolute()), stamp))


def helper_source_is_retired(source: str, *, theorem_name: str = "") -> bool:
    digest = helper_retirement_source_hash(source)
    return any(row["source_sha256"] == digest and (
        not row["theorem_name"] or row["theorem_name"] == theorem_name
    ) for row in retirement_snapshot())


def helper_record_is_retired(record: Mapping[str, Any]) -> bool:
    return helper_source_is_retired(str(record.get("source") or ""),
                                    theorem_name=str(record.get("theorem_name") or ""))


def assert_helpers_not_retired(sources: Any, *, theorem_name: str = "") -> None:
    if any(helper_source_is_retired(str(source), theorem_name=theorem_name) for source in sources):
        raise HelperRetirementError(
            "Helper context contains an operator-retired source. Start a fresh run to "
            "reverify the remaining library, or explicitly revise the retirement policy."
        )


def theory_source_is_retired(source: str, *, theorem_name: str = "") -> bool:
    """Check exact declaration blocks inside generated theory module wrappers.

    Find executable declaration spans with the shared Lean scanner, then compare
    original bytes. Comments and literals never introduce declarations. Trailing
    comment trivia belongs to no proof; appended tactics change its source.
    """
    rows = [row for row in retirement_snapshot()
            if not row["theorem_name"] or row["theorem_name"] == theorem_name]
    if not rows:
        return False
    from .mini_lean_extract import _strip_lean_comments, _top_level_declaration_registry_with_opens

    module = _normalized(source)
    blocks, _ambiguous, _opens, positions = _top_level_declaration_registry_with_opens(module)
    for row in rows:
        expected = _normalized(row["source"])
        _expected_blocks, ambiguous, _expected_opens, expected_positions = (
            _top_level_declaration_registry_with_opens(expected)
        )
        if ambiguous or len(expected_positions) != 1:
            continue
        expected_offset = next(iter(expected_positions.values()))
        for name, declaration_start in positions.items():
            start = declaration_start - expected_offset
            end = start + len(expected)
            declaration_end = declaration_start + len(blocks[name])
            if start < 0 or end > declaration_end or module[start:end] != expected:
                continue
            if not _strip_lean_comments(module[end:declaration_end]).strip():
                return True
    return False


def retire_helper_source(source: str, reason: str, *, theorem_name: str = "",
                         path: Path | None = None) -> dict[str, str]:
    """Persist an explicit operator decision, bound to the full source bytes."""
    source, reason = _normalized(source), str(reason).strip()
    if not source or not reason:
        raise ValueError("retirement requires a source and a reason")
    selected = Path(path) if path is not None else retirement_path()
    selected.parent.mkdir(parents=True, exist_ok=True)
    row = {"source": source, "source_sha256": helper_retirement_source_hash(source),
           "theorem_name": str(theorem_name).strip(), "reason": reason}
    lock_path = selected.with_name("." + selected.name + ".lock")
    with lock_path.open("a") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        records = list(retirement_snapshot(path=selected))
        records = [item for item in records if (item["source_sha256"], item["theorem_name"])
                   != (row["source_sha256"], row["theorem_name"])]
        records.append(row)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=selected.parent,
                                             prefix="." + selected.name + ".", delete=False) as output:
                temporary = Path(output.name)
                json.dump({"schema_version": 1, "retirements": records}, output, ensure_ascii=False)
                output.write("\n")
                output.flush()
                os.fsync(output.fileno())
            os.replace(temporary, selected)
            directory = os.open(selected.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    return dict(row)


def main() -> None:
    parser = argparse.ArgumentParser(description="Retire one exact helper source from future reuse.")
    parser.add_argument("source_file", type=Path)
    parser.add_argument("--reason", required=True)
    parser.add_argument("--theorem-name", default="", help="Optional owner scope; default applies to every owner.")
    parser.add_argument("--policy", type=Path)
    args = parser.parse_args()
    row = retire_helper_source(args.source_file.read_text(encoding="utf-8"), args.reason,
                               theorem_name=args.theorem_name, path=args.policy)
    print(row["source_sha256"])


if __name__ == "__main__":
    main()
