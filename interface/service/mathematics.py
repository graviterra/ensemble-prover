"""Bounded mathematical source for the selected recorded graph node.

Helper statements come from their acceptance row. Checkpoint proofs require
the same helper name, statement identity, and verification environment. No
checkpoint paths outside the run are followed and no source is executed.
"""

from __future__ import annotations

from functools import lru_cache
import hashlib
from itertools import islice
import json
import os
from pathlib import Path
import re
import stat
from typing import Any

from console.reducer import MAX_HELPER_MATH, MAX_MATH_TEXT
from console.session import AttachedRun

MAX_CHECKPOINT_BYTES = 16 * 1024 * 1024
MAX_SOURCE_TEXT = 32 * 1024
MAX_SOURCE_TOTAL = 1024 * 1024
_SNAPSHOT_NAME = re.compile(r"[0-9]{12}\.json\Z")


def _text(value: Any, limit: int) -> str:
    if not isinstance(value, str) or len(value) > limit or "\0" in value:
        return ""
    try:
        value.encode("utf-8")
    except UnicodeError:
        return ""
    return value


def _open(run_dir: str, name: str, *, checkpoint: bool = False) -> int:
    directory = os.open(run_dir, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        if checkpoint:
            child = os.open("checkpoints", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
            os.close(directory)
            directory = child
        return os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
    finally:
        os.close(directory)


def _fingerprint(info: os.stat_result) -> tuple[int, int, int, int]:
    return info.st_dev, info.st_ino, info.st_mtime_ns, info.st_size


def _read(fd: int, limit: int) -> dict[str, Any]:
    with os.fdopen(fd, "rb") as handle:
        info = os.fstat(handle.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            return {}
        raw = handle.read(limit + 1)
    if len(raw) > limit:
        return {}
    value = json.loads(raw)
    return value if isinstance(value, dict) else {}


@lru_cache(maxsize=8)
def _checkpoint(
    run_dir: str, name: str, signature: tuple[int, int, int, int], digest: str, attempt: str,
) -> dict[str, Any]:
    fd = _open(run_dir, name, checkpoint=True)
    if _fingerprint(os.fstat(fd)) != signature:
        os.close(fd)
        return {}
    record = _read(fd, MAX_CHECKPOINT_BYTES)
    if record.get("attempt_id") != attempt or record.get("schema_version") not in (1, 2):
        return {}
    canonical = json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)
    if hashlib.sha256(canonical.encode("utf-8")).hexdigest() != digest:
        return {}
    identity = record.get("identity")
    root = identity.get("input") if isinstance(identity, dict) else None
    root = root if isinstance(root, dict) else {}
    theorem = _text(root.get("theorem_name"), 512)
    statement = _text(root.get("statement_type"), MAX_MATH_TEXT)
    helpers: dict[tuple[str, str, str, str], set[str]] = {}
    roots: set[str] = set()
    total = len(statement)
    sessions = record.get("sessions")
    incomplete = isinstance(sessions, dict) and len(sessions) > 128
    if isinstance(sessions, dict):
        for session in islice(sessions.values(), 128):
            dossier = session.get("dossier") if isinstance(session, dict) else None
            if not isinstance(dossier, dict):
                continue
            if dossier.get("theorem_name") == theorem and dossier.get("root_statement") == statement:
                proof = _text(dossier.get("final_proof"), MAX_SOURCE_TEXT)
                if proof and total + len(proof) <= MAX_SOURCE_TOTAL:
                    roots.add(proof)
                    total += len(proof)
                else:
                    roots.add("")
            candidates = dossier.get("verified_helpers")
            if not isinstance(candidates, list):
                continue
            incomplete = incomplete or len(candidates) > MAX_HELPER_MATH
            for candidate in islice(candidates, MAX_HELPER_MATH):
                if not isinstance(candidate, dict):
                    continue
                key = tuple(_text(candidate.get(field), limit) for field, limit in (
                    ("name", 160), ("contract_identity", 512), ("verification_environment_hash", 512),
                    ("progress_statement", MAX_MATH_TEXT),
                ))
                source = _text(candidate.get("source"), MAX_SOURCE_TEXT)
                if not all(key):
                    continue
                if key not in helpers and len(helpers) >= MAX_HELPER_MATH:
                    incomplete = True
                    continue
                key_chars = len(key[3]) if key not in helpers else 0
                if total + key_chars > MAX_SOURCE_TOTAL:
                    incomplete = True
                    continue
                total += key_chars
                values = helpers.setdefault(key, set())
                if not source:
                    values.add("")
                    continue
                if source in values:
                    continue
                if len(values) >= 2 or total + len(source) > MAX_SOURCE_TOTAL:
                    values.add("")  # Ambiguity or omitted variants must not become a unique match.
                    incomplete = True
                    continue
                values.add(source)
                total += len(source)
    if incomplete:
        roots.clear()
        for values in helpers.values():
            values.add("")
    return {"theorem": theorem, "statement": statement, "proofs": roots, "helpers": helpers}


def _load_checkpoint(run_dir: Path) -> dict[str, Any]:
    try:
        manifest = _read(_open(str(run_dir), "attempt_checkpoint.json"), 256 * 1024)
        head = manifest.get("head")
        if not isinstance(head, dict) or manifest.get("schema_version") != 1:
            return {}
        path = _text(head.get("snapshot_path"), 4096)
        name = Path(path).name
        digest = _text(head.get("snapshot_hash"), 64)
        attempt = _text(manifest.get("attempt_id"), 128)
        if not _SNAPSHOT_NAME.fullmatch(name) or not re.fullmatch(r"[0-9a-f]{64}", digest) or not attempt:
            return {}
        fd = _open(str(run_dir), name, checkpoint=True)
        try:
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_CHECKPOINT_BYTES:
                return {}
            signature = _fingerprint(info)
        finally:
            os.close(fd)
        return _checkpoint(str(run_dir), name, signature, digest, attempt)
    except (OSError, ValueError, UnicodeError, RecursionError, OverflowError):
        return {}


def node_mathematics(attached: AttachedRun, root_name: str) -> dict[str, dict[str, str]]:
    checkpoint = _load_checkpoint(attached.run_dir)
    root_statement = checkpoint.get("statement", "") if checkpoint.get("theorem") == root_name else ""
    root_proofs = checkpoint.get("proofs", set()) if root_statement else set()
    root_proof = next(iter(root_proofs)) if len(root_proofs) == 1 else ""
    evidence = {"root": {
        "statement": root_statement, "leanSource": root_proof, "scope": "problem",
        "source": "Recorded checkpoint" if root_statement else "",
        "reason": "" if root_proof else "No uniquely matched root proof source was recorded." if root_statement
        else "No matching formal root statement is available in the recorded checkpoint.",
    }}
    total = len(root_statement) + len(root_proof)
    candidates = checkpoint.get("helpers", {})
    for name, item in attached.state.helper_math.items():
        statement = item["statement"]
        source = ""
        reason = item["reason"]
        scope = ""
        if not item["ambiguous"]:
            scopes, identity, environment = item["identity"]
            scope = scopes[0] or "not recorded"
            proofs = candidates.get((name, identity, environment, statement), set()) if identity and environment and statement else set()
            if len(proofs) == 1 and "" not in proofs:
                source = next(iter(proofs))
            elif not reason:
                reason = "No uniquely matched Lean proof source is available; the statement comes from its recorded acceptance."
        if total + len(statement) + len(source) > MAX_SOURCE_TOTAL:
            statement = source = ""
            reason = "The mathematics display limit was reached."
        total += len(statement) + len(source)
        evidence[f"helper:{name}"] = {
            "statement": statement, "leanSource": source, "scope": scope,
            "source": "Recorded helper acceptance and matching checkpoint" if source else "Recorded helper acceptance" if statement else "",
            "reason": reason,
        }
    return evidence
