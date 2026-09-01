#!/usr/bin/env python3
"""Reconstruct, verify, and publish standalone Lean proof artifacts.

The live path exports one finalized run under a directory-wide publication
lock. Batch mode rebuilds eligible exports from completed run summaries. Both
generic theorem-project snapshots and PutnamBench adapter runs preserve their
recorded theorem declaration, imports, execution context, helper closure, and
answer-visibility contract.

The CLI verifies and axiom-audits reconstructed proofs unless explicitly asked
to skip Lean; Mini's automatic solved-run export also requests verification.
The lower-level ``export_solved_run`` API leaves verification opt-in so callers
must choose the appropriate trust boundary. A directory-wide lock serializes
publication. Verified Lean installation uses same-directory replacement after
replay and audit; the explicitly unverified API path writes its output directly.
Same-run retries are idempotent, and the manifest records exact run and project
provenance. Publication spans multiple artifacts and is not one filesystem
transaction. The default source-checkout destination is
``runs/mini_prover/solved``; programmatic callers may supply another path.

Usage::

    python -m ensemble_prover.extract_solved
    python -m ensemble_prover.extract_solved --audit-existing
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from ensemble_prover.helper_salvage import merge_context_helpers  # noqa: E402
from ensemble_prover.lean_artifact_sanitize import (  # noqa: E402
    sanitize_lean_artifact_text,
    sanitize_lean_artifact_texts,
)
from ensemble_prover.putnam import load_putnam_problem  # noqa: E402
from ensemble_prover.theorem_project import (  # noqa: E402
    GENERIC_ADAPTER_ID,
    PUTNAMBENCH_ADAPTER_ID,
    active_include_variables,
    decode_theorem_target_context,
    generic_theorem_artifact_slug,
    is_valid_lean_qualified_name,
    is_valid_lean_universe_suffix,
    merge_imports,
    scan_lean_theorems,
    select_lean_theorem,
    split_lean_import_header,
    theorem_artifact_slug,
    theorem_proof_scoped_prefix,
    theorem_reusable_preamble,
    theorem_project_compiled_content_hash,
    theorem_project_environment_hash,
    theorem_project_tree_content_hash,
)
from ensemble_prover.mini_theory.model import PublishedTheoryBundle  # noqa: E402
from ensemble_prover.solved_export_policy import (  # noqa: E402
    EXPORT_BOUNDARY_KEYS as POLICY_EXPORT_BOUNDARY_KEYS,
    EXPORT_FAILURE_COUNTER_KEYS as POLICY_EXPORT_FAILURE_COUNTER_KEYS,
    bool_true as policy_bool_true,
    counter_positive as policy_counter_positive,
    counter_zero_or_absent as policy_counter_zero_or_absent,
    effective_solved as policy_effective_solved,
    export_boundary_present as policy_export_boundary_present,
    export_status_values as policy_export_status_values,
    solved_export_verified_payload as policy_solved_export_verified_payload,
)
from ensemble_prover.subprocess_environment import (  # noqa: E402
    sanitized_subprocess_environment,
)

RUNS_DIR = PROJECT_ROOT / "runs" / "mini_prover"
SOLVED_DIR = RUNS_DIR / "solved"
PUTNAM_SRC = PROJECT_ROOT / "external" / "PutnamBench" / "lean4" / "src"

_THEOREM_HEADER_RE = re.compile(r"(?m)^\s*theorem\s+([A-Za-z0-9_']+)\b")
_EXPORT_PROBLEM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_MINI_THEORY_MODULE_RE = re.compile(
    r"^MiniTheory\.Domains\.[A-Za-z][A-Za-z0-9_']*\.Bundles\."
    r"B_([0-9a-f]{16})\.Theory$"
)
_EXPORT_FAILURE_COUNTER_KEYS = POLICY_EXPORT_FAILURE_COUNTER_KEYS
_EXPORT_BOUNDARY_KEYS = POLICY_EXPORT_BOUNDARY_KEYS


def _mini_theory_snapshot_bundle_id(
    module_name: str,
    record: Dict[str, Any],
) -> Optional[str]:
    match = _MINI_THEORY_MODULE_RE.fullmatch(str(module_name or "").strip())
    if match is None:
        return None
    bundle_id = match.group(1)
    if str(record.get("bundle_id") or "").strip() != bundle_id:
        return None
    return bundle_id


@dataclass
class SolvedRecord:
    theorem_name: str
    output_stem: str
    solve_index: int
    solve_count: int
    output_path: str
    source_path: str
    run_dir: str
    solved_at_ts: float
    solved_at_iso: str
    turns: int
    wall_s: float
    helper_count: int
    has_refiner: bool
    proof_chars: int
    answer_visibility: str
    opaque_mode: Optional[bool] = None
    allow_official_answer_visibility: Optional[bool] = None
    official_answer_payload_present: Optional[bool] = None
    export_verified: bool = False
    export_verification_status: str = ""
    export_verification_output: str = ""
    export_axioms: Tuple[str, ...] = ()
    source_map_path: str = ""
    dependency_graph_path: str = ""
    dependency_graph_json_path: str = ""
    source_html_path: str = ""
    navigation_artifacts_error: str = ""
    lean_project_path: str = ""
    module_search_paths: Tuple[str, ...] = ()
    project_imports: Tuple[str, ...] = ()
    support_project_builds: Dict[str, List[str]] = field(default_factory=dict)


@dataclass
class ExportResult:
    records: List[SolvedRecord]
    skipped: List[Tuple[str, str]]


def _write_solved_manifest(manifest_path: Path, records: List[Dict[str, Any]]) -> None:
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w",
        encoding="utf-8",
        delete=False,
        dir=str(manifest_path.parent),
    ) as handle:
        json.dump(records, handle, indent=2, ensure_ascii=False)
        handle.write("\n")
        temp_name = handle.name
    os.replace(temp_name, manifest_path)


class SolvedExportVerificationError(RuntimeError):
    """Raised when the exact emitted solved Lean file does not kernel-check.

    ``status`` distinguishes the rejection class machine-readably:
    ``lean_rejected`` (kernel compile), ``axiom_rejected`` (trust-expanding
    axioms, e.g. native_decide), ``axiom_audit_failed`` (audit infra).
    """

    def __init__(self, output: str, *, status: str = "lean_rejected") -> None:
        super().__init__("exported solved Lean file failed kernel verification")
        self.status = str(status or "lean_rejected")
        self.output = str(output or "")


def _summary_export_status_values(summary: Dict[str, Any]) -> Tuple[str, ...]:
    return policy_export_status_values(summary)


def _summary_export_boundary_status(summary: Dict[str, Any]) -> Tuple[bool, str]:
    statuses = _summary_export_status_values(summary)
    status = (
        statuses[0]
        if statuses and all(item == statuses[0] for item in statuses)
        else ""
    )
    if statuses and not status:
        status = "malformed"
    boundary_present = policy_export_boundary_present(summary)
    return boundary_present, status


def _summary_counter_positive(summary: Dict[str, Any], *keys: str) -> bool:
    return policy_counter_positive(summary, *keys)


def _summary_counter_zero_or_absent(summary: Dict[str, Any], *keys: str) -> bool:
    return policy_counter_zero_or_absent(summary, *keys)


def _summary_bool_true(summary: Dict[str, Any], key: str) -> bool:
    return policy_bool_true(summary, key)


def _summary_export_verified(summary: Dict[str, Any]) -> bool:
    return policy_solved_export_verified_payload(summary)


def _summary_solved_for_export(summary: Dict[str, Any]) -> bool:
    return policy_effective_solved(summary)


# Live export is a two-phase commit. The worker leaves ``not_attempted`` and
# the supervisor durably publishes ``pending_supervisor_verification`` before
# invoking this exporter, so a crash can never leave solved=true without an
# installed kernel-verified artifact. An ``import_error`` records the same
# finalized boundary after exporter infrastructure failed to load; it is safe
# to retry only through this explicit verify_lean + pre-export-bootstrap path.
# Batch export remains fail-closed because it does not enable that bootstrap.
_LIVE_PRE_EXPORT_BOOTSTRAP_STATUSES = frozenset(
    {"not_attempted", "pending_supervisor_verification", "import_error"}
)


def _find_solved_runs(answer_visibility: str = "opaque") -> Dict[str, List[Path]]:
    """All solved run dirs per theorem name, oldest first."""

    target_visibility = (
        "visible"
        if str(answer_visibility or "").strip().lower() == "visible"
        else "opaque"
    )
    solved: Dict[str, List[Tuple[float, Path]]] = {}
    for d in RUNS_DIR.iterdir():
        if not d.is_dir() or d.name.startswith("_"):
            continue
        s_path = d / "summary.json"
        if not s_path.exists():
            continue
        try:
            s = json.loads(s_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not _summary_solved_for_export(s):
            continue
        if _summary_answer_visibility(s) != target_visibility:
            continue
        identity = _single_run_export_identity(s)
        if identity is None:
            recorded_identity = _recorded_export_identity_for_cleanup(s)
            if recorded_identity is None:
                continue
            identity = (recorded_identity[0], recorded_identity[1], None)
        name = identity[0]
        ts = d.stat().st_mtime
        solved.setdefault(name, []).append((ts, d))
    return {
        name: [
            path for _, path in sorted(items, key=lambda item: (item[0], item[1].name))
        ]
        for name, items in solved.items()
    }


def _get_solved_turn(run_dir: Path) -> Optional[Dict[str, Any]]:
    """Pull the root SOLVED turn record, ignoring child/subgoal sessions."""
    t_path = run_dir / "turns.jsonl"
    if not t_path.exists():
        return None
    solved_rec: Optional[Dict[str, Any]] = None
    for line in t_path.read_text(encoding="utf-8").splitlines():
        try:
            rec = json.loads(line)
        except Exception:
            continue
        if rec.get("verdict") == "solved":
            if str(rec.get("session_scope") or "").strip() == "subgoal":
                continue
            solved_rec = rec
    return solved_rec


def _summary_replay(summary: Dict[str, Any]) -> Tuple[str, List[str]]:
    """Return the root proof/helpers recorded by the run summary, if present."""

    certificate = _summary_root_certificate(summary)
    if certificate:
        proof = certificate.get("proof")
        helpers_raw = certificate.get("replay_helpers")
        if isinstance(proof, str) and proof.strip() and isinstance(helpers_raw, list):
            helpers = list(sanitize_lean_artifact_texts(helpers_raw))
            return sanitize_lean_artifact_text(proof), helpers
    proof = summary.get("final_proof")
    if not isinstance(proof, str) or not proof.strip():
        return "", []
    helpers = _summary_verified_helpers(summary)
    helpers_raw = summary.get("final_proof_helpers")
    final_helpers: List[str] = []
    if isinstance(helpers_raw, list):
        final_helpers = list(sanitize_lean_artifact_texts(helpers_raw))
    if helpers and final_helpers:
        helpers = merge_context_helpers(helpers, final_helpers)
    elif final_helpers:
        helpers = final_helpers
    return sanitize_lean_artifact_text(proof), helpers


def _summary_root_certificate(summary: Dict[str, Any]) -> Dict[str, Any]:
    raw = summary.get("root_proof_certificate")
    if isinstance(raw, dict) and raw:
        return raw
    dossier = summary.get("proof_dossier")
    if isinstance(dossier, dict):
        raw = dossier.get("root_proof_certificate")
        if isinstance(raw, dict) and raw:
            return raw
    return {}


def _summary_verified_helpers(summary: Dict[str, Any]) -> List[str]:
    dossier = summary.get("proof_dossier")
    if not isinstance(dossier, dict):
        return []
    raw_helpers = dossier.get("verified_helpers")
    if not isinstance(raw_helpers, list):
        return []
    helpers: List[str] = []
    for item in raw_helpers:
        if isinstance(item, str):
            text = item.strip()
        elif isinstance(item, dict):
            text = str(
                item.get("source") or item.get("block") or item.get("text") or ""
            ).strip()
        else:
            text = ""
        if text:
            sanitized = sanitize_lean_artifact_text(text)
            if sanitized:
                helpers.append(sanitized)
    return helpers


def _root_replay_for_export(
    summary: Dict[str, Any],
    solved_turn: Optional[Dict[str, Any]],
) -> Tuple[str, List[str]]:
    """Return the proof/helper set that should replay the root theorem.

    Modern mini-prover runs persist the accepted root proof in
    ``summary.final_proof``.  The turn stream may also contain successful child
    sessions; those are useful evidence, but they are not root replay records.
    """

    proof, helpers = _summary_replay(summary)
    if proof:
        return proof, helpers
    if solved_turn is None:
        return "", []
    if not _solved_turn_has_root_finalization_evidence(solved_turn):
        return "", []
    proof = _proof_for_replay(solved_turn)
    if not proof:
        return "", []
    return proof, _helpers_for_replay(solved_turn)


def _solved_turn_has_root_finalization_evidence(rec: Dict[str, Any]) -> bool:
    verdict = str(rec.get("root_finalization_verdict") or "").strip()
    if verdict in {"root_finalization_accepted", "root_finalization_already_applied"}:
        return True
    if rec.get("root_finalization_accepted") is True:
        return True
    return False


def _helpers_for_replay(rec: Dict[str, Any]) -> List[str]:
    replay_helpers = list(rec.get("replay_helpers") or [])
    if replay_helpers:
        return list(sanitize_lean_artifact_texts(replay_helpers))
    context_helpers = list(rec.get("dossier_context_helpers") or [])
    fresh_helpers = list(rec.get("extracted_helpers") or [])
    return list(
        sanitize_lean_artifact_texts(
            merge_context_helpers(context_helpers, fresh_helpers)
        )
    )


def _proof_for_replay(rec: Dict[str, Any]) -> str:
    """Return the proof Lean accepted for root replay."""

    accepted = rec.get("accepted_proof")
    if isinstance(accepted, str) and accepted.strip():
        return sanitize_lean_artifact_text(accepted)
    extracted = rec.get("extracted_proof")
    if isinstance(extracted, str) and extracted.strip():
        return sanitize_lean_artifact_text(extracted)
    return ""


def _replace_theorem_sorry(
    src: str,
    theorem_name: str,
    proof: str,
) -> Optional[str]:
    """Replace the trailing ``sorry`` of ``theorem <theorem_name>`` with proof."""
    # Find the theorem header line by name.
    m = None
    for mm in _THEOREM_HEADER_RE.finditer(src):
        if mm.group(1) == theorem_name:
            m = mm
            break
    if m is None:
        return None
    # Find the ``:=`` separator after the header.
    rest = src[m.start() :]
    # Match either `:= sorry` (inline) or `:=\n<whitespace>sorry`.
    sep = re.search(r":=\s*sorry\b", rest)
    if not sep:
        return None
    # Compute absolute positions.
    abs_sep_start = m.start() + sep.start()
    abs_sep_end = m.start() + sep.end()
    # Build replacement: `:= <proof>`. Keep proof on its own line for readability.
    proof_block = proof.strip()
    if (
        not proof_block.startswith("by")
        and not proof_block.startswith("(")
        and "\n" not in proof_block.rstrip()[:64]
    ):
        # Single-line term proof — keep inline.
        replacement = f":= {proof_block}"
    else:
        replacement = f":= {proof_block}"
    return src[:abs_sep_start] + replacement + src[abs_sep_end:]


def _insert_helpers(src: str, theorem_name: str, helpers: List[str]) -> str:
    """Insert helper declarations above the theorem (separated by blank lines)."""
    if not helpers:
        return src
    m = None
    for mm in _THEOREM_HEADER_RE.finditer(src):
        if mm.group(1) == theorem_name:
            m = mm
            break
    if m is None:
        return src  # shouldn't happen — caller already verified
    # Find the actual line start (could be preceded by docstring `/-- ... -/`).
    line_start = src.rfind("\n", 0, m.start())
    insert_pos = line_start + 1 if line_start >= 0 else m.start()
    # Walk back over the docstring block if present so helpers go ABOVE the docstring,
    # producing: preamble → helpers → docstring → theorem.
    pre = src[:insert_pos]
    # Strip trailing whitespace-only lines from `pre` — find the last non-blank end
    pre_rstripped = pre.rstrip()
    if pre_rstripped.endswith("-/"):
        # docstring block — find its start
        ds_start = pre_rstripped.rfind("/--")
        if ds_start >= 0:
            insert_pos = ds_start
            # Trim trailing whitespace in the prefix before that
            while insert_pos > 0 and src[insert_pos - 1] in " \t\n":
                insert_pos -= 1
            insert_pos += 1  # leave one trailing newline
    helper_block = "\n\n".join(h.strip() for h in helpers if h.strip())
    return src[:insert_pos] + "\n" + helper_block + "\n\n" + src[insert_pos:]


def _summary_answer_visibility(summary: Dict[str, Any]) -> str:
    raw = str(summary.get("answer_visibility") or "").strip().lower()
    if raw in {"opaque", "visible"}:
        return raw
    if summary.get("opaque_mode") is False:
        return "visible"
    # Legacy summaries predate the explicit field and were produced by the
    # answer-safe path, so keep them in the opaque/no-answer export pool.
    return "opaque"


def _summary_visibility_flags(summary: Dict[str, Any]) -> Dict[str, Optional[bool]]:
    """Raw answer-visibility flags recorded by the run, when present."""

    def flag(name: str) -> Optional[bool]:
        value = summary.get(name)
        return value if isinstance(value, bool) else None

    return {
        "opaque_mode": flag("opaque_mode"),
        "allow_official_answer_visibility": flag("allow_official_answer_visibility"),
        "official_answer_payload_present": flag("official_answer_payload_present"),
    }


def _visibility_comment(
    answer_visibility: str,
    *,
    opaque_mode: Optional[bool] = None,
    allow_official_answer_visibility: Optional[bool] = None,
    official_answer_payload_present: Optional[bool] = None,
) -> str:
    visibility = _normalize_answer_visibility(answer_visibility)
    flag_bits: List[str] = []
    if opaque_mode is not None:
        flag_bits.append(f"opaque_mode={'true' if opaque_mode else 'false'}")
    if allow_official_answer_visibility is not None:
        flag_bits.append(
            "allow_official_answer_visibility="
            f"{'true' if allow_official_answer_visibility else 'false'}"
        )
    if official_answer_payload_present is not None:
        flag_bits.append(
            "official_answer_payload_present="
            f"{'true' if official_answer_payload_present else 'false'}"
        )
    flags = "; ".join(flag_bits)
    if visibility == "visible":
        suffix = (
            flags
            if flags
            else "opaque_mode=false; official answer definitions included"
        )
        return f"-- mini-prover answer visibility: visible ({suffix})"
    if flags:
        return f"-- mini-prover answer visibility: opaque ({flags})"
    return "-- mini-prover answer visibility: opaque (opaque_mode=true)"


def _normalize_answer_visibility(answer_visibility: str) -> str:
    return (
        "visible"
        if str(answer_visibility or "").strip().lower() == "visible"
        else "opaque"
    )


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(PROJECT_ROOT))
    except ValueError:
        return str(path)


def _write_text_atomic(path: Path, text: str) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(
        prefix=f".{target.name}.",
        suffix=".tmp",
        dir=str(target.parent),
    )
    os.close(fd)
    tmp_path = Path(tmp_name)
    try:
        tmp_path.write_text(text, encoding="utf-8")
        tmp_path.replace(target)
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def _valid_export_problem_name(name: str) -> bool:
    return _EXPORT_PROBLEM_NAME_RE.fullmatch(str(name or "").strip()) is not None


def _single_run_export_identity(
    summary: Dict[str, Any],
) -> Optional[Tuple[str, str, Optional[Dict[str, Any]]]]:
    """Return ``(logical_name, safe_stem, immutable_snapshot)``.

    Legacy summaries only support the historical plain Putnam identifier.
    New theorem-project summaries may use qualified/quoted Lean names, but
    their filesystem stem is always independently derived and verified.
    """

    logical_name = str(summary.get("problem") or "").strip()
    raw_snapshot = summary.get("theorem_project_export")
    snapshot = dict(raw_snapshot) if isinstance(raw_snapshot, dict) else None
    if snapshot is None:
        if not _valid_export_problem_name(logical_name):
            return None
        return logical_name, logical_name, None
    if (
        not is_valid_lean_qualified_name(logical_name)
        or str(snapshot.get("theorem_name") or "").strip() != logical_name
        or not is_valid_lean_qualified_name(
            str(snapshot.get("declaration_name") or logical_name).strip()
        )
    ):
        return None
    snapshot_adapter = str(snapshot.get("adapter_id") or "").strip()
    if snapshot_adapter not in {"generic", PUTNAMBENCH_ADAPTER_ID}:
        return None
    summary_adapter = str(summary.get("theorem_project_adapter") or "").strip()
    project_record = summary.get("theorem_project")
    project_adapter = (
        str(project_record.get("adapter_id") or "").strip()
        if isinstance(project_record, dict)
        else ""
    )
    if any(
        value and value != snapshot_adapter
        for value in (summary_adapter, project_adapter)
    ):
        return None
    if snapshot_adapter == GENERIC_ADAPTER_ID and not _generic_snapshot_is_source_bound(
        summary,
        snapshot,
    ):
        return None
    if snapshot_adapter == GENERIC_ADAPTER_ID:
        assert isinstance(project_record, dict)
        project_path_text = str(project_record.get("project_path") or "").strip()
        lean_file_text = str(project_record.get("lean_file") or "").strip()
        if not project_path_text or not lean_file_text:
            return None
        safe_stem = generic_theorem_artifact_slug(
            logical_name,
            project_path=Path(project_path_text),
            lean_file=Path(lean_file_text),
            imports=tuple(str(item) for item in project_record.get("imports") or ()),
            source_dirs=tuple(
                Path(str(item.get("path") or ""))
                for item in project_record.get("source_dirs") or ()
                if isinstance(item, dict) and str(item.get("path") or "").strip()
            ),
        )
    else:
        safe_stem = theorem_artifact_slug(logical_name)
    recorded_stem = str(snapshot.get("artifact_slug") or safe_stem).strip()
    if recorded_stem != safe_stem or not _valid_export_problem_name(safe_stem):
        return None
    return logical_name, safe_stem, snapshot


def _recorded_export_identity_for_cleanup(
    summary: Dict[str, Any],
) -> Optional[Tuple[str, str]]:
    """Recover a safe stable stem without requiring current source freshness."""

    logical_name = str(summary.get("problem") or "").strip()
    raw_snapshot = summary.get("theorem_project_export")
    if not isinstance(raw_snapshot, dict):
        return (
            (logical_name, logical_name)
            if _valid_export_problem_name(logical_name)
            else None
        )
    snapshot = dict(raw_snapshot)
    if (
        not is_valid_lean_qualified_name(logical_name)
        or str(snapshot.get("theorem_name") or "").strip() != logical_name
    ):
        return None
    adapter_id = str(snapshot.get("adapter_id") or "").strip()
    if adapter_id == GENERIC_ADAPTER_ID:
        project_record = summary.get("theorem_project")
        if not isinstance(project_record, dict):
            return None
        snapshot_declaration = str(snapshot.get("declaration_name") or "").strip()
        if (
            str(project_record.get("theorem_name") or "").strip() != logical_name
            or str(project_record.get("declaration_name") or "").strip()
            != snapshot_declaration
            or not is_valid_lean_qualified_name(snapshot_declaration)
            or str(project_record.get("source_sha256") or "").strip()
            != str(snapshot.get("source_sha256") or "").strip()
            or str(summary.get("theorem_project_adapter") or "").strip()
            not in {"", GENERIC_ADAPTER_ID}
        ):
            return None
        recorded_hash = str(project_record.get("input_spec_hash") or "").strip()
        hash_payload = dict(project_record)
        hash_payload.pop("input_spec_hash", None)
        actual_hash = hashlib.sha256(
            json.dumps(
                hash_payload,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        if (
            not recorded_hash
            or actual_hash != recorded_hash
            or recorded_hash
            != str(summary.get("theorem_project_input_hash") or "").strip()
            or str(project_record.get("adapter_id") or "").strip() != GENERIC_ADAPTER_ID
        ):
            return None
        project_path = str(project_record.get("project_path") or "").strip()
        lean_file = str(project_record.get("lean_file") or "").strip()
        support_records = project_record.get("source_dirs")
        if (
            not project_path
            or not lean_file
            or not isinstance(support_records, list)
            or str(snapshot.get("source_path") or "").strip() != lean_file
            or str(summary.get("lean_file") or "").strip() != lean_file
        ):
            return None
        safe_stem = generic_theorem_artifact_slug(
            logical_name,
            project_path=Path(project_path),
            lean_file=Path(lean_file),
            imports=tuple(str(item) for item in project_record.get("imports") or ()),
            source_dirs=tuple(
                Path(str(item.get("path") or ""))
                for item in support_records
                if isinstance(item, dict) and str(item.get("path") or "").strip()
            ),
        )
    elif adapter_id == PUTNAMBENCH_ADAPTER_ID:
        safe_stem = theorem_artifact_slug(logical_name)
    else:
        return None
    if str(
        snapshot.get("artifact_slug") or ""
    ).strip() != safe_stem or not _valid_export_problem_name(safe_stem):
        return None
    return logical_name, safe_stem


def _generic_snapshot_is_source_bound(
    summary: Dict[str, Any],
    snapshot: Dict[str, Any],
) -> bool:
    """Verify generic reconstruction data against its immutable source spec."""

    project_record = summary.get("theorem_project")
    if not isinstance(project_record, dict):
        return False
    recorded_spec_hash = str(project_record.get("input_spec_hash") or "").strip()
    if (
        not recorded_spec_hash
        or recorded_spec_hash
        != str(summary.get("theorem_project_input_hash") or "").strip()
    ):
        return False
    hash_payload = dict(project_record)
    hash_payload.pop("input_spec_hash", None)
    actual_spec_hash = hashlib.sha256(
        json.dumps(
            hash_payload,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    if actual_spec_hash != recorded_spec_hash:
        return False
    project_path_text = str(project_record.get("project_path") or "").strip()
    project_path = Path(project_path_text).expanduser()
    if (
        not project_path_text
        or not project_path.is_absolute()
        or not project_path.is_dir()
    ):
        return False
    support_records = project_record.get("source_dirs")
    if not isinstance(support_records, list):
        return False
    try:
        if (
            theorem_project_environment_hash(
                project_path,
                (
                    Path(str(path))
                    for path in dict(
                        project_record.get("project_import_sources") or {}
                    ).values()
                ),
            )
            != str(project_record.get("project_input_hash") or "").strip()
        ):
            return False
        for support_record in support_records:
            if not isinstance(support_record, dict):
                return False
            support_path_text = str(support_record.get("path") or "").strip()
            support_path = Path(support_path_text).expanduser()
            if (
                not support_path_text
                or not support_path.is_absolute()
                or not support_path.is_dir()
                or theorem_project_tree_content_hash(support_path)
                != str(support_record.get("content_hash") or "").strip()
            ):
                return False
            raw_compiled_roots = support_record.get("compiled_module_roots")
            if not isinstance(raw_compiled_roots, list):
                return False
            compiled_roots = tuple(
                Path(str(path)).expanduser() for path in raw_compiled_roots
            )
            if any(
                not path.is_absolute() or not path.is_dir() for path in compiled_roots
            ):
                return False
            if (
                theorem_project_compiled_content_hash(compiled_roots)
                != str(support_record.get("compiled_content_hash") or "").strip()
            ):
                return False
            build_project_text = str(
                support_record.get("build_project_path") or ""
            ).strip()
            if build_project_text:
                build_project = Path(build_project_text).expanduser()
                if not build_project.is_absolute() or not build_project.is_dir():
                    return False
                if (
                    theorem_project_environment_hash(
                        build_project,
                        (
                            Path(str(path))
                            for path in dict(
                                support_record.get("build_import_sources") or {}
                            ).values()
                        ),
                    )
                    != str(support_record.get("build_project_input_hash") or "").strip()
                ):
                    return False
    except (OSError, UnicodeError, TypeError, ValueError):
        return False
    source_path_text = str(snapshot.get("source_path") or "").strip()
    if (
        not source_path_text
        or source_path_text != str(project_record.get("lean_file") or "").strip()
        or source_path_text != str(summary.get("lean_file") or "").strip()
    ):
        return False
    source_path = Path(source_path_text).expanduser()
    if not source_path.is_absolute() or not source_path.is_file():
        return False
    try:
        source = source_path.read_text(encoding="utf-8")
        source_hash = hashlib.sha256(source.encode("utf-8")).hexdigest()
        if source_hash != str(project_record.get("source_sha256") or "").strip():
            return False
        if source_hash != str(snapshot.get("source_sha256") or "").strip():
            return False
        declaration = select_lean_theorem(
            scan_lean_theorems(source),
            str(project_record.get("theorem_name") or ""),
        )
        expected_preamble, target_scoped_prefix = theorem_reusable_preamble(
            source,
            declaration,
            tuple(project_record.get("imports") or ()),
        )
        target_omit_variables = active_include_variables(
            source,
            declaration.declaration_start,
        )
    except (OSError, UnicodeError, TypeError, ValueError):
        return False
    source_statement_type = str(
        project_record.get("source_statement_type") or declaration.statement_type
    ).strip()
    exported_statement_type = str(
        project_record.get("elaborated_statement_type") or source_statement_type
    ).strip()
    return bool(
        declaration.canonical_name
        == str(snapshot.get("theorem_name") or "").strip()
        == str(project_record.get("theorem_name") or "").strip()
        and declaration.source_name
        == str(snapshot.get("declaration_name") or "").strip()
        and declaration.universe_suffix
        == str(snapshot.get("declaration_universe_suffix") or "").strip()
        and declaration.public is (snapshot.get("declaration_public") is True)
        and str(snapshot.get("target_scoped_prefix") or "").strip()
        == str(project_record.get("target_scoped_prefix") or "").strip()
        == target_scoped_prefix
        and list(snapshot.get("target_omit_variables") or ())
        == list(project_record.get("target_omit_variables") or ())
        == list(target_omit_variables)
        and declaration.statement_type.strip() == source_statement_type
        and exported_statement_type == str(snapshot.get("statement_type") or "").strip()
        and expected_preamble.rstrip() == str(snapshot.get("preamble") or "").rstrip()
        and str(snapshot.get("docstring") or "").strip()
        == str(project_record.get("description") or "").strip()
    )


def _export_root_name_candidates(stem: str) -> List[str]:
    raw = str(stem or "").strip()
    without_version = re.sub(r"_v[1-9][0-9]*$", "", raw)
    candidates = [
        raw,
        without_version,
        re.sub(r"_visible$", "", without_version),
        re.sub(r"_visible$", "", raw),
    ]
    ordered: List[str] = []
    for candidate in candidates:
        if candidate and candidate not in ordered:
            ordered.append(candidate)
    return ordered


def _export_root_name_for_content(stem: str, content: str) -> str:
    declared = set(_THEOREM_HEADER_RE.findall(str(content or "")))
    for candidate in _export_root_name_candidates(stem):
        if candidate in declared:
            return candidate
    candidates = _export_root_name_candidates(stem)
    return candidates[-1] if candidates else str(stem or "").strip()


def _remove_export_navigation_artifacts(
    solved_dir: Path,
    stem: str,
    *,
    remove_shared_index: bool = True,
) -> None:
    clean_stem = str(stem or "").strip()
    if not clean_stem:
        return
    root = Path(solved_dir)
    candidates = [
        root / f"{clean_stem}.source_map.json",
        root / "depgraphs" / f"{clean_stem}.json",
        root / "depgraphs" / f"{clean_stem}.html",
        root / "depgraphs" / f"{clean_stem}.source.html",
        root / "depgraphs" / f"{clean_stem}.source_map.json",
    ]
    if remove_shared_index:
        candidates.append(root / "depgraphs" / "index.html")
    for path in candidates:
        try:
            path.unlink()
        except FileNotFoundError:
            pass
        except Exception:
            pass


def _output_stem_for_solve(
    problem_name: str,
    *,
    answer_visibility: str,
    solve_index: int,
    solve_count: int,
) -> str:
    if not _valid_export_problem_name(problem_name):
        raise ValueError(f"unsafe problem name for export: {problem_name!r}")
    base = (
        f"{problem_name}_visible"
        if _normalize_answer_visibility(answer_visibility) == "visible"
        else problem_name
    )
    return f"{base}_v{solve_index}" if solve_count > 1 else base


def _next_single_run_output(
    solved_dir: Path,
    problem_name: str,
    *,
    answer_visibility: str,
) -> Tuple[str, int, int]:
    """Return the next non-destructive output stem for one just-finished run.

    Batch exports rebuild the whole solved set and can name all versions from
    run chronology. A live mini-prover auto-export must not scan/rewrite older
    solved runs, so it only looks at occupied filenames and picks the next free
    slot.
    """

    base = _output_stem_for_solve(
        problem_name,
        answer_visibility=answer_visibility,
        solve_index=1,
        solve_count=1,
    )
    occupied_versions = set()
    if (solved_dir / f"{base}.lean").exists():
        occupied_versions.add(1)

    version_re = re.compile(rf"^{re.escape(base)}_v([1-9][0-9]*)\.lean$")
    if solved_dir.exists():
        for path in solved_dir.iterdir():
            if not path.is_file():
                continue
            match = version_re.match(path.name)
            if match:
                occupied_versions.add(int(match.group(1)))

    if not occupied_versions:
        return base, 1, 1

    version = max(occupied_versions) + 1
    while (solved_dir / f"{base}_v{version}.lean").exists():
        version += 1
    return f"{base}_v{version}", version, version


def _preamble_for_export(
    problem: Any,
    answer_visibility: str = "opaque",
) -> Optional[str]:
    if _normalize_answer_visibility(answer_visibility) == "visible":
        value = str(getattr(problem, "lean_preamble", "") or problem.preamble)
    else:
        value = str(problem.preamble)
    clean, _prefix, _variables = decode_theorem_target_context(value)
    return clean.rstrip()


def _build_solved_file(
    problem_name: str,
    proof: str,
    helpers: List[str],
    answer_visibility: str = "opaque",
    opaque_mode: Optional[bool] = None,
    allow_official_answer_visibility: Optional[bool] = None,
    official_answer_payload_present: Optional[bool] = None,
    extra_imports: Sequence[str] = (),
    extra_theory_sources: Sequence[str] = (),
) -> Optional[str]:
    """Reconstruct a standalone Lean source.

    The mini-prover Lean-checked the proof against ``example : <statement_type>
    := <proof>`` where ``statement_type`` is the FORALL form (``∀ binders,
    type``). The original PutnamBench file uses explicit binders
    (``theorem foo (a : T) : type``), so the proof's leading ``intro`` would
    fail when spliced into the original theorem header (binders are already
    in scope, no quantifier to introduce). Both forms have the same theorem
    type, so we emit the theorem with the FORALL form to keep the proof
    intact.

    Output shape:
        {run-visibility preamble}

        {helpers (if any)}

        {docstring (if present)}
        theorem <name> : <forall_statement_type> := <proof>
    """
    if not _valid_export_problem_name(problem_name):
        return None
    src_path = PUTNAM_SRC / f"{problem_name}.lean"
    if not src_path.exists():
        return None
    try:
        problem = load_putnam_problem(src_path)
    except Exception:
        return None

    preamble = _preamble_for_export(
        problem,
        answer_visibility=answer_visibility,
    )
    if preamble is None:
        return None
    clean_extra_imports = tuple(
        dict.fromkeys(
            str(module or "").strip()
            for module in extra_imports
            if str(module or "").strip()
        )
    )
    if clean_extra_imports:
        preamble_lines = preamble.splitlines()
        insert_at = 0
        while insert_at < len(preamble_lines) and (
            not preamble_lines[insert_at].strip()
            or preamble_lines[insert_at].lstrip().startswith("import ")
        ):
            insert_at += 1
        existing = {
            line.strip()[len("import ") :].strip()
            for line in preamble_lines
            if line.strip().startswith("import ")
        }
        additions = [
            f"import {module}"
            for module in clean_extra_imports
            if module not in existing
        ]
        preamble_lines[insert_at:insert_at] = additions
        preamble = "\n".join(preamble_lines)

    parts: List[str] = []
    parts.append(f"-- Solved by mini-prover. Source: {_display_path(src_path)}")
    parts.append(
        _visibility_comment(
            answer_visibility,
            opaque_mode=opaque_mode,
            allow_official_answer_visibility=allow_official_answer_visibility,
            official_answer_payload_present=official_answer_payload_present,
        )
    )
    parts.append(preamble)
    clean_theory_sources = []
    for source in extra_theory_sources:
        clean_source = str(source or "").strip()
        if not clean_source:
            continue
        # Mini modules compile with an explicit package policy, but the option
        # must not leak past an inlined module boundary into the conjecture or
        # its run-local helpers. The source hash was checked before this
        # portability transform.
        clean_source = "\n".join(
            line
            for line in clean_source.splitlines()
            if line.strip() != "set_option autoImplicit false"
        ).strip()
        if clean_source:
            clean_theory_sources.append(clean_source)
    if clean_theory_sources:
        parts.append("")
        parts.append("\n\n".join(clean_theory_sources))
    artifact_helpers = list(sanitize_lean_artifact_texts(helpers))
    if artifact_helpers:
        parts.append("")
        parts.append("\n\n".join(artifact_helpers))
    parts.append("")
    if problem.docstring.strip():
        parts.append(problem.docstring.strip())
    proof_block = sanitize_lean_artifact_text(proof)
    declaration_block = (
        f"theorem {problem.theorem_name} : {problem.statement_type.strip()} := "
        f"{proof_block}"
    )
    target_omit_variables = tuple(getattr(problem, "target_omit_variables", ()) or ())
    if target_omit_variables:
        declaration_block = (
            f"omit {' '.join(target_omit_variables)} in\n{declaration_block}"
        )
    proof_scoped_prefix = theorem_proof_scoped_prefix(
        str(getattr(problem, "target_scoped_prefix", "") or "")
    )
    if proof_scoped_prefix:
        declaration_block = f"{proof_scoped_prefix}\n{declaration_block}"
    parts.append(declaration_block)
    return "\n".join(parts) + "\n"


def _build_theorem_project_solved_file(
    problem_record: Dict[str, Any],
    proof: str,
    helpers: List[str],
    *,
    extra_imports: Sequence[str] = (),
    extra_theory_sources: Sequence[str] = (),
) -> Optional[str]:
    """Reconstruct a solved source from the run's immutable input snapshot."""

    theorem_name = str(problem_record.get("theorem_name") or "").strip()
    declaration_name = str(
        problem_record.get("declaration_name") or theorem_name
    ).strip()
    universe_suffix = str(
        problem_record.get("declaration_universe_suffix") or ""
    ).strip()
    public_prefix = (
        "public " if problem_record.get("declaration_public") is True else ""
    )
    statement_type = str(problem_record.get("statement_type") or "").strip()
    if (
        not is_valid_lean_qualified_name(theorem_name)
        or not is_valid_lean_qualified_name(declaration_name)
        or not is_valid_lean_universe_suffix(universe_suffix)
        or not statement_type
    ):
        return None
    preamble = str(problem_record.get("preamble") or "").rstrip()
    clean_extra_imports = tuple(
        dict.fromkeys(
            str(module or "").strip()
            for module in extra_imports
            if str(module or "").strip()
        )
    )
    if clean_extra_imports:
        try:
            preamble = merge_imports(preamble, clean_extra_imports)
        except ValueError:
            return None

    clean_theory_sources: list[str] = []
    for source in extra_theory_sources:
        clean_source = str(source or "").strip()
        if not clean_source:
            continue
        clean_source = "\n".join(
            line
            for line in clean_source.splitlines()
            if line.strip() != "set_option autoImplicit false"
        ).strip()
        if clean_source:
            clean_theory_sources.append(clean_source)
    # Published Mini theory modules are root-level libraries. Generic target
    # preambles may leave ``namespace Foo`` open, so inlining a theory module
    # after the whole preamble would silently rename it to ``Foo.MiniTheory``.
    # Keep imports and root-level theory before the target's namespace/body;
    # run-local helpers remain after the preamble because that is the scope in
    # which Lean verified them during the run.
    import_prefix, scoped_preamble = split_lean_import_header(preamble)
    import_prefix = import_prefix.strip()
    scoped_preamble = scoped_preamble.strip()
    parts = ["-- Solved by mini-prover from a theorem-project input snapshot."]
    if import_prefix:
        parts.extend(("", import_prefix))
    if clean_theory_sources:
        parts.extend(("", "\n\n".join(clean_theory_sources)))
    if scoped_preamble:
        parts.extend(("", scoped_preamble))
    artifact_helpers = list(sanitize_lean_artifact_texts(helpers))
    if artifact_helpers:
        parts.extend(("", "\n\n".join(artifact_helpers)))
    description = str(problem_record.get("docstring") or "").strip()
    rendered_description = ""
    if description:
        if description.startswith("/--") and description.endswith("-/"):
            description = description[3:-2].strip()
        safe_description = description.replace("/-", "/ -").replace("-/", "- /")
        rendered_description = f"/-- {safe_description} -/"
    proof_block = sanitize_lean_artifact_text(proof)
    # The exact type comes from Lean's elaborated declaration and its pretty
    # printer may alpha-rename universe parameters (for example source ``u``
    # becomes ``u_1``). Reusing the source suffix would bind the wrong level.
    # Let Lean re-generalize every level/name in the already-elaborated type
    # under a declaration-local autoImplicit scope instead.
    declaration_lines = ["set_option autoImplicit true in"]
    if rendered_description:
        declaration_lines.append(rendered_description)
    declaration_lines.append(
        f"{public_prefix}theorem {declaration_name} : {statement_type} := {proof_block}"
    )
    declaration_block = "\n".join(declaration_lines)
    target_scoped_prefix = theorem_proof_scoped_prefix(
        str(problem_record.get("target_scoped_prefix") or "")
    )
    target_omit_variables = tuple(
        str(item).strip()
        for item in problem_record.get("target_omit_variables") or ()
        if str(item).strip()
    )
    if target_omit_variables:
        declaration_block = (
            f"omit {' '.join(target_omit_variables)} in\n{declaration_block}"
        )
    if target_scoped_prefix:
        declaration_block = f"{target_scoped_prefix}\n{declaration_block}"
    parts.extend(("", declaration_block))
    # A wrapper or active section include must never silently change the
    # published signature after we render Lean's canonical type. Keep an
    # executable exact ascription in the artifact so both installation and
    # future recompilation fail if the named theorem acquires any extra binder.
    signature_check = (
        "set_option autoImplicit true in\n"
        f"example : {statement_type} := by exact @_root_.{theorem_name}"
    )
    if target_omit_variables:
        signature_check = (
            f"omit {' '.join(target_omit_variables)} in\n{signature_check}"
        )
    parts.extend(("", signature_check))
    return "\n".join(parts) + "\n"


# Lean exits 0 even when a declaration uses ``sorry``/``admit`` (it is a warning,
# not an error). The live verifier rejects these via
# ``parse_lean_output().sorry_count`` (lean_runner.py); the export backstop MUST
# apply the same gate or a sorry-containing helper/proof could be exported as
# "verified". ``admit`` is a Lean alias for ``sorry`` and emits the identical
# warning, so this single pattern covers both. We deliberately do NOT also match
# a bare ``sorryAx`` token: ``#print axioms`` is not run on this path, so that
# token only ever appears in echoed source/comments — matching it would
# false-positive (reject sound proofs) while being stricter than the live gate.
# NOTE: this fallback regex is a deliberate COPY of
# lean_parser._REAL_SORRY_WARNING_RE (kept in sync), NOT an import — it is used
# only when parse_lean_output is unavailable, so it must not depend on importing
# lean_parser. It matches single-quote AND backtick rendering, an optional
# "declaration " prefix, and is case-insensitive: exactly the live matcher.
_LEAN_SORRY_RE = re.compile(r"(?:declaration\s+)?uses\s+[`']sorry[`']", re.IGNORECASE)


def _export_lean_verdict(returncode: int, output: str) -> Tuple[bool, str]:
    """Decide whether an exported Lean compile counts as verified.

    Mirrors the live gate ``returncode == 0 and sorry_count == 0`` by reusing
    ``parse_lean_output`` for sorry detection, with a conservative textual
    fallback (the ``declaration uses 'sorry'`` warning) so a ``sorry``/``admit``
    can never slip through even if the parser fails to load. Pure (no
    subprocess) so it is unit-testable without a Lean toolchain.

    NOTE (residual, matches the live gate): trust-expanding axioms that are NOT
    ``sorry`` — custom ``axiom`` decls, ``native_decide``'s ``Lean.ofReduceBool``
    — are not detected here; a stricter backstop would run ``#print axioms`` with
    an allowlist (a policy decision with its own false-positive risk).
    """

    text = str(output or "")
    rc = int(returncode)
    sorry_detected = False
    try:
        from ensemble_prover.lean_parser import parse_lean_output

        parsed = parse_lean_output(text, rc)
        if int(getattr(parsed, "sorry_count", 0) or 0) > 0:
            sorry_detected = True
    except Exception:
        pass
    if not sorry_detected and _LEAN_SORRY_RE.search(text):
        sorry_detected = True
    if rc != 0:
        return False, text
    if sorry_detected:
        return False, (
            text + "\n[export-verify] rejected: proof/helper uses sorry "
            "(export soundness backstop)"
        )
    return True, text


# Axiom-usage audit (SafeVerify-equivalent trust surface). A compiled,
# sorry-free proof can still expand the trust base beyond the Lean kernel:
# ``native_decide`` pulls in ``Lean.ofReduceBool``/``Lean.trustCompiler``
# (trusting the whole compiler), ``@[implemented_by]`` + ``native_decide`` is
# the canonical way to prove ``False``, and custom ``axiom`` declarations are
# assumptions, not proofs. ``#print axioms <root>`` reports the transitive
# axiom closure of the root theorem; anything beyond the standard mathlib
# trust base fails the export.
_ALLOWED_EXPORT_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

_PRINT_AXIOMS_DEPENDS_RE = re.compile(
    r"'([^\r\n]+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]"
)
_PRINT_AXIOMS_NONE_RE = re.compile(
    r"'([^\r\n]+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms"
)


def _parse_print_axioms(output: str, theorem_name: str) -> Optional[List[str]]:
    """Extract the axiom list ``#print axioms`` reported for *theorem_name*.

    Returns ``[]`` for "does not depend on any axioms", the parsed list for
    the "depends on axioms: [...]" form, and ``None`` when no report for the
    theorem is present in *output* (callers must fail closed on ``None``).

    Name matching is EXACT, not dot-suffix: ``#print axioms putnam_x`` reports
    the fully-qualified name of the resolved declaration, and we always ask
    about the exact root name. Suffix matching would let a namespaced decoy
    (``Decoy.putnam_x``) whose clean report happens to appear in the same
    stdout satisfy the audit for the real ``putnam_x``. The "depends on
    axioms" form is scanned BEFORE the "no axioms" form so a dirty report can
    never be masked by a clean same-name report (dirty wins).
    """

    text = str(output or "")
    want = str(theorem_name or "").strip()
    if not want:
        return None

    for match in _PRINT_AXIOMS_DEPENDS_RE.finditer(text):
        if match.group(1).strip() == want:
            return [
                axiom.strip() for axiom in match.group(2).split(",") if axiom.strip()
            ]
    for match in _PRINT_AXIOMS_NONE_RE.finditer(text):
        if match.group(1).strip() == want:
            return []
    return None


def _axiom_audit_verdict(
    axioms: Optional[List[str]],
) -> Tuple[bool, List[str]]:
    """Return ``(ok, unexpected_axioms)`` for a parsed axiom report.

    A missing report (``None``) fails closed: the audit ran but produced no
    usable answer, so the export cannot claim the SafeVerify-equivalent
    guarantee.
    """

    if axioms is None:
        return False, []
    unexpected = sorted(set(axioms) - _ALLOWED_EXPORT_AXIOMS)
    return (not unexpected), unexpected


def _export_lean_env(extra_lean_paths: Sequence[Path]) -> Dict[str, str]:
    env = os.environ.copy()
    paths = tuple(
        dict.fromkeys(
            str(Path(path).resolve()) for path in extra_lean_paths if str(path).strip()
        )
    )
    if paths:
        env["LEAN_PATH"] = os.pathsep.join((*paths, env.get("LEAN_PATH", ""))).rstrip(
            os.pathsep
        )
    return env


def _audit_exported_axioms(
    content: str,
    theorem_name: str,
    *,
    scratch_dir: Path,
    lean_project_dir: Optional[Path] = None,
    timeout_s: float = 180.0,
    extra_lean_paths: Sequence[Path] = (),
) -> Tuple[bool, List[str], List[str], str]:
    """Run ``#print axioms`` on *content*'s root theorem.

    Returns ``(ok, axioms, unexpected, output)``. Any infrastructure failure
    (compile error of the audit file, timeout, missing report, unusable
    theorem name) fails closed with ``ok=False``.
    """

    theorem_name = str(theorem_name or "").strip()
    if theorem_name.startswith("_root_."):
        theorem_name = theorem_name[len("_root_.") :]
    if not is_valid_lean_qualified_name(theorem_name):
        return (
            False,
            [],
            [],
            f"unauditable theorem name: {theorem_name!r} (must be a valid "
            "Lean qualified identifier)",
        )
    project_dir = (
        Path(lean_project_dir)
        if lean_project_dir is not None
        else PROJECT_ROOT / "external" / "PutnamBench" / "lean4"
    )
    # Machine-generated unique name (NOT derived from theorem_name): keeps
    # concurrent audits of the same theorem from racing on one shared path,
    # and prevents an untrusted ``problem`` value (e.g. "../../evil") from
    # steering the write/unlink outside scratch_dir.
    scratch_dir.mkdir(parents=True, exist_ok=True)
    fd, audit_name = tempfile.mkstemp(
        prefix=".axiom_audit_", suffix=".tmp.lean", dir=str(scratch_dir)
    )
    os.close(fd)
    audit_path = Path(audit_name)
    # Force resolution from the root namespace. The reconstructed source can
    # intentionally leave its target namespace open, in which case an
    # unqualified directive would look for ``Foo.Foo.target``.
    audit_path.write_text(
        f"{content}\n#print axioms _root_.{theorem_name}\n", encoding="utf-8"
    )
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(audit_path.resolve())],
            cwd=str(project_dir),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=max(1.0, float(timeout_s or 180.0)),
            check=False,
            env=sanitized_subprocess_environment(
                _export_lean_env(extra_lean_paths)
            ),
        )
        output = str(proc.stdout or "")
        returncode = int(proc.returncode)
    except Exception as exc:
        return False, [], [], f"{type(exc).__name__}: {exc}"
    finally:
        try:
            audit_path.unlink()
        except Exception:
            pass
    axioms = _parse_print_axioms(output, theorem_name)
    ok, unexpected = _axiom_audit_verdict(axioms)
    # The audit file is the verified content plus one directive, so a
    # non-zero exit means the audit itself is unreliable — fail closed even
    # if a parseable report happens to be present.
    if returncode != 0:
        return False, list(axioms or []), unexpected, output
    return ok, list(axioms or []), unexpected, output


def _verify_exported_lean(
    lean_path: Path,
    *,
    lean_project_dir: Optional[Path] = None,
    timeout_s: float = 180.0,
    extra_lean_paths: Sequence[Path] = (),
) -> Tuple[bool, str]:
    project_dir = (
        Path(lean_project_dir)
        if lean_project_dir is not None
        else PROJECT_ROOT / "external" / "PutnamBench" / "lean4"
    )
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(Path(lean_path).resolve())],
            cwd=str(project_dir),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=max(1.0, float(timeout_s or 180.0)),
            check=False,
            env=sanitized_subprocess_environment(
                _export_lean_env(extra_lean_paths)
            ),
        )
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}"
    return _export_lean_verdict(proc.returncode, str(proc.stdout or ""))


def _build_export_project_imports(
    project_imports: Sequence[str],
    *,
    lean_project_dir: Optional[Path],
    timeout_s: float,
) -> Tuple[bool, str]:
    """Build exact project module targets needed by an export or later audit."""

    build_targets = tuple(
        dict.fromkeys(
            str(module or "").strip()
            for module in project_imports
            if str(module or "").strip()
        )
    )
    if not build_targets:
        return True, ""
    if lean_project_dir is None:
        return False, "project import targets have no Lean project"
    try:
        build = subprocess.run(
            ["lake", "build", *build_targets],
            cwd=str(Path(lean_project_dir)),
            env=sanitized_subprocess_environment(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=max(1.0, float(timeout_s or 180.0)),
            check=False,
        )
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}"
    if int(build.returncode) != 0:
        return False, str(build.stdout or "")
    return True, str(build.stdout or "")


def _build_export_support_projects(
    support_project_builds: Mapping[str, Sequence[str]],
    *,
    timeout_s: float,
) -> Tuple[bool, str]:
    for raw_project, raw_targets in dict(support_project_builds or {}).items():
        project = Path(str(raw_project)).expanduser()
        targets = tuple(
            dict.fromkeys(
                str(target or "").strip()
                for target in list(raw_targets or ())
                if str(target or "").strip()
            )
        )
        if not project.is_absolute() or not project.is_dir():
            return False, f"invalid supporting Lean project: {project}"
        try:
            build = subprocess.run(
                ["lake", "build", *targets],
                cwd=str(project),
                env=sanitized_subprocess_environment(),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=max(1.0, float(timeout_s or 180.0)),
                check=False,
            )
        except Exception as exc:
            return False, f"{type(exc).__name__}: {exc}"
        if int(build.returncode) != 0:
            return False, str(build.stdout or "")
    return True, ""


def _install_exported_lean(
    out_path: Path,
    content: str,
    *,
    verify_lean: bool,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
    theorem_name: str = "",
    extra_lean_paths: Sequence[Path] = (),
    project_imports: Sequence[str] = (),
    support_project_builds: Optional[Mapping[str, Sequence[str]]] = None,
) -> Tuple[bool, str, str, Tuple[str, ...]]:
    """Write ``content`` to ``out_path`` only after optional kernel checking.

    When *theorem_name* is provided, a successful kernel check is followed by
    an axiom-usage audit (``#print axioms``): the export is rejected when the
    root theorem's transitive axiom closure goes beyond the standard trust
    base (``propext``/``Classical.choice``/``Quot.sound``) — e.g. ``sorryAx``,
    ``native_decide``'s ``Lean.ofReduceBool``, or custom ``axiom`` decls.
    """

    if not verify_lean:
        out_path.write_text(content, encoding="utf-8")
        return False, "", "", ()
    if not str(theorem_name or "").strip():
        # Fail CLOSED: a verified install without an auditable root name
        # would silently skip the axiom backstop, making "no audit ran"
        # indistinguishable from "audit passed".
        return (
            False,
            "axiom_audit_failed",
            "[export-verify] rejected: no root theorem name supplied for "
            "the axiom audit (fail closed)",
            (),
        )
    build_ok, build_output = _build_export_project_imports(
        project_imports,
        lean_project_dir=lean_project_dir,
        timeout_s=lean_timeout_s,
    )
    if not build_ok:
        return (
            False,
            "project_import_build_failed",
            f"[export-verify] {build_output}",
            (),
        )
    support_ok, support_output = _build_export_support_projects(
        support_project_builds or {},
        timeout_s=lean_timeout_s,
    )
    if not support_ok:
        return (
            False,
            "support_project_build_failed",
            f"[export-verify] {support_output}",
            (),
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    temp_fd, temp_name = tempfile.mkstemp(
        prefix=f".{out_path.stem}.verify.",
        suffix=".tmp.lean",
        dir=str(out_path.parent),
    )
    os.close(temp_fd)
    temp_path = Path(temp_name)
    temp_path.write_text(content, encoding="utf-8")
    export_verified, verification_output = _verify_exported_lean(
        temp_path,
        lean_project_dir=lean_project_dir,
        timeout_s=lean_timeout_s,
        extra_lean_paths=extra_lean_paths,
    )
    if not export_verified:
        try:
            temp_path.unlink()
        except Exception:
            pass
        return False, "lean_rejected", verification_output, ()
    axioms: Tuple[str, ...] = ()
    if theorem_name:
        audit_ok, audit_axioms, unexpected, audit_output = _audit_exported_axioms(
            content,
            theorem_name,
            scratch_dir=out_path.parent,
            lean_project_dir=lean_project_dir,
            timeout_s=lean_timeout_s,
            extra_lean_paths=extra_lean_paths,
        )
        axioms = tuple(audit_axioms)
        if not audit_ok:
            try:
                temp_path.unlink()
            except Exception:
                pass
            status = "axiom_rejected" if unexpected else "axiom_audit_failed"
            note = (
                f"[export-verify] rejected: unexpected axioms {unexpected} "
                "(export axiom-audit backstop)"
                if unexpected
                else "[export-verify] rejected: axiom audit produced no "
                "usable #print axioms report (fail closed)"
            )
            return (
                False,
                status,
                f"{verification_output}\n{note}\n{audit_output}",
                axioms,
            )
    if out_path.exists():
        publish_mode = out_path.stat().st_mode & 0o777
    else:
        # Solved artifacts are shared project outputs (the existing pool uses
        # 0664).  Avoid reading umask via os.umask(), which is process-global
        # and creates a cross-thread permission race.
        publish_mode = 0o664
    os.chmod(temp_path, publish_mode)
    temp_path.replace(out_path)
    return True, "verified", verification_output, axioms


def _summary_proof_graph_record(summary: Dict[str, Any]) -> Dict[str, Any]:
    dossier = summary.get("proof_dossier")
    if isinstance(dossier, dict):
        graph = dossier.get("proof_graph")
        if isinstance(graph, dict):
            return graph
    graph = summary.get("proof_graph")
    if isinstance(graph, dict):
        return graph
    return {}


def _write_export_navigation_artifacts(
    out_path: Path,
    *,
    summary: Optional[Dict[str, Any]] = None,
    export_axioms: Tuple[str, ...] = (),
    export_verified: bool = False,
) -> Dict[str, str]:
    """Write graph/source-map artifacts for an installed solved Lean file.

    These artifacts are observability only. They are intentionally generated
    after the verified install path has placed the final Lean bytes on disk.
    """

    try:
        from .export_dependency_graph import export_file
    except Exception as exc:
        _remove_export_navigation_artifacts(
            Path(out_path).parent,
            Path(out_path).stem,
        )
        return {"dependency_graph_error": f"{type(exc).__name__}: {exc}"}

    depgraph_dir = Path(out_path).parent / "depgraphs"
    stem = Path(out_path).stem
    parent = Path(out_path).parent
    try:
        payload = export_file(
            Path(out_path),
            depgraph_dir,
            axioms=list(export_axioms),
            audit_ok=True if export_verified else None,
            proof_graph_record=_summary_proof_graph_record(summary or {}),
        )
        if payload is None:
            _remove_export_navigation_artifacts(
                Path(out_path).parent,
                Path(out_path).stem,
            )
            return {"dependency_graph_error": "no declarations found"}
        dep_source_map = depgraph_dir / f"{stem}.source_map.json"
        side_source_map = parent / f"{stem}.source_map.json"
        if dep_source_map.exists():
            try:
                sidecar = json.loads(dep_source_map.read_text(encoding="utf-8"))
                source_html_rel = str(Path("depgraphs") / f"{stem}.source.html")
                sidecar["source_html_path"] = source_html_rel
                for decl in list(sidecar.get("declarations") or []):
                    if not isinstance(decl, dict):
                        continue
                    line = max(1, int(decl.get("line_start") or 1))
                    proof_line = max(1, int(decl.get("proof_start_line") or line))
                    decl["href"] = f"{source_html_rel}#L{line}"
                    decl["proof_href"] = f"{source_html_rel}#L{proof_line}"
                _write_text_atomic(
                    side_source_map,
                    json.dumps(sidecar, indent=2, ensure_ascii=False),
                )
            except Exception:
                _write_text_atomic(
                    side_source_map,
                    dep_source_map.read_text(encoding="utf-8"),
                )
    except Exception as exc:
        _remove_export_navigation_artifacts(
            Path(out_path).parent,
            Path(out_path).stem,
        )
        return {"dependency_graph_error": f"{type(exc).__name__}: {exc}"}
    return {
        "dependency_graph_path": _display_path(depgraph_dir / f"{stem}.html"),
        "dependency_graph_json_path": _display_path(depgraph_dir / f"{stem}.json"),
        "source_map_path": _display_path(side_source_map),
        "source_html_path": _display_path(depgraph_dir / f"{stem}.source.html"),
        "navigation_artifacts_error": "",
    }


def export_solved_files(
    *,
    answer_visibility: str = "opaque",
    problem_name: Optional[str] = None,
    solved_dir: Optional[Path] = None,
    write_manifest: bool = True,
    verify_lean: bool = True,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
) -> ExportResult:
    """Serialize batch publication with concurrent live exporters."""

    target_dir = Path(solved_dir) if solved_dir is not None else SOLVED_DIR
    target_dir.mkdir(parents=True, exist_ok=True)
    lock_path = target_dir / ".export-publication.lock"
    with lock_path.open("a+") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            return _export_solved_files_locked(
                answer_visibility=answer_visibility,
                problem_name=problem_name,
                solved_dir=target_dir,
                write_manifest=write_manifest,
                verify_lean=verify_lean,
                lean_project_dir=lean_project_dir,
                lean_timeout_s=lean_timeout_s,
            )
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def _export_solved_files_locked(
    *,
    answer_visibility: str = "opaque",
    problem_name: Optional[str] = None,
    solved_dir: Optional[Path] = None,
    write_manifest: bool = True,
    verify_lean: bool = True,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
) -> ExportResult:
    """Export solved run artifacts as standalone Lean files.

    The default remains the no-answer/opaque export pool. Passing
    ``answer_visibility="visible"`` exports with-answer control runs and writes
    a visible-mode header into each Lean file.
    """

    solved_dir = Path(solved_dir) if solved_dir is not None else SOLVED_DIR
    solved_dir.mkdir(parents=True, exist_ok=True)
    visibility = _normalize_answer_visibility(answer_visibility)
    runs_by_name = _find_solved_runs(answer_visibility=visibility)
    if problem_name:
        if not is_valid_lean_qualified_name(problem_name):
            return ExportResult(
                records=[], skipped=[(problem_name, "unsafe problem name")]
            )
        runs_by_name = (
            {problem_name: runs_by_name.get(problem_name, [])}
            if runs_by_name.get(problem_name)
            else {}
        )

    manifest: List[SolvedRecord] = []
    skipped: List[Tuple[str, str]] = []

    def remove_stale_output(stem: str) -> None:
        stale_out = solved_dir / f"{stem}.lean"
        try:
            stale_out.unlink()
        except FileNotFoundError:
            pass
        except Exception:
            pass
        _remove_export_navigation_artifacts(
            solved_dir,
            stem,
        )

    def remove_stale_output_family(identity_stem: str) -> None:
        base = _output_stem_for_solve(
            identity_stem,
            answer_visibility=visibility,
            solve_index=1,
            solve_count=1,
        )
        version_re = re.compile(rf"^{re.escape(base)}_v[1-9][0-9]*$")
        stems = {base}
        for path in solved_dir.glob(f"{base}_v*.lean"):
            if version_re.fullmatch(path.stem):
                stems.add(path.stem)
        for stem in stems:
            remove_stale_output(stem)

    def remove_surplus_version_outputs(name: str, solve_count: int) -> None:
        base = _output_stem_for_solve(
            name,
            answer_visibility=visibility,
            solve_index=1,
            solve_count=1,
        )
        version_re = re.compile(rf"^{re.escape(base)}_v([1-9][0-9]*)$")

        def artifact_stem(path: Path) -> str:
            name = path.name
            for suffix in (".source_map.json", ".source.html"):
                if name.endswith(suffix):
                    return name[: -len(suffix)]
            return path.stem

        candidate_stems = {
            artifact_stem(path)
            for root in (solved_dir, solved_dir / "depgraphs")
            for path in root.glob(f"{base}_v*")
        }
        for stem in sorted(candidate_stems):
            match = version_re.fullmatch(stem)
            if match is None:
                continue
            if solve_count > 1 and int(match.group(1)) <= solve_count:
                continue
            path = solved_dir / f"{stem}.lean"
            try:
                path.unlink()
            except FileNotFoundError:
                pass
            except Exception:
                pass
            _remove_export_navigation_artifacts(
                solved_dir,
                stem,
            )

    identity_groups: Dict[Tuple[str, str], List[Path]] = {}
    for name in sorted(runs_by_name):
        for run_dir in runs_by_name[name]:
            summary_path = run_dir / "summary.json"
            try:
                candidate_summary = json.loads(summary_path.read_text(encoding="utf-8"))
            except Exception:
                candidate_summary = {}
            candidate_identity = _single_run_export_identity(candidate_summary)
            if candidate_identity is None:
                recorded_identity = _recorded_export_identity_for_cleanup(
                    candidate_summary
                )
                if recorded_identity is not None:
                    remove_stale_output_family(recorded_identity[1])
                skipped.append(
                    (
                        f"{name} ({run_dir.name})",
                        "missing or invalid theorem-project artifact identity",
                    )
                )
                continue
            identity_groups.setdefault(
                (candidate_identity[0], candidate_identity[1]), []
            ).append(run_dir)

    for name, output_key in sorted(identity_groups):
        run_dirs = identity_groups[(name, output_key)]
        solve_count = len(run_dirs)
        single_stem = _output_stem_for_solve(
            output_key,
            answer_visibility=visibility,
            solve_index=1,
            solve_count=1,
        )
        if solve_count > 1:
            stale_single = solved_dir / f"{single_stem}.lean"
            if stale_single.exists():
                stale_single.unlink()
            _remove_export_navigation_artifacts(
                solved_dir,
                single_stem,
            )
        for solve_index, run_dir in enumerate(run_dirs, 1):
            output_stem = _output_stem_for_solve(
                output_key,
                answer_visibility=visibility,
                solve_index=solve_index,
                solve_count=solve_count,
            )
            skip_label = f"{output_stem} ({run_dir.name})"
            out_path = solved_dir / f"{output_stem}.lean"

            s_path = run_dir / "summary.json"
            s = (
                json.loads(s_path.read_text(encoding="utf-8"))
                if s_path.exists()
                else {}
            )
            rec = _get_solved_turn(run_dir)
            proof, helpers = _root_replay_for_export(s, rec)
            if not proof:
                skipped.append((skip_label, "empty root proof"))
                remove_stale_output(output_stem)
                continue

            identity = _single_run_export_identity(s)
            if identity is None or identity[1] != output_key:
                skipped.append((skip_label, "theorem-project artifact identity drift"))
                remove_stale_output(output_stem)
                continue
            snapshot = identity[2] if identity is not None else None
            adapter_id = str(
                (snapshot or {}).get("adapter_id") or PUTNAMBENCH_ADAPTER_ID
            )
            content = (
                _build_theorem_project_solved_file(snapshot, proof, helpers)
                if snapshot is not None
                else _build_solved_file(
                    name,
                    proof,
                    helpers,
                    answer_visibility=_summary_answer_visibility(s),
                    **_summary_visibility_flags(s),
                )
            )
            if content is None:
                skipped.append((skip_label, "could not reconstruct file"))
                remove_stale_output(output_stem)
                continue

            project_record = s.get("theorem_project")
            project_record = project_record if isinstance(project_record, dict) else {}
            effective_project = lean_project_dir
            if effective_project is None and project_record.get("project_path"):
                effective_project = Path(str(project_record["project_path"]))
            module_paths = tuple(
                Path(str(path))
                for source_record in list(project_record.get("source_dirs") or ())
                if isinstance(source_record, dict)
                for path in list(source_record.get("compiled_module_roots") or ())
                if str(path or "").strip()
            )
            export_verified, verification_status, verification_output, export_axioms = (
                _install_exported_lean(
                    out_path,
                    content,
                    verify_lean=verify_lean,
                    lean_project_dir=effective_project,
                    lean_timeout_s=lean_timeout_s,
                    theorem_name=name,
                    extra_lean_paths=module_paths,
                    project_imports=tuple(project_record.get("project_imports") or ()),
                    support_project_builds=dict(
                        project_record.get("support_project_builds") or {}
                    ),
                )
            )
            if verify_lean and not export_verified:
                skipped.append(
                    (
                        skip_label,
                        f"Lean verification rejected export ({verification_status})",
                    )
                )
                remove_stale_output(output_stem)
                continue
            navigation_artifacts = (
                _write_export_navigation_artifacts(
                    out_path,
                    summary=s,
                    export_axioms=export_axioms,
                    export_verified=export_verified,
                )
                if adapter_id == PUTNAMBENCH_ADAPTER_ID
                else {}
            )

            ts = run_dir.stat().st_mtime
            record = SolvedRecord(
                theorem_name=name,
                output_stem=output_stem,
                solve_index=solve_index,
                solve_count=solve_count,
                output_path=_display_path(out_path),
                source_path=(
                    str((snapshot or {}).get("source_path") or "").strip()
                    or _display_path(PUTNAM_SRC / f"{name}.lean")
                ),
                lean_project_path=str(effective_project or ""),
                module_search_paths=tuple(str(path) for path in module_paths),
                project_imports=tuple(project_record.get("project_imports") or ()),
                support_project_builds={
                    str(project): list(targets)
                    for project, targets in dict(
                        project_record.get("support_project_builds") or {}
                    ).items()
                },
                run_dir=_display_path(run_dir),
                solved_at_ts=ts,
                solved_at_iso=time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(ts)),
                turns=int(s.get("total_turns", 0) or 0),
                wall_s=float(s.get("wall_clock_s", 0.0) or 0.0),
                helper_count=len(helpers),
                has_refiner=bool(s.get("refiner")),
                proof_chars=len(proof),
                answer_visibility=_summary_answer_visibility(s),
                **_summary_visibility_flags(s),
                export_verified=export_verified,
                export_verification_status=verification_status,
                export_verification_output=verification_output[:4000],
                export_axioms=export_axioms,
                source_map_path=navigation_artifacts.get("source_map_path", ""),
                dependency_graph_path=navigation_artifacts.get(
                    "dependency_graph_path", ""
                ),
                dependency_graph_json_path=navigation_artifacts.get(
                    "dependency_graph_json_path", ""
                ),
                source_html_path=navigation_artifacts.get("source_html_path", ""),
                navigation_artifacts_error=navigation_artifacts.get(
                    "dependency_graph_error", ""
                )
                or navigation_artifacts.get("navigation_artifacts_error", ""),
            )
            manifest.append(record)
            version_note = f" [{solve_index}/{solve_count}]" if solve_count > 1 else ""
            print(
                f"  ✓ {name}{version_note}  -> {out_path.name}  "
                f"({len(helpers)} helpers, {len(proof)} proof chars)"
            )
        remove_surplus_version_outputs(output_key, solve_count)

    if write_manifest:
        manifest_path = solved_dir / "manifest.json"
        _write_solved_manifest(manifest_path, [asdict(record) for record in manifest])
    return ExportResult(records=manifest, skipped=skipped)


def export_solved_run(
    run_dir: Path,
    *,
    solved_dir: Optional[Path] = None,
    verify_lean: bool = False,
    allow_pre_export_bootstrap: bool = False,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
) -> Optional[SolvedRecord]:
    """Serialize allocation/install/manifest publication for one theorem."""

    run_path = Path(run_dir)
    try:
        summary = json.loads((run_path / "summary.json").read_text(encoding="utf-8"))
    except Exception:
        return None
    if _single_run_export_identity(summary) is None:
        return None
    target_dir = Path(solved_dir) if solved_dir is not None else SOLVED_DIR
    target_dir.mkdir(parents=True, exist_ok=True)
    # One directory-wide lock coordinates the shared manifest as well as
    # filenames.  Per-theorem locks lose records when different theorem
    # exporters concurrently read/modify/write the same manifest.
    lock_path = target_dir / ".export-publication.lock"
    with lock_path.open("a+") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            return _export_solved_run_locked(
                run_path,
                solved_dir=target_dir,
                verify_lean=verify_lean,
                allow_pre_export_bootstrap=allow_pre_export_bootstrap,
                lean_project_dir=lean_project_dir,
                lean_timeout_s=lean_timeout_s,
            )
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def _export_solved_run_locked(
    run_dir: Path,
    *,
    solved_dir: Optional[Path] = None,
    verify_lean: bool = False,
    allow_pre_export_bootstrap: bool = False,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
) -> Optional[SolvedRecord]:
    """Export only one completed mini-prover run.

    This is the live auto-export path used at the end of a successful
    mini-prover invocation. It intentionally does not call
    ``export_solved_files`` because that batch path rewrites every solved run
    for the theorem and can rename a historical singleton export to ``_v1``.
    """

    run_dir = Path(run_dir)
    s_path = run_dir / "summary.json"
    if not s_path.exists():
        return None
    try:
        summary = json.loads(s_path.read_text(encoding="utf-8"))
    except Exception:
        return None
    if not summary.get("problem"):
        return None
    if not _summary_solved_for_export(summary):
        boundary_present, export_status = _summary_export_boundary_status(summary)
        pre_export_bootstrap = bool(
            allow_pre_export_bootstrap
            and verify_lean
            and (
                _summary_bool_true(summary, "pre_export_solved")
                or _summary_bool_true(summary, "session_root_finalized")
            )
            and (
                export_status in _LIVE_PRE_EXPORT_BOOTSTRAP_STATUSES
                or (not boundary_present and not export_status)
            )
        )
        if not pre_export_bootstrap:
            return None

    run_key = _display_path(run_dir)
    rec = _get_solved_turn(run_dir)
    proof, helpers = _root_replay_for_export(summary, rec)
    if not proof:
        return None
    export_identity = _single_run_export_identity(summary)
    if export_identity is None:
        return None
    problem_name, output_key, project_snapshot = export_identity
    adapter_id = str(
        (project_snapshot or {}).get("adapter_id")
        or summary.get("theorem_project_adapter")
        or PUTNAMBENCH_ADAPTER_ID
    ).strip()
    visibility = _summary_answer_visibility(summary)
    visibility_flags = _summary_visibility_flags(summary)
    theory_snapshot_raw = summary.get("mini_theory_snapshot")
    theory_snapshot = (
        [dict(item) for item in theory_snapshot_raw if isinstance(item, dict)]
        if isinstance(theory_snapshot_raw, list)
        else []
    )
    theory_modules = tuple(
        dict.fromkeys(
            str(item.get("module_name") or "").strip()
            for item in theory_snapshot
            if str(item.get("module_name") or "").strip()
        )
    )
    theory_lean_paths: tuple[Path, ...] = ()
    theory_sources: list[str] = []
    theory_source_imports: list[str] = []
    if theory_modules:
        theory_root = Path(str(summary.get("mini_theory_root") or "")).expanduser()
        modules_root = theory_root / "modules"
        if not theory_root.is_absolute() or not modules_root.is_dir():
            return None
        # Every imported module must still have the exact content-addressed
        # artifact recorded by the run. Missing provenance fails export closed.
        snapshot_by_module = {
            str(item.get("module_name") or ""): item for item in theory_snapshot
        }
        for module in theory_modules:
            record = snapshot_by_module[module]
            snapshot_bundle_id = _mini_theory_snapshot_bundle_id(module, record)
            if snapshot_bundle_id is None:
                return None
            resolved_modules_root = modules_root.resolve()
            artifact = modules_root.joinpath(*module.split(".")).with_suffix(".olean")
            source_path = modules_root.joinpath(*module.split(".")).with_suffix(".lean")
            manifest_path = source_path.parent / "manifest.json"
            try:
                artifact.resolve().relative_to(resolved_modules_root)
                source_path.resolve().relative_to(resolved_modules_root)
                manifest_path.resolve().relative_to(resolved_modules_root)
            except (OSError, ValueError):
                return None
            if not artifact.is_file():
                return None
            if not source_path.is_file():
                return None
            if not manifest_path.is_file():
                return None
            try:
                bundle = PublishedTheoryBundle.from_dict(
                    json.loads(manifest_path.read_text(encoding="utf-8"))
                )
            except (OSError, ValueError, TypeError):
                return None
            if (
                bundle.bundle_id != snapshot_bundle_id
                or bundle.module_name != module
                or not bundle.manifest_hash
                or bundle.manifest_hash != bundle.computed_manifest_hash()
            ):
                return None
            expected_hash = str(record.get("compiled_artifact_hash") or "").strip()
            if (
                not expected_hash
                or bundle.compiled_artifact_hash != expected_hash
                or hashlib.sha256(artifact.read_bytes()).hexdigest() != expected_hash
            ):
                return None
            source_text = source_path.read_text(encoding="utf-8").strip()
            expected_source_hash = str(record.get("source_hash") or "").strip()
            if (
                not expected_source_hash
                or bundle.source_hash != expected_source_hash
                or hashlib.sha256(source_text.encode("utf-8")).hexdigest()
                != expected_source_hash
            ):
                return None
            body_lines: list[str] = []
            for line in source_text.splitlines():
                import_match = re.match(r"^\s*import\s+([^\s]+)\s*$", line)
                if import_match is None:
                    body_lines.append(line)
                    continue
                imported_module = import_match.group(1)
                if not imported_module.startswith("MiniTheory."):
                    theory_source_imports.append(imported_module)
            theory_sources.append("\n".join(body_lines).strip())
        theory_lean_paths = (modules_root,)
    if project_snapshot is not None:
        content = _build_theorem_project_solved_file(
            project_snapshot,
            proof,
            helpers,
            extra_imports=tuple(dict.fromkeys(theory_source_imports)),
            extra_theory_sources=tuple(theory_sources),
        )
    else:
        content = _build_solved_file(
            problem_name,
            proof,
            helpers,
            answer_visibility=visibility,
            **visibility_flags,
            extra_imports=tuple(dict.fromkeys(theory_source_imports)),
            extra_theory_sources=tuple(theory_sources),
        )
    if content is None:
        return None

    target_dir = Path(solved_dir) if solved_dir is not None else SOLVED_DIR
    target_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = target_dir / "manifest.json"
    try:
        raw_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception:
        raw_manifest = []
    prior_manifest = [
        dict(item) for item in list(raw_manifest or []) if isinstance(item, dict)
    ]
    base_stem = _output_stem_for_solve(
        output_key,
        answer_visibility=visibility,
        solve_index=1,
        solve_count=1,
    )
    version_re = re.compile(rf"^{re.escape(base_stem)}_v([1-9][0-9]*)$")
    prior_run_records = []
    for item in prior_manifest:
        item_stem = str(item.get("output_stem") or "").strip()
        if item_stem != base_stem and version_re.fullmatch(item_stem) is None:
            continue
        if (
            str(item.get("run_dir") or "") == run_key
            and str(item.get("theorem_name") or "") == problem_name
            and _normalize_answer_visibility(
                str(item.get("answer_visibility") or "opaque")
            )
            == visibility
        ):
            prior_run_records.append(item)
    if prior_run_records:
        # Retrying supervisor publication for the same run must re-verify and
        # replace that run's existing export, not manufacture a second solve.
        prior_run_records.sort(
            key=lambda item: (
                int(item.get("solve_index", 1) or 1),
                str(item.get("output_stem") or ""),
            )
        )
        canonical = prior_run_records[0]
        output_stem = str(canonical["output_stem"])
        solve_index = int(canonical.get("solve_index", 1) or 1)
        solve_count = int(canonical.get("solve_count", solve_index) or solve_index)
    else:
        output_stem, solve_index, solve_count = _next_single_run_output(
            target_dir,
            output_key,
            answer_visibility=visibility,
        )
    stale_retry_stems = {
        str(item.get("output_stem") or "")
        for item in prior_run_records
        if str(item.get("output_stem") or "") != output_stem
    }
    out_path = target_dir / f"{output_stem}.lean"
    theorem_project_record = summary.get("theorem_project")
    theorem_project_record = (
        theorem_project_record if isinstance(theorem_project_record, dict) else {}
    )
    effective_lean_project_dir = lean_project_dir
    if effective_lean_project_dir is None:
        recorded_project = str(theorem_project_record.get("project_path") or "").strip()
        if recorded_project:
            effective_lean_project_dir = Path(recorded_project)
    project_module_paths: list[Path] = []
    raw_source_dirs = theorem_project_record.get("source_dirs")
    if isinstance(raw_source_dirs, list):
        for source_record in raw_source_dirs:
            if not isinstance(source_record, dict):
                continue
            for path in source_record.get("compiled_module_roots") or ():
                value = str(path or "").strip()
                if value:
                    project_module_paths.append(Path(value))
    all_lean_paths = tuple(dict.fromkeys((*theory_lean_paths, *project_module_paths)))
    export_verified, verification_status, verification_output, export_axioms = (
        _install_exported_lean(
            out_path,
            content,
            verify_lean=verify_lean,
            lean_project_dir=effective_lean_project_dir,
            lean_timeout_s=lean_timeout_s,
            theorem_name=problem_name,
            extra_lean_paths=all_lean_paths,
            project_imports=tuple(theorem_project_record.get("project_imports") or ()),
            support_project_builds=dict(
                theorem_project_record.get("support_project_builds") or {}
            ),
        )
    )
    if verify_lean and not export_verified:
        raise SolvedExportVerificationError(
            verification_output,
            status=verification_status or "lean_rejected",
        )
    # A versioned retry and its canonical stem share the local depgraph index.
    # Remove stale retry artifacts only after the canonical Lean file verifies,
    # but before regenerating canonical navigation so shared files are recreated
    # rather than deleted afterward.
    for stale_stem in stale_retry_stems:
        if stale_stem != base_stem and version_re.fullmatch(stale_stem) is None:
            continue
        try:
            (target_dir / f"{stale_stem}.lean").unlink()
        except FileNotFoundError:
            pass
        _remove_export_navigation_artifacts(
            target_dir,
            stale_stem,
            remove_shared_index=False,
        )
    navigation_artifacts = (
        _write_export_navigation_artifacts(
            out_path,
            summary=summary,
            export_axioms=export_axioms,
            export_verified=export_verified,
        )
        if adapter_id == PUTNAMBENCH_ADAPTER_ID
        else {}
    )
    ts = run_dir.stat().st_mtime
    record = SolvedRecord(
        theorem_name=problem_name,
        output_stem=out_path.stem,
        solve_index=solve_index,
        solve_count=solve_count,
        output_path=_display_path(out_path),
        source_path=(
            str((project_snapshot or {}).get("source_path") or "").strip()
            or _display_path(PUTNAM_SRC / f"{problem_name}.lean")
        ),
        run_dir=run_key,
        solved_at_ts=ts,
        solved_at_iso=time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(ts)),
        turns=int(summary.get("total_turns", 0) or 0),
        wall_s=float(summary.get("wall_clock_s", 0.0) or 0.0),
        helper_count=len(helpers),
        has_refiner=bool(summary.get("refiner")),
        proof_chars=len(proof),
        answer_visibility=visibility,
        **visibility_flags,
        export_verified=export_verified,
        export_verification_status=verification_status,
        export_verification_output=verification_output[:4000],
        export_axioms=export_axioms,
        source_map_path=navigation_artifacts.get("source_map_path", ""),
        dependency_graph_path=navigation_artifacts.get("dependency_graph_path", ""),
        dependency_graph_json_path=navigation_artifacts.get(
            "dependency_graph_json_path", ""
        ),
        source_html_path=navigation_artifacts.get("source_html_path", ""),
        navigation_artifacts_error=navigation_artifacts.get(
            "dependency_graph_error", ""
        )
        or navigation_artifacts.get("navigation_artifacts_error", ""),
        lean_project_path=str(effective_lean_project_dir or ""),
        module_search_paths=tuple(str(path) for path in all_lean_paths),
        project_imports=tuple(theorem_project_record.get("project_imports") or ()),
        support_project_builds={
            str(project): list(targets)
            for project, targets in dict(
                theorem_project_record.get("support_project_builds") or {}
            ).items()
        },
    )
    manifest: List[Dict[str, Any]] = []
    for item in prior_manifest:
        if not str(item.get("output_stem") or "").strip():
            continue
        same_run = (
            str(item.get("run_dir") or "") == run_key
            and str(item.get("theorem_name") or "") == problem_name
            and _normalize_answer_visibility(
                str(item.get("answer_visibility") or "opaque")
            )
            == visibility
        )
        if same_run:
            continue
        if str(item.get("output_stem") or "") == record.output_stem:
            continue
        manifest.append(item)
    manifest.append(asdict(record))
    _write_solved_manifest(manifest_path, manifest)
    return record


def audit_existing_exports(
    *,
    solved_dir: Optional[Path] = None,
    lean_project_dir: Optional[Path] = None,
    lean_timeout_s: float = 180.0,
    problem_name: Optional[str] = None,
) -> List[Dict[str, Any]]:
    """Run the axiom audit over already-exported solved ``.lean`` files.

    Writes ``axiom_audit.json`` next to the exports and returns the report
    rows. Does not modify or re-verify the exports themselves.
    """

    target_dir = Path(solved_dir) if solved_dir is not None else SOLVED_DIR
    rows: List[Dict[str, Any]] = []
    manifest_by_stem: Dict[str, Dict[str, Any]] = {}
    try:
        manifest_payload = json.loads(
            (target_dir / "manifest.json").read_text(encoding="utf-8")
        )
    except Exception:
        manifest_payload = []
    for item in list(manifest_payload or ()):
        if isinstance(item, dict) and str(item.get("output_stem") or "").strip():
            manifest_by_stem[str(item["output_stem"])] = item
    lean_files = sorted(target_dir.glob("*.lean"))
    for lean_path in lean_files:
        if lean_path.name.startswith("."):
            continue
        content = lean_path.read_text(encoding="utf-8")
        manifest_record = manifest_by_stem.get(lean_path.stem, {})
        theorem_name = str(manifest_record.get("theorem_name") or "").strip()
        if not theorem_name:
            # Legacy exports predate manifest-backed logical identities.
            theorem_name = _export_root_name_for_content(lean_path.stem, content)
        if problem_name and not theorem_name.startswith(problem_name):
            continue
        try:
            select_lean_theorem(scan_lean_theorems(content), theorem_name)
        except ValueError:
            rows.append(
                {
                    "file": lean_path.name,
                    "theorem": theorem_name,
                    "ok": False,
                    "axioms": [],
                    "unexpected_axioms": [],
                    "source_hash": hashlib.sha256(content.encode("utf-8")).hexdigest()[
                        :16
                    ],
                    "error": (
                        f"root theorem '{theorem_name}' (manifest or legacy identity) "
                        "not declared in file"
                    ),
                }
            )
            continue
        effective_project = lean_project_dir
        if effective_project is None and manifest_record.get("lean_project_path"):
            effective_project = Path(str(manifest_record["lean_project_path"]))
        module_paths = tuple(
            Path(str(path))
            for path in list(manifest_record.get("module_search_paths") or ())
            if str(path or "").strip()
        )
        project_imports = tuple(
            str(module or "").strip()
            for module in list(manifest_record.get("project_imports") or ())
            if str(module or "").strip()
        )
        build_ok, build_output = _build_export_project_imports(
            project_imports,
            lean_project_dir=effective_project,
            timeout_s=lean_timeout_s,
        )
        if not build_ok:
            rows.append(
                {
                    "file": lean_path.name,
                    "theorem": theorem_name,
                    "ok": False,
                    "axioms": [],
                    "unexpected_axioms": [],
                    "source_hash": hashlib.sha256(content.encode("utf-8")).hexdigest()[
                        :16
                    ],
                    "error": f"project import build failed: {build_output}"[-1500:],
                }
            )
            continue
        support_ok, support_output = _build_export_support_projects(
            dict(manifest_record.get("support_project_builds") or {}),
            timeout_s=lean_timeout_s,
        )
        if not support_ok:
            rows.append(
                {
                    "file": lean_path.name,
                    "theorem": theorem_name,
                    "ok": False,
                    "axioms": [],
                    "unexpected_axioms": [],
                    "source_hash": hashlib.sha256(content.encode("utf-8")).hexdigest()[
                        :16
                    ],
                    "error": f"support project build failed: {support_output}"[-1500:],
                }
            )
            continue
        ok, axioms, unexpected, output = _audit_exported_axioms(
            content,
            theorem_name,
            scratch_dir=target_dir,
            lean_project_dir=effective_project,
            timeout_s=lean_timeout_s,
            extra_lean_paths=module_paths,
        )
        rows.append(
            {
                "file": lean_path.name,
                "theorem": theorem_name,
                "ok": bool(ok),
                "axioms": list(axioms),
                "unexpected_axioms": list(unexpected),
                "source_hash": hashlib.sha256(content.encode("utf-8")).hexdigest()[:16],
                "error": "" if ok else output[-1500:],
            }
        )
        verdict = "OK" if ok else f"FAIL unexpected={unexpected or 'no-report'}"
        print(f"  {verdict:<40} {lean_path.name}  axioms={axioms}")
    report_path = target_dir / "axiom_audit.json"
    report_path.write_text(
        json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    print(f"\nAxiom audit report: {report_path}")
    failures = [row for row in rows if not row["ok"]]
    print(f"{len(rows) - len(failures)}/{len(rows)} exports pass the axiom audit")
    return rows


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Export finalized theorem-prover runs as standalone Lean files."
    )
    parser.add_argument(
        "--answer-visibility",
        choices=["opaque", "visible"],
        default="opaque",
        help="Which solved-run answer-visibility pool to export.",
    )
    parser.add_argument(
        "--opaque-mode",
        dest="answer_visibility",
        action="store_const",
        const="opaque",
        help="Export opaque/no-answer solves (default).",
    )
    parser.add_argument(
        "--visible-answer-mode",
        "--no-opaque-mode",
        dest="answer_visibility",
        action="store_const",
        const="visible",
        help="Export visible-answer control solves.",
    )
    parser.add_argument(
        "--skip-lean-verify",
        action="store_true",
        help="Write reconstructed solved files without running lake env lean.",
    )
    parser.add_argument(
        "--lean-project-dir",
        default=None,
        help=(
            "Override the Lean project used for export verification. By default "
            "each theorem-project manifest supplies its own project and legacy "
            "Putnam exports use PutnamBench."
        ),
    )
    parser.add_argument(
        "--lean-timeout-s",
        type=float,
        default=180.0,
        help="Per-file Lean verification timeout in seconds.",
    )
    parser.add_argument(
        "--audit-existing",
        action="store_true",
        help=(
            "Run the #print axioms audit over already-exported solved .lean "
            "files (no re-export); writes axiom_audit.json next to them."
        ),
    )
    parser.add_argument(
        "--problem",
        default=None,
        help="Restrict --audit-existing to files whose root theorem starts with this name.",
    )
    args = parser.parse_args(list(argv or []))

    if bool(args.audit_existing):
        rows = audit_existing_exports(
            lean_project_dir=(
                Path(args.lean_project_dir) if args.lean_project_dir else None
            ),
            lean_timeout_s=float(args.lean_timeout_s),
            problem_name=args.problem,
        )
        return 0 if all(row["ok"] for row in rows) else 1

    result = export_solved_files(
        answer_visibility=str(args.answer_visibility),
        write_manifest=True,
        verify_lean=not bool(args.skip_lean_verify),
        lean_project_dir=(
            Path(args.lean_project_dir) if args.lean_project_dir else None
        ),
        lean_timeout_s=float(args.lean_timeout_s),
    )
    if not result.records:
        print("No solved runs found.")
        return 0

    print()
    print(f"Wrote {len(result.records)} files to {SOLVED_DIR}")
    print(f"Manifest: {SOLVED_DIR / 'manifest.json'}")
    if result.skipped:
        print()
        print(f"Skipped {len(result.skipped)}:")
        for n, reason in result.skipped:
            print(f"  - {n}: {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
