"""Committed proof receipts used by problem-level sweep milestone deadlines."""

from __future__ import annotations

import hashlib
import json
import re
import time
from typing import Any

from .proof_dossier import canonical_dossier_statement_key, helper_decl_statement, text_hash


# The graph key shields literals/quoted identifiers in NUL-delimited atoms.
# Keep those atoms, qualified names, and complete symbolic tokens intact while
# ignoring layout between tokens. Removing all spaces would merge `f x`/`fx`
# or the distinct operators `+ +`/`++`.
_STATEMENT_TOKEN_PATTERN = re.compile(
    r"\x00[^\x00]*\x00|"
    r"[^\W\d][\w'✝!?]*(?:\.[^\W\d][\w'✝!?]*)*|"
    r"\d+(?:\.\d+)?|"
    r"[()[\]{},;]|"
    r"[^\w\s()[\]{},;\x00]+"
)


def accepted_statement_identity(statement: str) -> str:
    """Ignore declaration names and proof scripts when counting a proposition."""

    key = canonical_dossier_statement_key(statement)
    tokens = _STATEMENT_TOKEN_PATTERN.findall(key)
    encoded = json.dumps(tokens, ensure_ascii=True, separators=(",", ":"))
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest() if tokens else ""


def committed_acceptance_records(
    session: Any,
    outcome: Any,
    *,
    prior_formal_evidence: tuple[str, ...] | None = None,
) -> list[dict[str, Any]]:
    """Read effective proof authority only after the enclosing apply commits.

    Helper additions must still exist in the accepted dossier. Cache and import
    actions restore previously known results and do not earn sweep milestones.
    The sweep merges proposition identities across samples and recursive scopes.
    """

    dossier = session.dossier
    if dossier is None:
        return []
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    records: dict[str, dict[str, Any]] = {}
    committed_at = time.monotonic()

    def add(statement: str, kind: str, helper_name: str = "") -> None:
        identity = accepted_statement_identity(statement)
        if identity:
            records[identity] = {
                "phase": "session_accepted_proof",
                "verdict": "accepted_proof_committed",
                "acceptance_identity": identity,
                "acceptance_monotonic_s": committed_at,
                "acceptance_kind": kind,
                "helper_name": helper_name,
                "action_id": outcome.action_id,
                "action_dispatch_id": str(
                    (outcome.metadata or {}).get("action_dispatch_id") or ""
                ),
            }

    helper_names = dict.fromkeys(outcome.helpers_added)
    if prior_formal_evidence is not None:
        prior = set(prior_formal_evidence)
        # An auxiliary proof can survive rejection of its dispatch's target,
        # even when that outcome deliberately reports no target progress.
        for name, helper in helpers.items():
            if f"helper:{name}:{helper.source_hash}" not in prior:
                helper_names[name] = None
    for name in helper_names:
        helper = helpers.get(name)
        if helper is None:
            continue
        phase = str(getattr(helper, "phase", "") or "").lower()
        if any(token in phase for token in ("cache", "seed", "import", "restore")):
            continue
        source = str(getattr(helper, "source", "") or "")
        if not source or getattr(helper, "source_hash", "") != text_hash(source):
            continue
        add(helper_decl_statement(source), "helper", str(name))

    metadata = outcome.metadata or {}
    certificate = getattr(dossier, "root_proof_certificate", None)
    if (
        outcome.solved
        and metadata.get("root_finalization_accepted") is True
        and isinstance(certificate, dict)
        and not metadata.get("hydrated_from_existing_root_finalization")
    ):
        add(str(certificate.get("root_statement") or dossier.root_statement), "root")
    return list(records.values())
