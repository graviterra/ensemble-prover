"""Committed proof receipts used by problem-level sweep milestone deadlines."""

from __future__ import annotations

import hashlib
import json
import re
import time
from typing import Any

from .proof_dossier import canonical_dossier_statement_key, helper_decl_statement, text_hash

_RESTORED_HELPER_PHASE_TOKENS = ("cache", "seed", "import", "restore")
_SCOPED_PROPOSITION_SYNTAX = re.compile(
    r"[,;∀∃λ↦∑∏⨆⨅$→↔]|=>|->|<\||\|>|"
    r"\b(?:forall|exists|fun|let|match|if|then|else|do|by|show|have|suffices|from)\b"
)


def helper_phase_is_restored(phase: str) -> bool:
    lowered = str(phase or "").lower()
    return any(token in lowered for token in _RESTORED_HELPER_PHASE_TOKENS)


def helper_restates_restored_knowledge(helper: Any, helpers: Any) -> bool:
    """True when a helper only restates cache/import/restore knowledge.

    Exact proposition copies of a restored helper do not earn a sweep identity.
    Cached dependencies alone do not establish restatement: a proof may also
    use Mathlib or new reasoning. Suppress connective wrappers only when the
    target directly wraps existing facts under identical binders.
    """

    if helper_phase_is_restored(str(getattr(helper, "phase", "") or "")):
        return True
    helper_map = helpers if isinstance(helpers, dict) else {}
    source = str(getattr(helper, "source", "") or "")
    identity = (
        accepted_statement_identity(helper_decl_statement(source)) if source else ""
    )
    helper_name = str(getattr(helper, "name", "") or "")
    if identity:
        for other in helper_map.values():
            if other is helper:
                continue
            if str(getattr(other, "name", "") or "") == helper_name:
                continue
            if not helper_phase_is_restored(str(getattr(other, "phase", "") or "")):
                continue
            other_source = str(getattr(other, "source", "") or "")
            if not other_source:
                continue
            if identity == accepted_statement_identity(
                helper_decl_statement(other_source)
            ):
                return True
    supports = [
        str(name or "").strip()
        for name in list(getattr(helper, "support_names", []) or [])
        if str(name or "").strip()
    ]
    if not supports:
        return False
    from .finite_claim_check import _first_forall_chunk
    from .helper_quality import _conclusion_is_projection_of_premise

    def telescope(statement: str) -> tuple[tuple[str, ...], str]:
        body = canonical_dossier_statement_key(statement)
        binders = []
        while (quantifier := _first_forall_chunk(body)) is not None:
            binder, body = quantifier
            binders.append(binder)
        return tuple(binders), body

    target_binders, target_body = telescope(helper_decl_statement(source))
    # Only ordinary connective wrappers are recognized. Unknown scope stays
    # eligible, and a small connective cap bounds the recursive projection.
    if _SCOPED_PROPOSITION_SYNTAX.search(target_body):
        return False
    if sum(target_body.count(token) for token in ("∧", "∨", "/\\", "\\/")) > 32:
        return False
    premises = []
    for name in supports:
        support = helper_map.get(name)
        if support is None or not helper_phase_is_restored(
            str(getattr(support, "phase", "") or "")
        ):
            return False
        support_source = str(getattr(support, "source", "") or "")
        if not support_source:
            return False
        binders, body = telescope(helper_decl_statement(support_source))
        # Never infer a fact about another binder domain by dropping its
        # telescope (e.g. a Nat fact cannot establish the same text over Int).
        if binders != target_binders or _SCOPED_PROPOSITION_SYNTAX.search(body):
            return False
        premises.append(body)
    # Keep cached statements opaque. Even propositional reasoning that derives
    # a new conclusion from several cached facts can earn a fresh receipt.
    return _conclusion_is_projection_of_premise(
        target_body, premise_keys=set(premises),
    )


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
    Exact restatements and demonstrated propositional wrappers of restored
    facts do not earn milestones. The sweep merges proposition identities
    across samples and recursive scopes.
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
        from .mini_session.progress_identity import helper_progress_keys
        helper_keys = helper_progress_keys(dossier)
        prior = set(prior_formal_evidence)
        # An auxiliary proof can survive rejection of its dispatch's target,
        # even when that outcome deliberately reports no target progress.
        for name, helper in helpers.items():
            if f"helper:{helper_keys[name]}" not in prior:
                helper_names[name] = None
    for name in helper_names:
        helper = helpers.get(name)
        if helper is None:
            continue
        if helper_restates_restored_knowledge(helper, helpers):
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
