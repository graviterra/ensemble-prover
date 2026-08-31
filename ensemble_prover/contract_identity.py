"""Versioned helpers for Lean-authoritative statement contract identities."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Optional, Tuple


LEAN_CONTRACT_IDENTITY_VERSION = 3
SUPPORTED_LEAN_CONTRACT_IDENTITY_VERSIONS = frozenset({2, 3})
LEAN_CONTRACT_EVIDENCE_VERSION = 1
LEAN_CONTRACT_TELESCOPE_EVIDENCE_VERSION = 1
_LEAN_CONTRACT_IDENTITY_RE = re.compile(
    r"^lean-expr-v(?P<version>[23]):"
    r"(?P<full>[0-9a-f]{64}):"
    r"(?P<profile>[0-9a-f]{64}|dependent)$"
)


def make_lean_contract_identity(
    full_expr_hash: str,
    contract_profile_hash: Optional[str],
    *,
    version: int = LEAN_CONTRACT_IDENTITY_VERSION,
) -> str:
    """Build a validated identity from full and proof-erased Expr hashes.

    Version 2 remains readable for durable-record compatibility. New
    elaborations use version 3, whose binder profile is restricted to the
    theorem's outer Pi telescope instead of unfolding its conclusion.
    """

    full = str(full_expr_hash or "").strip().lower()
    profile = str(contract_profile_hash or "dependent").strip().lower()
    if version not in SUPPORTED_LEAN_CONTRACT_IDENTITY_VERSIONS:
        return ""
    candidate = f"lean-expr-v{version}:{full}:{profile}"
    if _LEAN_CONTRACT_IDENTITY_RE.fullmatch(candidate) is None:
        return ""
    return candidate


def parse_lean_contract_identity(identity: str) -> Optional[Tuple[str, str]]:
    """Return ``(full_expr_hash, contract_profile_hash)`` for trusted syntax."""

    match = _LEAN_CONTRACT_IDENTITY_RE.fullmatch(str(identity or "").strip())
    if match is None:
        return None
    return match.group("full"), match.group("profile")


def lean_contract_identity_version(identity: str) -> Optional[int]:
    """Return the evidence format version for a valid identity token."""

    match = _LEAN_CONTRACT_IDENTITY_RE.fullmatch(str(identity or "").strip())
    if match is None:
        return None
    return int(match.group("version"))


def has_current_lean_contract_identity(identity: str) -> bool:
    """Return whether ``identity`` uses the current contract semantics."""

    return lean_contract_identity_version(identity) == LEAN_CONTRACT_IDENTITY_VERSION


def has_lean_contract_identity(identity: str) -> bool:
    """Return whether ``identity`` is a complete supported Lean evidence token."""

    return parse_lean_contract_identity(identity) is not None


def make_lean_contract_evidence_receipt(
    identity: str,
    statement_key: str,
    environment_hash: str,
) -> str:
    """Bind a structural identity to its elaborated source and environment.

    The Expr token alone does not say which declaration produced it.  This
    receipt prevents stale checkpoint/import metadata from attaching a valid-
    looking token to a different helper declaration.  It is an integrity
    binding for trusted internal evidence, not a substitute for Lean.
    """

    structural = str(identity or "").strip()
    statement = str(statement_key or "").strip()
    environment = str(environment_hash or "").strip()
    if not has_lean_contract_identity(structural) or not statement:
        return ""
    payload = "\n".join(
        (
            f"lean-contract-evidence-v{LEAN_CONTRACT_EVIDENCE_VERSION}",
            structural,
            statement,
            environment,
        )
    )
    return "lean-contract-evidence-v1:" + hashlib.sha256(
        payload.encode("utf-8", errors="replace")
    ).hexdigest()


def lean_contract_evidence_receipt_matches(
    receipt: str,
    *,
    identity: str,
    statement_key: str,
    environment_hash: str,
) -> bool:
    """Return whether a durable receipt exactly binds all evidence fields."""

    expected = make_lean_contract_evidence_receipt(
        identity,
        statement_key,
        environment_hash,
    )
    return bool(expected and str(receipt or "").strip() == expected)


def make_lean_contract_telescope_evidence_receipt(
    identity: str,
    statement_key: str,
    environment_hash: str,
    proof_binder_structural_hashes: tuple[str, ...],
    conclusion_structural_hash: str,
    *,
    binder_sorts: tuple[str, ...] = (),
    proof_binder_types: tuple[str, ...] = (),
) -> str:
    """Bind Lean-derived telescope metadata to its statement evidence."""

    structural = str(identity or "").strip()
    statement = str(statement_key or "").strip()
    environment = str(environment_hash or "").strip()
    premise_hashes = tuple(
        str(value or "").strip().lower()
        for value in proof_binder_structural_hashes
    )
    conclusion = str(conclusion_structural_hash or "").strip().lower()
    sorts = tuple(str(value or "").strip().lower() for value in binder_sorts)
    proof_types = tuple(
        str(value or "").strip() for value in proof_binder_types
    )
    if (
        not has_lean_contract_identity(structural)
        or not statement
        or any(re.fullmatch(r"[0-9a-f]{64}", value) is None for value in premise_hashes)
        or re.fullmatch(r"[0-9a-f]{64}", conclusion) is None
        or any(value not in {"proof", "data"} for value in sorts)
        or sum(value == "proof" for value in sorts) != len(proof_types)
        or len(proof_types) != len(premise_hashes)
    ):
        return ""
    payload = json.dumps(
        {
            "conclusion": conclusion,
            "binder_sorts": sorts,
            "environment": environment,
            "identity": structural,
            "premises": premise_hashes,
            "proof_binder_types": proof_types,
            "statement": statement,
            "version": LEAN_CONTRACT_TELESCOPE_EVIDENCE_VERSION,
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    return "lean-contract-telescope-evidence-v1:" + hashlib.sha256(
        payload.encode("utf-8", errors="replace")
    ).hexdigest()


def lean_contract_telescope_evidence_receipt_matches(
    receipt: str,
    *,
    identity: str,
    statement_key: str,
    environment_hash: str,
    proof_binder_structural_hashes: tuple[str, ...],
    conclusion_structural_hash: str,
    binder_sorts: tuple[str, ...] = (),
    proof_binder_types: tuple[str, ...] = (),
) -> bool:
    expected = make_lean_contract_telescope_evidence_receipt(
        identity,
        statement_key,
        environment_hash,
        proof_binder_structural_hashes,
        conclusion_structural_hash,
        binder_sorts=binder_sorts,
        proof_binder_types=proof_binder_types,
    )
    return bool(expected and str(receipt or "").strip() == expected)
