"""Schema and parser-version stamps for durable prover artifacts."""

from __future__ import annotations

import hashlib
from typing import Any, Dict

# Bump when Lean declaration parsing semantics change in a way that affects
# serialized statements/types (lemma index, memory statements, guidance data).
STATEMENT_PARSER_VERSION = "2026-05-07-binder-folding-v4"

# Per-artifact schema versions.  These govern serialized metadata contracts.
LEMMA_INDEX_META_SCHEMA_VERSION = 2
GUIDANCE_ARTIFACT_SCHEMA_VERSION = 3
MEMORY_ENTRY_SCHEMA_VERSION = 2
PROVEN_LEMMA_ENTRY_SCHEMA_VERSION = 1

# Length of the preamble fingerprint hex prefix stamped onto proof-bearing
# artifacts.  16 hex chars = 64 bits of SHA-256, collision-resistant for the
# tiny cardinality of distinct preamble configs a single project sees.
PREAMBLE_FINGERPRINT_LEN = 16

# ── Canonical version-key names (single source of truth) ──────────────
_VERSION_KEY_SCHEMA = "artifact_schema_version"
_VERSION_KEY_PARSER = "statement_parser_version"
_VERSION_KEY_PREAMBLE_FP = "preamble_fingerprint"


def _make_versions(schema_version: int, parser_version: str) -> Dict[str, Any]:
    """Build a canonical version dict.  Every version dict in the system
    should ultimately originate from this function."""
    return {
        _VERSION_KEY_SCHEMA: schema_version,
        _VERSION_KEY_PARSER: parser_version,
    }


def compute_preamble_fingerprint(
    preamble_import: str, preamble_tactics: str
) -> str:
    """Return a short, stable fingerprint of the effective Lean preamble.

    The fingerprint covers the two runtime-configurable preamble sources:
    * ``preamble_import`` — ``import`` lines prepended to every Lean check.
    * ``preamble_tactics`` — ATP tactic-pack macros/DSL appended after imports.

    Proof text persisted in ``proven_lemmas.jsonl`` / ``memory_*.jsonl`` can
    reference those macros directly; if either input changes, stored proofs
    silently become stale.  Stamping this fingerprint onto each entry and
    rejecting mismatched entries at load time closes that gap in the same way
    ``proof_cache.jsonl``'s context key already does for Lean verification.

    A literal separator is interposed so ``("ab", "")`` cannot collide with
    ``("a", "b")``.
    """
    payload = (
        (preamble_import or "")
        + "\n---preamble-tactics---\n"
        + (preamble_tactics or "")
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[
        :PREAMBLE_FINGERPRINT_LEN
    ]


def _with_optional_preamble_fingerprint(
    versions: Dict[str, Any], preamble_fingerprint: str
) -> Dict[str, Any]:
    if preamble_fingerprint:
        versions[_VERSION_KEY_PREAMBLE_FP] = preamble_fingerprint
    return versions


def current_lemma_index_versions() -> Dict[str, Any]:
    # Lemma index persists declaration signatures only — no proof text, so no
    # coupling to preamble_tactics.  Intentionally excluded from fingerprint.
    return _make_versions(LEMMA_INDEX_META_SCHEMA_VERSION, STATEMENT_PARSER_VERSION)


def current_guidance_versions(
    preamble_fingerprint: str = "",
) -> Dict[str, Any]:
    return _with_optional_preamble_fingerprint(
        _make_versions(GUIDANCE_ARTIFACT_SCHEMA_VERSION, STATEMENT_PARSER_VERSION),
        preamble_fingerprint,
    )


def current_memory_versions(
    preamble_fingerprint: str = "",
) -> Dict[str, Any]:
    return _with_optional_preamble_fingerprint(
        _make_versions(MEMORY_ENTRY_SCHEMA_VERSION, STATEMENT_PARSER_VERSION),
        preamble_fingerprint,
    )


def current_proven_lemma_versions(
    preamble_fingerprint: str = "",
) -> Dict[str, Any]:
    return _with_optional_preamble_fingerprint(
        _make_versions(PROVEN_LEMMA_ENTRY_SCHEMA_VERSION, STATEMENT_PARSER_VERSION),
        preamble_fingerprint,
    )


def stamp_versions(target: Dict[str, Any], versions: Dict[str, Any]) -> Dict[str, Any]:
    """Merge canonical version keys into *target* and return *target*.

    Use this in write paths so version key names are never duplicated:

        meta = stamp_versions({"created_at": time.time(), ...},
                              current_guidance_versions())
    """
    target.update(versions)
    return target


def versions_match(found: Dict[str, Any] | None, expected: Dict[str, Any]) -> bool:
    """Return True iff *found* contains every key in *expected* with the same
    string representation.

    A nonempty preamble fingerprint is identity-bearing rather than ordinary
    optional metadata: it cannot be ignored merely because *expected* omitted
    the key.  That prevents a fingerprinted proof artifact from silently
    crossing into an unspecified preamble environment.

    Raises ``ValueError`` if *expected* is empty (would vacuously accept
    anything, masking bugs in callers).
    """
    if not expected:
        raise ValueError(
            "versions_match called with empty expected dict — "
            "this would accept any artifact and is almost certainly a bug"
        )
    if not isinstance(found, dict):
        return False
    found_preamble_fingerprint = str(found.get(_VERSION_KEY_PREAMBLE_FP, ""))
    expected_preamble_fingerprint = str(
        expected.get(_VERSION_KEY_PREAMBLE_FP, "")
    )
    if found_preamble_fingerprint and not expected_preamble_fingerprint:
        return False
    for key, exp in expected.items():
        if str(found.get(key, "")) != str(exp):
            return False
    return True
