"""Purely extract typed Lean candidates from one provider response.

``extract_helpers_and_proof`` returns helpers, a main proof, memoized lemma-DAG
candidates, post-main declarations, and ambiguous extra main chunks. It makes
no model or Lean calls and does not mutate session state.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import List

from ensemble_prover.proof_dossier import (
    canonical_dossier_statement_key,
    helper_decl_name,
)
from ensemble_prover.proof_graph import (
    helper_decl_body,
    helper_decl_kind,
    helper_decl_statement,
)

def _legacy_imports():
    """Lazy import of the legacy extraction primitives.

    Keeps mini_prover.py decoupled from the mini_session subpackage at
    module load time. M6 may inline these once mini_prover.py shrinks.
    """

    from ensemble_prover.mini_prover import (
        _extract_helpers_and_main,
        _extract_lemma_dag_helper_declarations,
        _find_extra_main_proof_chunks,
        _find_helpers_after_final_main,
        _find_post_main_helper_declarations,
        _partition_preamble_redeclarations,
        _salvage_small_multiple_main_submission,
        _top_level_chunks_from_reply,
    )

    return {
        "extract_helpers_and_main": _extract_helpers_and_main,
        "extract_lemma_dag_helper_declarations": _extract_lemma_dag_helper_declarations,
        "find_extra_main_proof_chunks": _find_extra_main_proof_chunks,
        "find_helpers_after_final_main": _find_helpers_after_final_main,
        "find_post_main_helper_declarations": _find_post_main_helper_declarations,
        "partition_preamble_redeclarations": _partition_preamble_redeclarations,
        "salvage_small_multiple_main_submission": (
            _salvage_small_multiple_main_submission
        ),
        "top_level_chunks_from_reply": _top_level_chunks_from_reply,
    }


@dataclass(frozen=True)
class TurnExtraction:
    """Typed bundle returned by ``extract_helpers_and_proof``.

    Fields are populated once at construction; downstream consumers
    treat instances as immutable views over the LLM reply.
    """

    helpers: List[str] = field(default_factory=list)
    proof: object = None  # Optional[str] — kept as object to preserve frozen=True with Optional

    # Computed-once lemma-DAG candidates. Single extraction by construction
    # prevents divergent no-proof and proof-extracted views of one reply.
    lemma_dag_candidates: List[str] = field(default_factory=list)

    # Top-level chunks (used by post-main / extra-main detectors).
    chunks: List[str] = field(default_factory=list)

    # Post-main helper declarations: declarations that appear AFTER the
    # main proof. The orchestrator rejects these as an ordering violation.
    post_main_declarations: List[str] = field(default_factory=list)

    # Extra main proof chunks: multiple ``example`` / bare-``by`` blocks.
    # The orchestrator rejects these as ambiguity.
    extra_main_chunks: List[str] = field(default_factory=list)
    # Small multiple-main replies are normalized to the documented final main
    # proof. This count makes the discarded anonymous candidates observable.
    demoted_main_chunks_dropped: int = 0
    # Immutable-preamble compilation boundary: helper names redeclaring a
    # preamble declaration with equivalent text (dropped — the preamble copy
    # is authoritative) vs. with conflicting content (policy-rejected instead
    # of silently shadowing the verification environment).
    preamble_redeclarations_dropped: List[str] = field(default_factory=list)
    preamble_redeclaration_conflicts: List[str] = field(default_factory=list)

    # Same-target declaration proofs: a top-level theorem/lemma declaration
    # whose body has been normalized into the active proof lane.
    same_target_decl_proof_normalized: bool = False
    same_target_decl_proof_name: str = ""
    same_target_decl_proof_statement_match: bool = False
    same_target_decl_proof_name_match: bool = False
    same_target_decl_proof_block: str = ""
    same_target_decl_proof_chunk_index: int = -1
    same_target_decl_proof_statement: str = ""
    same_target_decl_proof_prefix_declarations: List[str] = field(
        default_factory=list
    )


def _usable_lemma_dag_candidates(
    helpers: List[str],
    *,
    theorem_name: str = "",
    suppress_solution_placeholders: bool = True,
) -> List[str]:
    """Return helper declarations that can sensibly feed lemma-DAG routing.

    M3 documentation note (2026-05-08): legacy ``run_conversation``
    passed helpers verbatim to the lemma-DAG path. This filter is an
    INTENTIONAL deviation from a faithful port — it drops two classes
    of helper that legacy would have processed and inevitably failed
    on:

    1. **Same-name-as-theorem helpers.** The LLM occasionally restates
       the theorem itself as a helper. Lemma-DAG decomposition always
       fails on this (the helper IS the goal) and wastes the slot.

    2. **Empty-body ``:=`` stubs.** A helper of shape ``theorem h : P :=``
       with no body is a sorry-stub — Lean rejects every variant.

    Both classes are caught later by the salvage Lean check anyway, so
    legacy behavior is observably equivalent except for slightly less
    wasted Lean time. The filter is documented here so reviewers know
    it's not a port mistake. Disable by replacing the call site if a
    diagnostic comparison run wants raw legacy behavior.
    """

    out: List[str] = []
    current = str(theorem_name or "").strip()
    for helper in helpers:
        text = str(helper or "").strip()
        name = helper_decl_name(text) or ""
        if suppress_solution_placeholders and _is_solution_placeholder_declaration(
            text, theorem_name=theorem_name
        ):
            continue
        if current and name == current:
            continue
        if name and text.endswith(":=") and not helper_decl_body(text):
            continue
        out.append(helper)
    return out


def _drop_solution_placeholder_declarations(helpers: List[str]) -> List[str]:
    """Remove copied PutnamBench answer placeholders from helper replay."""

    out: List[str] = []
    for helper in helpers:
        text = str(helper or "").strip()
        if _is_solution_placeholder_declaration(text):
            continue
        out.append(helper)
    return out


def _is_solution_placeholder_declaration(
    helper: str,
    *,
    theorem_name: str = "",
) -> bool:
    name = helper_decl_name(str(helper or "").strip()) or ""
    if not name:
        return False
    root = str(theorem_name or "").strip()
    if root and name == f"{root}_solution":
        return True
    return bool(re.fullmatch(r"putnam_\d{4}_[ab]\d+_solution", name))


def _same_target_decl_proof_metadata(
    chunks: List[str],
    *,
    proof: object,
    theorem_name: str = "",
    goal_statement: str = "",
) -> dict[str, object]:
    """Return metadata when a declaration body became the active proof.

    This mirrors the declaration-main paths in ``_extract_helpers_and_main``
    without re-running the legacy extractor. It gives proof-only child runs
    first-class telemetry for the normalized declaration shape instead of
    making dashboards infer it from generic proof/no-proof verdicts.
    """

    proof_text = " ".join(str(proof or "").split())
    if not proof_text:
        return {
            "normalized": False,
            "name": "",
            "statement_match": False,
            "name_match": False,
            "block": "",
            "chunk_index": -1,
            "statement": "",
            "prefix_declarations": [],
        }
    expected_name = str(theorem_name or "").strip()
    expected_statement_key = canonical_dossier_statement_key(goal_statement)
    matches: List[dict[str, object]] = []
    for chunk_index, chunk in enumerate(chunks):
        text = str(chunk or "").strip()
        body = helper_decl_body(text)
        if not body:
            continue
        name = helper_decl_name(text) or ""
        statement = helper_decl_statement(text)
        statement_key = canonical_dossier_statement_key(
            statement
        )
        statement_match = bool(
            expected_statement_key
            and statement_key
            and statement_key == expected_statement_key
        )
        name_match = bool(expected_name and name == expected_name)
        body_match = " ".join(str(body or "").split()) == proof_text
        if not (body_match and (statement_match or name_match)):
            continue
        matches.append({
            "name": name,
            "statement_match": statement_match,
            "name_match": name_match,
            "body_match": body_match,
            "block": text,
            "chunk_index": chunk_index,
            "statement": statement,
        })
    if matches:
        selected = min(
            matches,
            key=lambda item: (
                0 if bool(item.get("name_match")) else 1,
                0 if bool(item.get("statement_match")) else 1,
                0 if bool(item.get("body_match")) else 1,
                int(item.get("chunk_index") or 0),
            ),
        )
        selected_index = int(selected.get("chunk_index") or 0)
        prefix_declarations: List[str] = []
        for prefix_chunk in chunks[:selected_index]:
            prefix_text = str(prefix_chunk or "").strip()
            if helper_decl_kind(prefix_text) not in {
                "theorem",
                "lemma",
                "def",
                "abbrev",
                "instance",
            }:
                continue
            if not helper_decl_name(prefix_text):
                continue
            if not helper_decl_body(prefix_text):
                continue
            prefix_declarations.append(prefix_text)
        return {
            "normalized": True,
            "name": str(selected.get("name") or ""),
            "statement_match": bool(selected.get("statement_match")),
            "name_match": bool(selected.get("name_match")),
            "block": str(selected.get("block") or ""),
            "chunk_index": selected_index,
            "statement": str(selected.get("statement") or ""),
            "prefix_declarations": prefix_declarations,
        }
    return {
        "normalized": False,
        "name": "",
        "statement_match": False,
        "name_match": False,
        "block": "",
        "chunk_index": -1,
        "statement": "",
        "prefix_declarations": [],
    }


def extract_helpers_and_proof(
    content: str,
    *,
    theorem_name: str = "",
    goal_statement: str = "",
    allow_decl_main: bool = True,
    suppress_solution_placeholders: bool = True,
    preamble: str = "",
) -> TurnExtraction:
    """Parse one LLM reply into a typed ``TurnExtraction``.

    Calls the existing extraction primitives in mini_prover.py once and
    bundles their results. Behavior is verbatim equivalent to the legacy
    pre-Lean-check sequence at mini_prover.py:3402-3406 + 3517 (lemma_dag
    candidates) + 3406-3408 (post-main / extra-main).
    """

    primitives = _legacy_imports()

    helpers, proof = primitives["extract_helpers_and_main"](
        content,
        theorem_name=theorem_name,
        goal_statement=goal_statement,
        allow_decl_main=allow_decl_main,
    )
    helpers = list(helpers)
    if suppress_solution_placeholders:
        helpers = [
            helper
            for helper in _drop_solution_placeholder_declarations(helpers)
            if not _is_solution_placeholder_declaration(
                helper,
                theorem_name=theorem_name,
            )
        ]

    # Memoize lemma-DAG candidates ONCE (Bonus #7 single-extraction
    # invariant). The legacy code re-extracted on the proof-extracted
    # branch even when helpers were present; here we always run the
    # extractor and let downstream consumers use ``helpers`` if non-
    # empty (mirroring legacy ``helpers or _extract_lemma_dag(...)``
    # semantics) without re-running the extraction.
    if helpers:
        lemma_dag_candidates = _usable_lemma_dag_candidates(
            list(helpers),
            theorem_name=theorem_name,
            suppress_solution_placeholders=suppress_solution_placeholders,
        )
    else:
        lemma_dag_candidates = list(
            primitives["extract_lemma_dag_helper_declarations"](
                content,
                theorem_name=theorem_name,
                suppress_solution_placeholders=suppress_solution_placeholders,
            )
        )
        if suppress_solution_placeholders:
            lemma_dag_candidates = _drop_solution_placeholder_declarations(
                lemma_dag_candidates
            )
            lemma_dag_candidates = [
                helper
                for helper in lemma_dag_candidates
                if not _is_solution_placeholder_declaration(
                    helper,
                    theorem_name=theorem_name,
                )
            ]

    chunks = list(primitives["top_level_chunks_from_reply"](content))
    extra_main = list(primitives["find_extra_main_proof_chunks"](chunks))
    helpers, proof, demoted_main_chunks_dropped = primitives[
        "salvage_small_multiple_main_submission"
    ](
        helpers,
        proof if isinstance(proof, str) else None,
        chunks,
        max_extra_mains=2,
    )
    if demoted_main_chunks_dropped:
        extra_main = []
        post_main = list(primitives["find_helpers_after_final_main"](chunks))
        lemma_dag_candidates = _usable_lemma_dag_candidates(
            list(helpers),
            theorem_name=theorem_name,
            suppress_solution_placeholders=suppress_solution_placeholders,
        )
    else:
        post_main = list(primitives["find_post_main_helper_declarations"](chunks))
    preamble_redeclarations_dropped: List[str] = []
    preamble_redeclaration_conflicts: List[str] = []
    if preamble:
        (
            helpers,
            preamble_redeclarations_dropped,
            preamble_redeclaration_conflicts,
        ) = primitives["partition_preamble_redeclarations"](helpers, preamble)
    decl_main = _same_target_decl_proof_metadata(
        chunks,
        proof=proof,
        theorem_name=theorem_name,
        goal_statement=goal_statement,
    )

    return TurnExtraction(
        helpers=list(helpers),
        proof=proof,
        lemma_dag_candidates=lemma_dag_candidates,
        chunks=chunks,
        post_main_declarations=post_main,
        extra_main_chunks=extra_main,
        demoted_main_chunks_dropped=demoted_main_chunks_dropped,
        preamble_redeclarations_dropped=preamble_redeclarations_dropped,
        preamble_redeclaration_conflicts=preamble_redeclaration_conflicts,
        same_target_decl_proof_normalized=bool(decl_main["normalized"]),
        same_target_decl_proof_name=str(decl_main["name"]),
        same_target_decl_proof_statement_match=bool(
            decl_main["statement_match"]
        ),
        same_target_decl_proof_name_match=bool(decl_main["name_match"]),
        same_target_decl_proof_block=str(decl_main["block"]),
        same_target_decl_proof_chunk_index=int(decl_main["chunk_index"]),
        same_target_decl_proof_statement=str(decl_main["statement"]),
        same_target_decl_proof_prefix_declarations=list(
            decl_main["prefix_declarations"]
        ),
    )
