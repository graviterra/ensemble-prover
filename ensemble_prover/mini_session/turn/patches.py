"""Patch support for iterative mini-session proof repair.

The LLM can submit a small fenced ``lean-patch``/``proof-patch`` block
instead of regenerating a long proof.  Patches apply to the latest retained
assistant proof body in the conversation history, then the ordinary extraction
and Lean verification pipeline consumes the reconstructed full proof.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Sequence, Tuple


_PATCH_FENCE_RE = re.compile(
    r"```[ \t]*(?:lean-?patch|proof-?patch|patch)[^\n`]*\n(.*?)```",
    re.IGNORECASE | re.DOTALL,
)
_SEARCH_REPLACE_RE = re.compile(
    r"<<<<<<<[ \t]*SEARCH[ \t]*\n(.*?)\n=======[ \t]*\n(.*?)\n>>>>>>>[ \t]*REPLACE[ \t]*",
    re.IGNORECASE | re.DOTALL,
)
_LINE_HUNK_RE = re.compile(
    r"^@@[ \t]*(?:lines?[ \t]+)?(\d+)(?:[ \t]*(?:-|:|,)[ \t]*(\d+))?[ \t]*(?:@@)?[ \t]*$",
    re.IGNORECASE | re.MULTILINE,
)


@dataclass(frozen=True)
class ProofPatchApplication:
    requested: bool = False
    applied: bool = False
    content: str = ""
    previous_content: str = ""
    previous_proof: str = ""
    patched_proof: str = ""
    error: str = ""
    hunk_count: int = 0
    metadata: Dict[str, Any] = field(default_factory=dict)


def apply_proof_patch_from_reply(
    content: str,
    *,
    history: Sequence[Dict[str, Any]],
    theorem_name: str = "",
    goal_statement: str = "",
    suppress_solution_placeholders: bool = True,
) -> ProofPatchApplication:
    """Apply a model-supplied proof patch to the latest retained proof.

    Supported patch formats inside a fenced ``lean-patch``/``proof-patch`` block:

    ``<<<<<<< SEARCH`` / ``=======`` / ``>>>>>>> REPLACE``
        Exact search/replace hunks against the previous proof body.

    ``@@ 45-50``
        Replace 1-indexed inclusive proof-body line range with the following
        lines, up to the next ``@@`` hunk.
    """

    patch_blocks = _patch_blocks(content)
    if not patch_blocks:
        return ProofPatchApplication(content=str(content or ""))

    previous_content, previous_helpers, previous_proof = _latest_assistant_proof(
        history,
        theorem_name=theorem_name,
        goal_statement=goal_statement,
        suppress_solution_placeholders=suppress_solution_placeholders,
    )
    if not previous_proof:
        return ProofPatchApplication(
            requested=True,
            applied=False,
            content=str(content or ""),
            previous_content=previous_content,
            error="no_previous_proof",
            hunk_count=0,
        )

    patched = str(previous_proof or "")
    total_hunks = 0
    for block in patch_blocks:
        next_patched, hunk_count, error = _apply_patch_block(patched, block)
        if error:
            return ProofPatchApplication(
                requested=True,
                applied=False,
                content=str(content or ""),
                previous_content=previous_content,
                previous_proof=previous_proof,
                patched_proof=patched,
                error=error,
                hunk_count=total_hunks,
            )
        patched = next_patched
        total_hunks += hunk_count

    if _normalise_for_change_check(patched) == _normalise_for_change_check(previous_proof):
        return ProofPatchApplication(
            requested=True,
            applied=False,
            content=str(content or ""),
            previous_content=previous_content,
            previous_proof=previous_proof,
            patched_proof=patched,
            error="patch_no_change",
            hunk_count=total_hunks,
        )

    patched_content = _render_patched_reply(previous_helpers, patched)
    return ProofPatchApplication(
        requested=True,
        applied=True,
        content=patched_content,
        previous_content=previous_content,
        previous_proof=previous_proof,
        patched_proof=patched,
        error="",
        hunk_count=total_hunks,
        metadata={
            "proof_patch_applied": True,
            "proof_patch_hunk_count": total_hunks,
            "previous_proof_line_count": len(str(previous_proof or "").splitlines()),
            "patched_proof_line_count": len(str(patched or "").splitlines()),
        },
    )


def format_proof_patch_failure_feedback(error: str) -> str:
    reason = str(error or "patch_failed").strip() or "patch_failed"
    return (
        "Your proof patch could not be applied to the latest retained Lean "
        f"proof attempt (`{reason}`). Submit either a full fenced `lean` "
        "proof block, or a fenced `lean-patch` block using exact hunks:\n\n"
        "<<<<<<< SEARCH\n"
        "<copy exact previous proof lines>\n"
        "=======\n"
        "<replacement lines>\n"
        ">>>>>>> REPLACE\n\n"
        "Or use an inclusive proof-body line range:\n\n"
        "@@ 45-50\n"
        "<replacement lines>"
    )


def _patch_blocks(content: str) -> List[str]:
    return [match.group(1) for match in _PATCH_FENCE_RE.finditer(str(content or ""))]


def _latest_assistant_proof(
    history: Sequence[Dict[str, Any]],
    *,
    theorem_name: str,
    goal_statement: str,
    suppress_solution_placeholders: bool,
) -> Tuple[str, List[str], str]:
    try:
        from ensemble_prover.mini_session.turn.extract import extract_helpers_and_proof
    except Exception:
        return "", [], ""

    for msg in reversed(list(history or ())):
        if msg.get("role") != "assistant" or msg.get("tool_calls"):
            continue
        previous_content = str(msg.get("content", "") or "")
        if not previous_content.strip():
            continue
        try:
            extraction = extract_helpers_and_proof(
                previous_content,
                theorem_name=theorem_name,
                goal_statement=goal_statement,
                allow_decl_main=True,
                suppress_solution_placeholders=suppress_solution_placeholders,
            )
        except Exception:
            continue
        proof = extraction.proof if isinstance(extraction.proof, str) else ""
        if proof.strip():
            return previous_content, list(extraction.helpers or ()), proof
    return "", [], ""


def _apply_patch_block(proof: str, block: str) -> Tuple[str, int, str]:
    search_hunks = list(_SEARCH_REPLACE_RE.finditer(str(block or "")))
    if search_hunks:
        patched = proof
        for match in search_hunks:
            search = _strip_one_edge_newline(match.group(1))
            replacement = _strip_one_edge_newline(match.group(2))
            if not search:
                return proof, 0, "empty_search_hunk"
            if search not in patched:
                return proof, 0, "search_hunk_not_found"
            patched = patched.replace(search, replacement, 1)
        return patched, len(search_hunks), ""

    line_hunks = list(_LINE_HUNK_RE.finditer(str(block or "")))
    if line_hunks:
        return _apply_line_hunks(proof, str(block or ""), line_hunks)

    return proof, 0, "no_supported_patch_hunks"


def _apply_line_hunks(
    proof: str,
    block: str,
    line_hunks: Sequence[re.Match[str]],
) -> Tuple[str, int, str]:
    lines = str(proof or "").splitlines()
    replacements: List[Tuple[int, int, List[str]]] = []
    for index, match in enumerate(line_hunks):
        start = int(match.group(1))
        end = int(match.group(2) or start)
        if start <= 0 or end < start:
            return proof, 0, "invalid_line_range"
        next_start = line_hunks[index + 1].start() if index + 1 < len(line_hunks) else len(block)
        replacement_text = block[match.end():next_start]
        replacement_lines = _strip_one_edge_newline(replacement_text).splitlines()
        replacements.append((start, end, replacement_lines))
    original_line_count = len(lines)
    patched = list(lines)
    for start, end, replacement_lines in sorted(replacements, reverse=True):
        if end > original_line_count:
            return proof, 0, "line_range_out_of_bounds"
        patched[start - 1:end] = replacement_lines
    trailing_newline = "\n" if str(proof or "").endswith("\n") else ""
    return "\n".join(patched) + trailing_newline, len(replacements), ""


def _render_patched_reply(helpers: Sequence[str], proof: str) -> str:
    lean_parts = [str(item or "").strip() for item in helpers or () if str(item or "").strip()]
    proof_text = str(proof or "").strip()
    if proof_text:
        lean_parts.append(proof_text)
    lean_block = "\n\n".join(lean_parts)
    return "Applied patch to the previous Lean proof attempt.\n\n```lean\n" + lean_block + "\n```"


def _strip_one_edge_newline(text: str) -> str:
    out = str(text or "")
    if out.startswith("\n"):
        out = out[1:]
    if out.endswith("\n"):
        out = out[:-1]
    return out


def _normalise_for_change_check(text: str) -> str:
    return "\n".join(line.rstrip() for line in str(text or "").strip().splitlines())
