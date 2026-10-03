"""Cheap discovery of scratch evidence worth replaying at a selected target.

These heuristics never establish equality, implication, or proof acceptance.
Every selected candidate still needs an independent Lean check at the target.
"""
from collections import Counter
import re


def statement_may_close_target(statement: str, target: str) -> bool:
    """Reserve root replay for closely related headers, in linear time.

    Parentheses and whitespace are deliberately ignored for *discovery* only.
    Equal token inventories are conservative candidate discovery; their order
    and binding still have to agree in Lean. This deliberately avoids replaying
    auxiliaries that merely share many of the root's hypotheses.
    """
    def tokens(text: str) -> Counter[str]:
        return Counter(re.findall(r"[\w']+|[^\s()]", str(text or "")))

    left, right = tokens(statement), tokens(target)
    if not left or not right:
        return False
    return left == right


def _accepted_scratch_target_candidate(bridge_source: str) -> str:
    """Embed a scratch declaration in a candidate proof of the active target.

    This is a candidate, never an equivalence judgment. Lean must check the
    resulting proof against the exact target and audit its axioms before it can
    bypass the helper cutpoint. Keeping the original binder list is essential:
    extracting only a declaration's body loses its explicit hypotheses.
    """
    import hashlib
    from .mini_lean_extract import _strip_lean_comments
    from .proof_graph import (
        _helper_decl_header,
        _SCOPED_OPEN_DECL_PREFIX_RE,
        helper_decl_statement,
    )

    source = str(bridge_source or "").strip()
    if _SCOPED_OPEN_DECL_PREFIX_RE.match(_strip_lean_comments(source)):
        return ""
    source = re.sub(
        r"^(\s*(?:noncomputable\s+)?)example\b",
        r"\1lemma mini_scratch_evidence",
        source,
    )
    header = _helper_decl_header(source)
    if header is None or header[0] not in {"lemma", "theorem"}:
        return ""
    # A fresh local name avoids shadowing identifiers in the submitted proof.
    name = "mini_checked_target_" + hashlib.sha256(
        source.encode("utf-8", errors="replace")
    ).hexdigest()[:16]
    while name in source:
        name += "_fresh"
    local = "have " + name + header[2]
    statement = helper_decl_statement(source)
    if not statement:
        return ""
    # `change` checks definitional equality before Lean executes the expensive
    # proof body. An auxiliary theorem with similar hypotheses fails here.
    guard = "  change (" + statement.replace("\n", "\n    ") + ")\n"
    return "by\n" + guard + "\n".join("  " + line for line in local.split("\n")) + (
        "\n  exact @" + name
    )
