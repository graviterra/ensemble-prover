"""Close the binder prefix in Lean's printed declaration signatures."""

from __future__ import annotations


def closed_declaration_type(rendered: str) -> str:
    """Return a type term for a printed signature or an already closed type.

    ``#check`` may print ``(n : Nat) : n = n`` after the declaration name.
    That header is not a type term until its binders become a telescope.
    This conversion supplies syntax only; consumers must still compare it
    with the actual declaration's elaborated type in Lean.
    """
    text = str(rendered or "").strip()
    if text.startswith(":"):
        return text[1:].strip()
    if not text.startswith(("(", "{", "[", "⦃")):
        return text

    from ..proof_graph import _declaration_type_colon, helper_decl_statement
    from ..utils import _binder_segment_parts, _split_binder_segment

    colon = _declaration_type_colon(text)
    if colon is None:
        return text
    binders = _split_binder_segment(text[:colon])
    if not binders or any(
        _binder_segment_parts(binder)[0] not in {"(", "{", "[", "⦃"}
        for binder in binders
    ):
        return text
    # Reuse the declaration parser's lexical islands, binder defaults, and
    # layout handling. The synthetic body is parsed only, never checked.
    closed = helper_decl_statement(
        f"theorem _miniTheoryDeclarationType {text}\n:= by exact ?_"
    )
    return closed or text
