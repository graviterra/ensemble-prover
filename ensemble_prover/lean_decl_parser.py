"""Comment- and delimiter-aware parsing of Lean declaration headers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


# These term forms all introduce a local assignment before the declaration's
# own body separator. Match whole keywords: ``letI`` is not the word ``let``.
_LET_KEYWORDS = (
    "let", "letI", "let_delayed", "let_tmp", "let_fun", "let_λ", "let_mvar%", "let_expr",
)
_HAVE_KEYWORDS = ("have", "haveI")
_OPTIONAL_ASSIGNMENT_KEYWORDS = ("obtain", "have", "let")


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'?!"


def _matches_word(text: str, i: int, word: str) -> bool:
    end = i + len(word)
    if end > len(text) or text[i:end] != word:
        return False
    prev = text[i - 1] if i > 0 else ""
    nxt = text[end] if end < len(text) else ""
    if prev and (_is_ident_char(prev) or prev == "."):
        return False
    # Punctuation-terminated syntax has no identifier boundary: Lean accepts
    # ``let_mvar%?m`` without whitespace before the metavariable identifier.
    if nxt and _is_ident_char(word[-1]) and (_is_ident_char(nxt) or nxt == "."):
        return False
    return True


def _skip_line_comment(text: str, i: int, n: int) -> int:
    j = i + 2
    while j < n and text[j] != "\n":
        j += 1
    return j


def _skip_block_comment(text: str, i: int, n: int) -> int:
    depth = 1
    j = i + 2
    while j < n and depth > 0:
        if j + 1 < n and text.startswith("/-", j):
            depth += 1
            j += 2
            continue
        if j + 1 < n and text.startswith("-/", j):
            depth -= 1
            j += 2
            continue
        j += 1
    return j


def _skip_string_literal(text: str, i: int, n: int) -> int:
    j = i + 1
    while j < n:
        ch = text[j]
        if ch == "\\":
            j += 2
            continue
        if ch == '"':
            return j + 1
        j += 1
    return j


def _skip_quoted_identifier(text: str, i: int, n: int) -> int:
    end = text.find("»", i + 1, n)
    return n if end < 0 else end + 1


def _skip_char_literal(text: str, i: int, n: int) -> int:
    """Skip a Lean 4 character literal ``'x'``, including escape sequences.

    Returns the index just past the closing ``'``, or *i* unchanged if
    the token at *i* is not a valid char-literal opener (so the caller
    can fall through to identifier handling for the apostrophe).
    """
    # Lean char literals: 'a', '\n', '\x41', '\u0041'
    # Must not match trailing apostrophe in identifiers (e.g. x')
    if i > 0 and _is_ident_char(text[i - 1]):
        return i  # apostrophe inside identifier — not a char literal
    j = i + 1
    if j >= n:
        return i
    if text[j] == "\\":
        # Escape sequence: skip backslash + at least one char
        j += 2
    else:
        j += 1
    if j < n and text[j] == "'":
        return j + 1  # valid char literal consumed
    return i  # not a char literal — return unchanged so caller treats ' as normal


def _raw_string_hash_count(text: str, i: int) -> Optional[int]:
    if i < 0 or i >= len(text) or text[i] != '"':
        return None
    j = i - 1
    hashes = 0
    while j >= 0 and text[j] == "#":
        hashes += 1
        j -= 1
    if j < 0 or text[j] != "r":
        return None
    prev = text[j - 1] if j > 0 else ""
    if prev and _is_ident_char(prev):
        return None
    return hashes


def _skip_raw_string_literal(text: str, i: int, n: int, hashes: int) -> int:
    closing = '"' + ("#" * hashes)
    j = i + 1
    while j < n:
        if text.startswith(closing, j):
            return j + len(closing)
        j += 1
    return n


def _line_indent_at(text: str, i: int) -> int:
    line_start = text.rfind("\n", 0, i) + 1
    indent = 0
    while line_start + indent < len(text) and text[line_start + indent] in " \t":
        indent += 1
    return indent


def _next_code_line_indent(text: str, i: int, n: int) -> Optional[int]:
    j = i
    while j < n:
        line_start = j
        k = line_start
        while k < n and text[k] in " \t":
            k += 1
        if k >= n:
            return None
        if text[k] == "\n":
            j = k + 1
            continue
        if k + 1 < n and text.startswith("--", k):
            j = _skip_line_comment(text, k, n)
            if j < n and text[j] == "\n":
                j += 1
            continue
        if k + 1 < n and text.startswith("/-", k):
            j = _skip_block_comment(text, k, n)
            continue
        # A block comment can move j into the middle of this physical line.
        # Its following space is not the line's indentation.
        return _line_indent_at(text, k)
    return None


@dataclass
class _LocalBindingFrame:
    indent: int
    keyword_pos: int
    keyword_end: int
    assignment_pending: bool = True
    type_match_seen: bool = False
    recursive: bool = False
    assignment_optional: bool = False


def _next_code_position(text: str, i: int, n: int) -> int:
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            i = _skip_line_comment(text, i, n)
        elif text.startswith("/-", i):
            i = _skip_block_comment(text, i, n)
        else:
            break
    return i


def _consume_inline_assignment_opener(
    frames: list[_LocalBindingFrame],
    line_start: int,
    current_indent: int,
) -> Optional[_LocalBindingFrame]:
    for frame in reversed(frames):
        if frame.assignment_pending and (
            frame.keyword_pos >= line_start or current_indent >= frame.indent
        ):
            frame.assignment_pending = False
            return frame
    return None


def find_decl_header_end(
    text: str,
    start_idx: int,
    *,
    max_scan: Optional[int] = None,
    allow_where: bool = False,
    allow_equations: bool = False,
) -> Optional[int]:
    """Find end of a Lean declaration header.

    Returns the exclusive end index:
    - just after top-level ``:=`` when declaration is assignment-style
    - right before top-level ``where`` when ``allow_where=True``
    - right before a layout equation clause when ``allow_equations=True``

    The scanner ignores ``:=`` tokens that occur inside top-level
    ``let ... := ...; ...`` / ``let ... := ... in ...`` type expressions
    (including Lean layout-style ``let`` blocks without explicit ``;``/``in``),
    their local-instance/auxiliary forms (``letI``, ``let_delayed``, etc.),
    and inside inline/local assignments such as ``have``, ``haveI``, and
    tactic-local ``obtain`` (whose assignment may also be omitted).
    """
    i = max(0, int(start_idx))
    if max_scan is not None and max_scan > 0:
        n = min(len(text), i + int(max_scan))
    else:
        n = len(text)

    depth = 0
    line_start = text.rfind("\n", 0, i) + 1
    frames: list[_LocalBindingFrame] = []
    pending_binder_commas = 0
    top_level_match_seen = False
    last_code_position = i
    while i < n:
        if i + 1 < n and text.startswith("--", i):
            i = _skip_line_comment(text, i, n)
            continue
        if i + 1 < n and text.startswith("/-", i):
            i = _skip_block_comment(text, i, n)
            continue

        ch = text[i]
        if not ch.isspace():
            last_code_position = i
        if ch == "«":
            i = _skip_quoted_identifier(text, i, n)
            continue
        if ch == "'":
            after = _skip_char_literal(text, i, n)
            if after != i:
                i = after
                continue
        if ch == '"':
            raw_hashes = _raw_string_hash_count(text, i)
            if raw_hashes is not None:
                i = _skip_raw_string_literal(text, i, n, raw_hashes)
            else:
                i = _skip_string_literal(text, i, n)
            continue

        if ch in "([{⟨⦃":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩⦄":
            depth = max(0, depth - 1)
            i += 1
            continue

        if depth == 0:
            if ch in "∀∃ΣΠ∑∏⨆⨅" or _matches_word(text, i, "forall"):
                pending_binder_commas += 1
            if ch == ",":
                if pending_binder_commas:
                    pending_binder_commas -= 1
                elif (
                    frames
                    and frames[-1].recursive
                    and _next_top_level_body_token(text, i + 1, n) == ":="
                ):
                    # Lean's let-rec group has comma-separated declarations;
                    # each assignment needs consuming. Match discriminants
                    # and patterns reach a clause arrow instead. Equation-
                    # style local definitions also need no := consumed.
                    frames[-1].assignment_pending = True
                    frames[-1].type_match_seen = False
            if _matches_word(text, i, "match"):
                top_level_match_seen = True
                if frames and frames[-1].assignment_pending:
                    frames[-1].type_match_seen = True
            if (
                ch == "|"
                and frames
                and frames[-1].assignment_pending
                and not frames[-1].type_match_seen
                and _next_top_level_body_token(text, i + 1, n) == "=>"
            ):
                # Local equation definitions have no assignment token. Their
                # clause arrow supplies the value; the next := can be the
                # theorem's proof. Match clauses in the local type do not.
                frames[-1].assignment_pending = False
            if (
                allow_equations
                and ch == "|"
                and not frames
                and not text[line_start:i].strip()
            ):
                # A theorem type may itself begin a continuation line with
                # absolute-value/norm notation (``|x|``). An equation clause
                # follows an already complete nonempty type and reaches its
                # ``=>`` before any assignment-style body opener.
                header_prefix = text[start_idx:i]
                last_colon = header_prefix.rfind(":")
                has_type_before_clause = bool(
                    last_colon >= 0 and header_prefix[last_colon + 1 :].strip()
                )
                if (
                    has_type_before_clause
                    and not top_level_match_seen
                    and _next_top_level_body_token(text, i + 1, n) == "=>"
                ):
                    return i
            keywords = (
                _LET_KEYWORDS if ch == "l" else
                _HAVE_KEYWORDS if ch == "h" else
                _OPTIONAL_ASSIGNMENT_KEYWORDS if ch == "o" else ()
            )
            keyword = next(
                (word for word in keywords if _matches_word(text, i, word)), None
            )
            if keyword is not None:
                next_token = i + len(keyword)
                while next_token < n:
                    if text[next_token].isspace():
                        next_token += 1
                    elif text.startswith("--", next_token):
                        next_token = _skip_line_comment(text, next_token, n)
                    elif text.startswith("/-", next_token):
                        next_token = _skip_block_comment(text, next_token, n)
                    else:
                        break
                frames.append(
                    _LocalBindingFrame(
                        indent=_line_indent_at(text, i),
                        keyword_pos=i,
                        keyword_end=i + len(keyword),
                        recursive=keyword == "let" and _matches_word(text, next_token, "rec"),
                        assignment_optional=keyword in _OPTIONAL_ASSIGNMENT_KEYWORDS,
                    )
                )
                i += len(keyword)
                continue
            if frames and _matches_word(text, i, "in"):
                frames.pop()
                i += 2
                continue
            if frames and ch == ";":
                frames.pop()
                i += 1
                continue
            if ch == "\n":
                line_start = i + 1
                next_indent = _next_code_line_indent(text, i + 1, n)
                if next_indent is None:
                    frames.clear()
                else:
                    next_code = _next_code_position(text, i + 1, n)
                    # ``obtain h : P`` and Mathlib's ``have/let h : P`` can
                    # open a subgoal without ``:=``.
                    # Retire that pending assignment at the next tactic;
                    # retain explicit assignment/type continuations so their
                    # separator is never mistaken for the theorem's proof.
                    while frames and (
                        next_indent < frames[-1].indent
                        or (next_indent == frames[-1].indent and not frames[-1].assignment_pending)
                        or (
                            frames[-1].assignment_optional
                            and frames[-1].assignment_pending
                            and (
                                text.startswith("·", next_code)
                                or _matches_word(text, next_code, "case")
                                or (
                                    next_indent == frames[-1].indent
                                    and last_code_position >= frames[-1].keyword_end
                                    and text[last_code_position] not in ":,→↦∧∨↔=≠≤≥<>+-*/^"
                                    and not text.startswith((":", "|", "(", "{", "[", "⦃"), next_code)
                                    and _next_top_level_body_token(
                                        text, next_code, n, include_type_colon=True
                                    ) != ":"
                                )
                            )
                        )
                    ):
                        frames.pop()
            if _matches_word(text, i, "where"):
                frame = _consume_inline_assignment_opener(
                    frames, line_start, current_indent=_line_indent_at(text, i)
                )
                if frame is not None:
                    i += len("where")
                    continue
                if allow_where:
                    return i
                return None
            if text.startswith(":=", i):
                if _consume_inline_assignment_opener(
                    frames, line_start, current_indent=_line_indent_at(text, i)
                ) is not None:
                    i += 2
                    continue
                return i + 2

        i += 1

    return None


def _next_top_level_body_token(
    text: str, start: int, end: int, *, include_type_colon: bool = False,
) -> Optional[str]:
    """Find the next clause arrow or declaration assignment outside patterns."""

    i = max(0, int(start))
    n = min(len(text), int(end))
    depth = 0
    while i < n:
        if text[i] == "«":
            i = _skip_quoted_identifier(text, i, n)
            continue
        if text.startswith("--", i):
            i = _skip_line_comment(text, i, n)
            continue
        if text.startswith("/-", i):
            i = _skip_block_comment(text, i, n)
            continue
        if text[i] == '"':
            raw_hashes = _raw_string_hash_count(text, i)
            i = (
                _skip_raw_string_literal(text, i, n, raw_hashes)
                if raw_hashes is not None
                else _skip_string_literal(text, i, n)
            )
            continue
        if text[i] == "'":
            after = _skip_char_literal(text, i, n)
            if after != i:
                i = after
                continue
        if text[i] in "([{":
            depth += 1
            i += 1
            continue
        if text[i] in ")]}":
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            if text.startswith("=>", i):
                return "=>"
            if text.startswith(":=", i):
                return ":="
            if include_type_colon and text[i] == ":":
                return ":"
        i += 1
    return None
