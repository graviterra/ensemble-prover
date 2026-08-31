"""Comment- and delimiter-aware parsing of Lean declaration headers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'"


def _matches_word(text: str, i: int, word: str) -> bool:
    end = i + len(word)
    if end > len(text) or text[i:end] != word:
        return False
    prev = text[i - 1] if i > 0 else ""
    nxt = text[end] if end < len(text) else ""
    if prev and _is_ident_char(prev):
        return False
    if nxt and _is_ident_char(nxt):
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
        return k - line_start
    return None


@dataclass
class _LetFrame:
    indent: int
    keyword_pos: int
    assignment_pending: bool = True


@dataclass
class _HaveFrame:
    indent: int
    keyword_pos: int


def _consume_inline_assignment_opener(
    let_stack: list[_LetFrame],
    have_stack: list[_HaveFrame],
    line_start: int,
    current_indent: int,
) -> bool:
    latest_let_idx: Optional[int] = None
    latest_let_pos = -1
    for idx in range(len(let_stack) - 1, -1, -1):
        frame = let_stack[idx]
        if frame.assignment_pending and (
            frame.keyword_pos >= line_start or current_indent > frame.indent
        ):
            latest_let_idx = idx
            latest_let_pos = frame.keyword_pos
            break

    latest_have_pos = -1
    if have_stack:
        have = have_stack[-1]
        if have.keyword_pos >= line_start or current_indent > have.indent:
            latest_have_pos = have.keyword_pos
    if latest_have_pos > latest_let_pos:
        have_stack.pop()
        return True
    if latest_let_idx is not None:
        let_stack[latest_let_idx].assignment_pending = False
        return True
    return False


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
    and inside inline/local assignments such as ``have ... := ...``.
    """
    i = max(0, int(start_idx))
    if max_scan is not None and max_scan > 0:
        n = min(len(text), i + int(max_scan))
    else:
        n = len(text)

    depth = 0
    line_start = text.rfind("\n", 0, i) + 1
    let_stack: list[_LetFrame] = []
    have_stack: list[_HaveFrame] = []
    top_level_match_seen = False
    while i < n:
        if i + 1 < n and text.startswith("--", i):
            i = _skip_line_comment(text, i, n)
            continue
        if i + 1 < n and text.startswith("/-", i):
            i = _skip_block_comment(text, i, n)
            continue

        ch = text[i]
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

        if ch in "([{":
            depth += 1
            i += 1
            continue
        if ch in ")]}":
            depth = max(0, depth - 1)
            i += 1
            continue

        if depth == 0:
            if _matches_word(text, i, "match"):
                top_level_match_seen = True
            if (
                allow_equations
                and ch == "|"
                and not let_stack
                and not have_stack
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
            if _matches_word(text, i, "let"):
                let_stack.append(
                    _LetFrame(indent=_line_indent_at(text, i), keyword_pos=i)
                )
                i += 3
                continue
            if _matches_word(text, i, "have"):
                have_stack.append(
                    _HaveFrame(indent=_line_indent_at(text, i), keyword_pos=i)
                )
                i += 4
                continue
            if let_stack and _matches_word(text, i, "in"):
                let_stack.pop()
                i += 2
                continue
            if let_stack and ch == ";":
                let_stack.pop()
                i += 1
                continue
            if ch == "\n":
                line_start = i + 1
                next_indent = _next_code_line_indent(text, i + 1, n)
                if next_indent is None:
                    have_stack.clear()
                else:
                    while have_stack and next_indent <= have_stack[-1].indent:
                        have_stack.pop()
            if let_stack and ch == "\n":
                if next_indent is None:
                    let_stack.clear()
                else:
                    while let_stack and next_indent <= let_stack[-1].indent:
                        let_stack.pop()
            if _matches_word(text, i, "where"):
                if _consume_inline_assignment_opener(
                    let_stack,
                    have_stack,
                    line_start,
                    current_indent=_line_indent_at(text, i),
                ):
                    i += 5
                    continue
                if allow_where:
                    return i
                return None
            if text.startswith(":=", i):
                if _consume_inline_assignment_opener(
                    let_stack,
                    have_stack,
                    line_start,
                    current_indent=_line_indent_at(text, i),
                ):
                    i += 2
                    continue
                return i + 2

        i += 1

    return None


def _next_top_level_body_token(text: str, start: int, end: int) -> Optional[str]:
    """Find the next clause arrow or declaration assignment outside patterns."""

    i = max(0, int(start))
    n = min(len(text), int(end))
    depth = 0
    while i < n:
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
        i += 1
    return None
