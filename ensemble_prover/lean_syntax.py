"""Small Lean syntax normalizers shared by prover front-ends.

These helpers intentionally do not know any mathematics. They only repair
common surface syntax drift in model output before Lean sees it.
"""

from __future__ import annotations

import re
import unicodedata

from .utils import _lean_lexical_skip_end


# Lean's inaccessible/shadowed-name marker (e.g. ``a✝``, ``x✝¹``). It is a
# Symbol-category code point, so the permissive Unicode-operator fallback in
# ``_lean_relation_binder_parts`` would otherwise misread ``a✝ : Nat`` as a
# relation binder ``a ✝ (: Nat)`` — splitting the marker off the identifier.
# It is always part of a name, never an infix relation.
_LEAN_NAME_MARKER_CHARS = frozenset("✝")

_LEAN_CHAR_LITERAL_START_PRECEDERS = frozenset("([{⦃⟨,;:=<>+-*/^%&|!~?")
_LEAN_SURFACE_GROUP_OPEN_TO_CLOSE = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⦃": "⦄",
    "⟨": "⟩",
}
_LEAN_LET_IN_BINDER_OPERATORS = (
    "∀ᶠ",
    "∃ᶠ",
    "∑",
    "∏",
    "∫",
    "⨍",
    "⋃",
    "⋂",
    "⨆",
    "⨅",
    "∐",
)


def lean_expression_delimiters_balanced(text: str) -> bool:
    """Whether model-supplied term text has balanced surface delimiters.

    This is an inexpensive rejection layer, not a command boundary: Lean's
    error recovery can still leave a parenthesized malformed term and resume
    parsing whitespace-separated commands.  Callers that interpolate the text
    must additionally parse it as exactly one complete Lean term.
    """

    raw = str(text or "")
    stack: list[str] = []
    close_to_open = {
        close: open_token
        for open_token, close in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.items()
    }
    index = 0
    while index < len(raw):
        skip_to = _lean_surface_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        token = raw[index]
        if token in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            stack.append(token)
        elif token in close_to_open:
            if not stack or stack[-1] != close_to_open[token]:
                return False
            stack.pop()
        index += 1
    return not stack


def _lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'"


def _lean_surface_lexical_skip_end(text: str, index: int) -> int | None:
    raw = str(text or "")
    if index < 0 or index >= len(raw):
        return None
    if raw[index] == "'":
        previous = raw[index - 1] if index > 0 else ""
        if previous and not previous.isspace() and previous not in (
            _LEAN_CHAR_LITERAL_START_PRECEDERS
        ):
            return None
    return _lean_lexical_skip_end(raw, index)


def _top_level_quantifier_token_len(text: str, index: int) -> int:
    ch = text[index] if 0 <= index < len(text) else ""
    if ch in {"∀", "∃"}:
        return 1
    for token in ("forall", "exists"):
        end = index + len(token)
        if not text.startswith(token, index):
            continue
        before_ok = index == 0 or not _lean_ident_char(text[index - 1])
        after_ok = end >= len(text) or not _lean_ident_char(text[end])
        if before_ok and after_ok:
            return len(token)
    return 0


def _lean_quoted_identifier_end(text: str, index: int) -> int:
    if index < 0 or index >= len(text) or text[index] != "«":
        return -1
    return text.find("»", index + 1)


def _lean_keyword_at(text: str, index: int, keyword: str) -> bool:
    token = str(keyword or "")
    if not token or not text.startswith(token, index):
        return False
    before_ok = index == 0 or not _lean_ident_char(text[index - 1])
    after_index = index + len(token)
    after_ok = after_index >= len(text) or not _lean_ident_char(text[after_index])
    return before_ok and after_ok


def _top_level_let_rec_after_let(raw: str, index: int) -> bool:
    i = index + len("let")
    while i < len(raw) and raw[i].isspace():
        i += 1
    return _lean_keyword_at(raw, i, "rec")


def _let_in_candidate_is_body_separator(
    raw: str,
    assign_index: int,
    in_index: int,
) -> bool:
    last_binder_operator = -1
    last_comma = -1
    depth = 0
    index = assign_index + 2
    while index < in_index:
        skip_to = _lean_surface_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = min(skip_to, in_index)
            continue
        ch = raw[index]
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            if ch == ",":
                last_comma = index
            else:
                for operator in _LEAN_LET_IN_BINDER_OPERATORS:
                    if raw.startswith(operator, index):
                        last_binder_operator = index
                        index += len(operator) - 1
                        break
        index += 1
    return not (last_binder_operator != -1 and last_comma < last_binder_operator)


def _top_level_let_body_start(text: str, index: int) -> int:
    raw = str(text or "")
    if not _lean_keyword_at(raw, index, "let"):
        return -1
    equation_style_let_rec = _top_level_let_rec_after_let(raw, index)
    assign_index = -1
    depth = 0
    i = index + len("let")
    while i < len(raw) - 1:
        skip_to = _lean_surface_lexical_skip_end(raw, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = raw[i]
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif ch == ":" and raw[i + 1] == "=" and depth == 0:
            assign_index = i
            break
        elif equation_style_let_rec and depth == 0 and ch == ";":
            return i + 1
        elif equation_style_let_rec and depth == 0 and ch in "\r\n":
            line_end = (
                i + 2
                if ch == "\r" and i + 1 < len(raw) and raw[i + 1] == "\n"
                else i + 1
            )
            suffix = raw[line_end:]
            indent_len = len(suffix) - len(suffix.lstrip(" \t"))
            visible_suffix = suffix[indent_len:].lstrip()
            if indent_len == 0 and visible_suffix and not visible_suffix.startswith("|"):
                return line_end
        i += 1
    if assign_index < 0:
        return -1

    depth = 0
    i = assign_index + 2
    while i < len(raw):
        skip_to = _lean_surface_lexical_skip_end(raw, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = raw[i]
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ";":
            return i + 1
        elif depth == 0 and ch in "\r\n":
            line_end = (
                i + 2
                if ch == "\r" and i + 1 < len(raw) and raw[i + 1] == "\n"
                else i + 1
            )
            assigned_prefix = raw[assign_index + 2 : i].strip()
            suffix = raw[line_end:].strip()
            if assigned_prefix and suffix:
                return line_end
        elif depth == 0 and _lean_keyword_at(raw, i, "in"):
            if _let_in_candidate_is_body_separator(raw, assign_index, i):
                return i + len("in")
        i += 1
    return -1


def _lean_relation_binder_parts(text: str) -> tuple[str, str, str] | None:
    """Split a top-level relation-style binder into left/operator/right."""

    value = str(text or "").strip()
    if not value:
        return None
    tokens = ("∈", "∉", "≤", "≥", "≠", "<=", ">=", "=", "<", ">", "∣")
    depth = 0
    index = 0
    while index < len(value):
        skip_to = _lean_surface_lexical_skip_end(value, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = value[index]
        if ch == "«":
            end = _lean_quoted_identifier_end(value, index)
            if end >= 0:
                index = end + 1
                continue
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            for token in tokens:
                if not value.startswith(token, index):
                    continue
                if token == "=" and (
                    value.startswith("=>", index)
                    or (index > 0 and value[index - 1] in {":", "!"})
                ):
                    continue
                left = value[:index].strip()
                right = value[index + len(token) :].strip()
                if left and right:
                    return left, token, right
            # Lean permits user-defined and Unicode infix relations in this
            # binder shorthand. A closed whitelist silently drops valid
            # premises such as `s ⊆ Set.univ`; recognize any top-level
            # operator token while excluding binder/body separators.
            if (
                not ch.isalnum()
                and not ch.isspace()
                and ch not in _LEAN_NAME_MARKER_CHARS
                and (
                    unicodedata.category(ch).startswith("S")
                    or ch in "!#$%&*+./<=>?@\\^|-~"
                )
            ):
                end = index + 1
                while end < len(value):
                    next_ch = value[end]
                    if next_ch.isalnum() or next_ch.isspace():
                        break
                    if next_ch in _LEAN_NAME_MARKER_CHARS:
                        break
                    if not (
                        unicodedata.category(next_ch).startswith("S")
                        or next_ch in "!#$%&*+./<=>?@\\^|-~"
                    ):
                        break
                    end += 1
                token = value[index:end]
                if token not in {":", ":=", "=>", "→", "↔", ",", ";"}:
                    left = value[:index].strip()
                    right = value[end:].strip()
                    if left and right:
                        return left, token, right
                index = end
                continue
        index += 1
    return None


def lean_relation_binder_premise(text: str) -> str:
    """Return ``text`` when it is a Lean relation-style binder premise.

    Lean accepts binders such as ``∀ n ≥ 2, P n`` and ``∀ x ∈ S, P x`` as
    shorthand for an ordinary binder plus an implication premise. Contract
    checks need to see that premise explicitly.
    """

    value = str(text or "").strip()
    if _lean_relation_binder_parts(value) is not None:
        return value
    return ""


def lean_relation_binder_parts(text: str) -> tuple[str, str, str] | None:
    """Return the parsed pieces of a relation-style Lean binder.

    This is the shared parser behind premise extraction, bound-name recovery,
    and proof-state identity normalization. Keeping one implementation avoids
    a closed operator whitelist in downstream canonicalizers silently
    disagreeing with Lean syntax such as ``E ⊆ ⋃ i, s i``.
    """

    return _lean_relation_binder_parts(text)


def lean_relation_binder_bound_names(text: str) -> tuple[str, ...]:
    """Return the variable introduced by a relation-style binder.

    In ``∀ n ≥ 2, P n`` and ``∀ x ∈ S, P x``, the left-hand identifier
    is both an implicit binder and part of the generated premise.  Only a
    single syntactic identifier is accepted here; compound left expressions
    are not guessed to introduce variables.
    """

    parts = _lean_relation_binder_parts(text)
    if parts is None:
        return ()
    left, _operator, _right = parts
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", left):
        return (left,)
    if left.startswith("«") and left.endswith("»") and len(left) > 2:
        return (left,)
    return ()


def _lean_strip_outer_type_ascription(text: str) -> str:
    raw = str(text or "").strip()
    if len(raw) < 3 or raw[0] != "(" or raw[-1] != ")":
        return raw
    depth = 0
    colon = -1
    index = 1
    while index < len(raw) - 1:
        skip_to = _lean_surface_lexical_skip_end(raw, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = raw[index]
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            if depth == 0:
                return raw
            depth -= 1
        elif depth == 0 and ch == ":" and not raw.startswith(":=", index):
            if colon >= 0:
                return raw
            colon = index
        index += 1
    if depth != 0 or colon < 0:
        return raw
    value = raw[1:colon].strip()
    type_text = raw[colon + 1 : -1].strip()
    return value if value and type_text else raw


def lean_relation_binder_equivalent(left: str, right: str) -> bool:
    """Compare relation shorthand without erasing elaboration-relevant types."""

    left_parts = _lean_relation_binder_parts(left)
    right_parts = _lean_relation_binder_parts(right)
    if left_parts is None or right_parts is None:
        return False
    left_lhs, left_op, left_rhs = left_parts
    right_lhs, right_op, right_rhs = right_parts

    def compact(value: str) -> str:
        return re.sub(r"\s+", "", str(value or ""))

    return bool(
        left_op == right_op
        and compact(left_lhs) == compact(right_lhs)
        and compact(left_rhs) == compact(right_rhs)
    )


def split_lean_top_level_implications(statement: str) -> list[str]:
    """Split outer Lean implications without entering quantifier scope.

    This is intentionally syntactic, but it respects one important Lean
    precedence rule: a top-level ``forall``/``exists`` scopes over the formula
    to its right. Arrows in an existential witness type, or in a quantified
    conclusion such as ``A -> forall x, B x -> C x``, are therefore not outer
    theorem premises.
    """

    text = str(statement or "")
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        skip_to = _lean_surface_lexical_skip_end(text, index)
        if skip_to is not None:
            index = skip_to
            continue
        ch = text[index]
        if ch == "«":
            end = _lean_quoted_identifier_end(text, index)
            if end >= 0:
                index = end + 1
                continue
        if ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE:
            depth += 1
        elif ch in _LEAN_SURFACE_GROUP_OPEN_TO_CLOSE.values():
            depth = max(0, depth - 1)
        elif depth == 0:
            let_body_start = _top_level_let_body_start(text, index)
            if let_body_start >= 0:
                if start > 0 or text[start:index].strip():
                    break
                index = let_body_start
                continue
            if _top_level_quantifier_token_len(text, index):
                break
            if ch == "→":
                parts.append(text[start:index].strip())
                start = index + 1
            elif text.startswith("->", index) and (
                index == 0 or text[index - 1] != "<"
            ):
                parts.append(text[start:index].strip())
                start = index + 2
                index += 1
        index += 1
    parts.append(text[start:].strip())
    return [part for part in parts if part]


_BANG_NAME_SKIP = frozenset(
    {
        "aesop",
        "by_contra",
        "congr",
        "constructor",
        "contrapose",
        "ext",
        "field_simp",
        "gcongr",
        "intro",
        "intros",
        "itauto",
        "linarith",
        "nlinarith",
        "norm_num",
        "omega",
        "positivity",
        "push_neg",
        "ring",
        "ring_nf",
        "simp",
        "simp_all",
        "tauto",
    }
)


def _is_atom_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'.«»✝↑"


def _factorial_atom_start(out: list[str], end: int) -> int | None:
    """Return the start of the postfix term ending at ``end``.

    A closing square bracket is not an atom by itself in expressions such as
    ``xs[i] !``: it is a postfix operation on ``xs``.  Likewise, a field
    projection after a parenthesized or indexed term belongs to the same
    postfix chain.  Walk those chains backwards so an explicitly separated
    factorial does not detach the final suffix from its receiver.
    """

    if end <= 0:
        return None
    last = out[end - 1]
    if last in ")]}⦄":
        pairs = {")": "(", "]": "[", "}": "{", "⦄": "⦃"}
        opener = pairs[last]
        depth = 0
        for i in range(end - 1, -1, -1):
            ch = out[i]
            if ch == last:
                depth += 1
            elif ch == opener:
                depth -= 1
                if depth == 0:
                    start = i
                    if last == "]" and start > 0 and not out[start - 1].isspace():
                        receiver_start = _factorial_atom_start(out, start)
                        if receiver_start is not None:
                            start = receiver_start
                    if start > 0 and out[start - 1] == "↑":
                        start -= 1
                    return start
        return None
    i = end - 1
    while i >= 0 and _is_atom_char(out[i]):
        i -= 1
    start = i + 1
    if start >= end:
        return None
    if out[start] == "." and start > 0:
        receiver_start = _factorial_atom_start(out, start)
        if receiver_start is not None:
            start = receiver_start
    return start


def _clean_factorial_expr(expr: str) -> str | None:
    clean = str(expr or "").strip()
    while clean.startswith("↑"):
        clean = clean[1:].strip()
    if not clean:
        return None
    if clean in _BANG_NAME_SKIP:
        return None
    # Retain the legacy protection for plain uppercase-qualified names such as
    # ``List.get``.  Restrict it to identifier-shaped candidates so grouped
    # applications and explicitly separated postfix chains can still be
    # normalized as factorial expressions.
    if all(_is_atom_char(ch) for ch in clean):
        head = clean.split(".", 1)[0]
        if head[:1].isupper():
            return None
    return clean


def _attached_bang_is_identifier(out: list[str], end: int) -> bool:
    """Whether an attached ``!`` belongs to Lean's preceding lexical token.

    Lean permits bang identifiers (``get!``, ``rfl!``, ``foo!``), and its
    unchecked indexing notation is written ``xs[i]!``.  Rewriting either form
    as factorial changes valid Lean.  A space before ``!`` disambiguates the
    postfix factorial; so do a closing parenthesis and numeric atoms or tuple
    projections, which cannot absorb ``!`` into an identifier.
    """

    if end != len(out) or end <= 0:
        return False
    if out[end - 1] == "]":
        return True
    if not _is_atom_char(out[end - 1]):
        return False
    start = end - 1
    while start >= 0 and _is_atom_char(out[start]):
        start -= 1
    token = "".join(out[start + 1 : end])
    # Keep compatibility with the benchmark's legacy one-letter factorials
    # (``n!``) as well as numerals and tuple projections (``p.1!``).  Longer
    # attached names are lexically bang identifiers, independent of whether
    # Lean happens to know a declaration with that name.
    return not (
        len(token) == 1
        or token.isdigit()
        or re.search(r"(?:^|\.)\d+$", token)
    )


def _normalize_factorials_in_code(raw: str) -> str:
    out: list[str] = []
    i = 0
    n = len(raw)
    while i < n:
        ch = raw[i]
        if ch != "!" or (i + 1 < n and raw[i + 1] == "="):
            out.append(ch)
            i += 1
            continue

        next_nonspace = i + 1
        while next_nonspace < n and raw[next_nonspace].isspace():
            next_nonspace += 1
        if next_nonspace < n and raw[next_nonspace] == "[":
            out.append(ch)
            i += 1
            continue

        end = len(out)
        while end > 0 and out[end - 1].isspace():
            end -= 1
        if _attached_bang_is_identifier(out, end):
            out.append(ch)
            i += 1
            continue
        start = _factorial_atom_start(out, end)
        if start is None:
            out.append(ch)
            i += 1
            continue
        expr = "".join(out[start:end])
        clean = _clean_factorial_expr(expr)
        if clean is None:
            out.append(ch)
            i += 1
            continue

        if clean == "s" and i + 1 < n and raw[i + 1] == '"':
            out.append(ch)
            i += 1
            continue

        if (
            start > 0
            and out[start - 1] == "("
            and next_nonspace < n
            and raw[next_nonspace] == ")"
        ):
            start -= 1
            i = next_nonspace + 1
        else:
            i += 1
        del out[start:]
        out.append(f"(Nat.factorial ({clean}))")
    return "".join(out)


def normalize_postfix_factorial_spacing(text: str) -> str:
    """Collapse whitespace before Lean's postfix factorial token.

    Models sometimes write Mathlib signatures as ``m !`` after seeing pretty
    Lean diagnostics, but Lean parses that spacing poorly. Outside comments
    and strings, ``atom !`` is normalized to ``atom!``.
    """

    raw = str(text or "")
    if "!" not in raw:
        return raw
    out: list[str] = []
    i = 0
    in_line_comment = False
    block_depth = 0
    in_string = False
    escaped = False

    def previous_can_bind_factorial() -> bool:
        j = len(out) - 1
        while j >= 0 and out[j].isspace():
            j -= 1
        if j < 0:
            return False
        ch = out[j]
        return ch.isalnum() or ch in "_')}]»"

    n = len(raw)
    while i < n:
        ch = raw[i]
        nxt = raw[i + 1] if i + 1 < n else ""

        if in_line_comment:
            out.append(ch)
            if ch == "\n":
                in_line_comment = False
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append(ch)
                out.append(nxt)
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.append(ch)
                out.append(nxt)
                i += 2
                continue
            out.append(ch)
            i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append(ch)
            out.append(nxt)
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append(ch)
            out.append(nxt)
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch.isspace():
            j = i
            while j < n and raw[j].isspace():
                j += 1
            if (
                j < n
                and raw[j] == "!"
                and (j + 1 >= n or raw[j + 1] != "=")
                and previous_can_bind_factorial()
            ):
                out.append("!")
                i = j + 1
                continue
            out.append(raw[i:j])
            i = j
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def normalize_nat_factorial_notation(text: str) -> str:
    """Rewrite model-emitted postfix Nat factorial syntax to `Nat.factorial`.

    The benchmark sources sometimes use notation such as ``(m)!`` in theorem
    declarations, but model-generated helper statements and proofs often place
    factorials inside ``∀`` types, calc blocks, or copied Lean diagnostics where
    the postfix form is fragile.  This pass rewrites explicit ``x !`` and
    ``(x + y)!`` occurrences, plus legacy one-letter ``x!`` notation, to
    ``Nat.factorial`` outside comments and strings. Attached multichar bang
    identifiers and unchecked indexing such as ``xs[i]!`` are left alone.
    """

    raw = str(text or "")
    if "!" not in raw:
        return raw
    out: list[str] = []
    code: list[str] = []
    i = 0
    n = len(raw)
    in_line_comment = False
    block_depth = 0
    in_string = False
    escaped = False

    def flush_code() -> None:
        if code:
            out.append(_normalize_factorials_in_code("".join(code)))
            code.clear()

    while i < n:
        ch = raw[i]
        nxt = raw[i + 1] if i + 1 < n else ""

        if in_line_comment:
            out.append(ch)
            if ch == "\n":
                in_line_comment = False
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append(ch)
                out.append(nxt)
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.append(ch)
                out.append(nxt)
                i += 2
                continue
            out.append(ch)
            i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == "-" and nxt == "-":
            flush_code()
            in_line_comment = True
            out.append(ch)
            out.append(nxt)
            i += 2
            continue
        if ch == "/" and nxt == "-":
            flush_code()
            block_depth = 1
            out.append(ch)
            out.append(nxt)
            i += 2
            continue
        if ch == "!" and nxt == '"' and code and code[-1] == "s":
            if len(code) == 1 or not _is_atom_char(code[-2]):
                prefix = "".join(code[:-1])
                if prefix:
                    out.append(_normalize_factorials_in_code(prefix))
                code.clear()
                out.append("s!")
                i += 1
                continue
        if ch == '"':
            flush_code()
            in_string = True
            out.append(ch)
            i += 1
            continue

        code.append(ch)
        i += 1

    flush_code()
    return "".join(out)
