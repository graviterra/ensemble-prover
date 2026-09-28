"""Capture the declarative name-resolution context needed by helper replay."""

from __future__ import annotations

import re
from typing import Sequence

from ..lean_runner import _free_universe_decl

# Lean's identifier alphabet includes punctuation-like letter symbols and
# subscript characters beyond Python's Unicode word class.
_LEAN_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff\u0100-\u017f"
)
_LEAN_SUBSCRIPT = r"\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
LEAN_IDENTIFIER_CONTINUATION = rf"\w'!?{_LEAN_LETTER_LIKE}{_LEAN_SUBSCRIPT}"
_IDENT_COMPONENT = (
    rf"(?:«[^»\r\n]+»|(?:[^\W\d]|_|[{_LEAN_LETTER_LIKE}])"
    rf"[{LEAN_IDENTIFIER_CONTINUATION}]*)"
)
_DOTTED_IDENT = rf"{_IDENT_COMPONENT}(?:\.{_IDENT_COMPONENT})*"
_LEXICAL_IDENTIFIER_RE = re.compile(_DOTTED_IDENT)
_RAW_STRING_START_RE = re.compile(r'r(?P<hashes>#+)?"')
_CHAR_LITERAL_RE = re.compile(
    r"'(?:\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^'\\])'"
)
_NAMESPACE_RE = re.compile(rf"namespace\s+(?P<name>{_DOTTED_IDENT})")
_SECTION_RE = re.compile(rf"section(?:\s+(?P<name>{_DOTTED_IDENT}))?")
_END_RE = re.compile(rf"end(?:\s+(?P<name>{_DOTTED_IDENT}))?")

_CONTEXT_LEXEME = re.compile(rf"{_DOTTED_IDENT}|->|→|[(),]")
_KEYWORDS = frozenset(
    {
        "in",
        "open",
        "scoped",
        "universe",
        "universes",
        "namespace",
        "end",
        "section",
        "variable",
        "variables",
        "axiom",
        "constant",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "class",
        "structure",
        "inductive",
        "mutual",
        "example",
        "set_option",
        "attribute",
        "local",
        "private",
        "protected",
        "noncomputable",
        "unsafe",
        "partial",
        "initialize",
        "builtin_initialize",
        "elab",
        "elab_rules",
        "macro",
        "syntax",
        "import",
        "prelude",
        "opaque",
        "run_cmd",
        "notation",
        "export",
        "include",
        "omit",
        "hiding",
        "renaming",
        "as",
        "by",
        "where",
        "with",
        "deriving",
    }
)


def _tokens(command: str) -> tuple[str, ...]:
    """Lex declarative context without changing quoted identifier contents."""

    tokens: list[str] = []
    cursor = 0
    for match in _CONTEXT_LEXEME.finditer(command):
        if command[cursor : match.start()].strip():
            return ()
        tokens.append(match.group())
        cursor = match.end()
    return tuple(tokens) if not command[cursor:].strip() else ()


def _name(token: str) -> bool:
    return token not in _KEYWORDS and re.fullmatch(_DOTTED_IDENT, token) is not None


def is_promotion_context_command(command: str) -> bool:
    """Accept only Lean's declarative open, universe and namespace grammar."""

    tokens = _tokens(command)
    if not tokens:
        return False
    kind, *tail = tokens
    if kind == "namespace":
        return len(tail) == 1 and _name(tail[0])
    if kind in {"universe", "universes"}:
        return bool(tail) and all(_name(token) for token in tail)
    if kind != "open" or not tail:
        return False
    if tail[0] == "scoped":
        return len(tail) > 1 and all(_name(token) for token in tail[1:])
    if not _name(tail[0]):
        return False
    if len(tail) > 1 and tail[1] == "(":
        return (
            len(tail) > 3
            and tail[-1] == ")"
            and all(_name(token) for token in tail[2:-1])
        )
    if len(tail) > 1 and tail[1] == "hiding":
        return len(tail) > 2 and all(_name(token) for token in tail[2:])
    if len(tail) > 1 and tail[1] == "renaming":
        remainder = tail[2:]
        while len(remainder) >= 3:
            if not (
                _name(remainder[0])
                and remainder[1] in {"→", "->"}
                and _name(remainder[2])
            ):
                return False
            remainder = remainder[3:]
            if not remainder:
                return True
            if remainder[0] != "," or len(remainder) == 1:
                return False
            remainder = remainder[1:]
        return False
    return all(_name(token) for token in tail)


def _normalize(command: str) -> str:
    return " ".join(_tokens(command))


def _comment_end(text: str, start: int) -> int | None:
    if text.startswith("--", start):
        newline = text.find("\n", start + 2)
        return len(text) if newline < 0 else newline
    if not text.startswith("/-", start):
        return None
    depth = 1
    end = start + 2
    while end < len(text) and depth:
        if text.startswith("/-", end):
            depth += 1
            end += 2
        elif text.startswith("-/", end):
            depth -= 1
            end += 2
        else:
            end += 1
    return end


def _literal_end(text: str, start: int) -> int | None:
    """Read a literal only at a token boundary established by the scanner."""

    if text[start] == "r":
        raw = _RAW_STRING_START_RE.match(text, start)
        if raw is not None:
            closing = '"' + (raw.group("hashes") or "")
            closing_index = text.find(closing, raw.end())
            return len(text) if closing_index < 0 else closing_index + len(closing)
    if text[start] == "'":
        character = _CHAR_LITERAL_RE.match(text, start)
        return character.end() if character is not None else None
    if text[start] != '"':
        return None
    end = start + 1
    while end < len(text):
        if text[end] == "\\":
            end += 2
        elif text[end] == '"':
            return end + 1
        else:
            end += 1
    return len(text)


def _mask_lean_noncode(source: str, *, mask_syntax_quotations: bool = False) -> str:
    """Mask Lean comments/literals, preserving names, offsets and newlines.

    Consume identifiers as whole tokens, including quoted names and primes.
    In comments and literals, guillemets are data and cannot hide delimiters.
    Policy checks can retain syntax quotations to inspect meta antiquotations;
    context/declaration scans instead mask their balanced contents as data.
    """

    text = str(source or "")
    out = list(text)
    pairs = {"(": ")", "[": "]", "{": "}"}
    quotation_stack: list[str] = []
    index = 0

    def mask(start: int, end: int) -> None:
        for position in range(start, end):
            if out[position] not in {"\n", "\r"}:
                out[position] = " "

    while index < len(text):
        end = _comment_end(text, index)
        if end is None:
            end = _literal_end(text, index)
        if end is not None:
            mask(index, end)
            index = end
            continue
        identifier = _LEXICAL_IDENTIFIER_RE.match(text, index)
        if identifier is not None:
            if quotation_stack:
                mask(index, identifier.end())
            index = identifier.end()
            continue
        if (
            mask_syntax_quotations
            and text[index] == "`"
            and index + 1 < len(text)
            and text[index + 1] in pairs
        ):
            quotation_stack.append(pairs[text[index + 1]])
            mask(index, index + 2)
            index += 2
            continue
        if quotation_stack:
            mask(index, index + 1)
            if text[index] in pairs:
                quotation_stack.append(pairs[text[index]])
            elif text[index] == quotation_stack[-1]:
                quotation_stack.pop()
        index += 1
    return "".join(out)


def _masked_preamble(preamble: str) -> str:
    return _mask_lean_noncode(preamble, mask_syntax_quotations=True)


def promotion_context_commands(preamble: str) -> tuple[str, ...]:
    """Capture ordered declarative context in every still-active Lean scope.

    Namespace scopes stay explicit: opening a namespace is not equivalent to
    elaborating inside it. The published bundle is nested below these scopes,
    preserving relative resolution without replaying problem assumptions.
    """

    scopes: list[tuple[str, str, list[str]]] = [("root", "", [])]
    lines = [
        line.strip()
        for line in _masked_preamble(str(preamble or "")).splitlines()
        if line.strip()
    ]
    consumed = 0
    for index, stripped in enumerate(lines):
        if index < consumed:
            continue
        namespace = _NAMESPACE_RE.fullmatch(stripped)
        section = _SECTION_RE.fullmatch(
            re.sub(r"^noncomputable\s+(?=section\b)", "", stripped)
        )
        scope = namespace or section
        closing = _END_RE.fullmatch(stripped)
        if scope is not None:
            kind, name = ("namespace" if namespace else "section"), scope.group(
                "name"
            ) or ""
            segments = re.findall(_IDENT_COMPONENT, name) if namespace else [name]
            for segment in segments:
                scopes.append((kind, segment, []))
        elif closing:
            if len(scopes) > 1:
                names = re.findall(_IDENT_COMPONENT, closing.group("name") or "")
                if not names:
                    scopes.pop()
                else:
                    for scope_index in range(len(scopes) - 1, 0, -1):
                        if lean_name_components(
                            scopes[scope_index][1]
                        ) == lean_name_components(names[-1]):
                            del scopes[max(1, scope_index - len(names) + 1) :]
                            break
        elif re.match(r"(?:namespace|section|end)\b", stripped):
            raise ValueError("unsupported promotion context scope")
        elif re.match(r"(?:open|universes?)\b", stripped):
            following = index + 1
            while following < len(lines):
                continuation = _tokens(lines[following])
                if not continuation or continuation[0] in _KEYWORDS - {
                    "hiding",
                    "renaming",
                }:
                    break
                if not all(
                    _name(token)
                    or token in {"hiding", "renaming", "(", ")", ",", "→", "->"}
                    for token in continuation
                ):
                    break
                stripped += " " + lines[following]
                following += 1
            consumed = following
            tokens = _CONTEXT_LEXEME.findall(stripped)
            # Command-local opens never become ambient context, including
            # the form whose `in` begins a subsequent line.
            if (
                "in" in tokens
                or following < len(lines)
                and re.match(r"in\b", lines[following])
            ):
                continue
            if not is_promotion_context_command(stripped):
                raise ValueError("unsupported promotion context command")
            scopes[-1][2].append(_normalize(stripped))
    commands: list[str] = []
    for kind, name, scoped_commands in scopes:
        if kind == "namespace":
            commands.append("namespace " + name)
        commands.extend(scoped_commands)
    return tuple(commands)


def validate_promotion_context(commands: Sequence[str]) -> tuple[str, ...]:
    """Validate persisted context while retaining command order and scopes."""

    if not isinstance(commands, (list, tuple)) or any(
        not isinstance(command, str) for command in commands
    ):
        raise ValueError("promotion context must be an array of strings")
    result: list[str] = []
    for command in commands:
        if (
            "\n" in command
            or "\r" in command
            or not is_promotion_context_command(command)
        ):
            raise ValueError("invalid promotion context command")
        result.append(_normalize(command))
    return tuple(result)


def promotion_context_namespace(commands: Sequence[str]) -> str:
    """Return the namespace created by validated, unclosed context scopes."""

    return ".".join(
        command.removeprefix("namespace ")
        for command in validate_promotion_context(commands)
        if command.startswith("namespace ")
    )


def split_promotion_context(source: str) -> tuple[tuple[str, ...], str]:
    """Separate an already validated helper's leading replay commands."""

    lines = source.splitlines()
    count = 0
    while count < len(lines) and is_promotion_context_command(lines[count].strip()):
        count += 1
    context = validate_promotion_context(tuple(line.strip() for line in lines[:count]))
    if not any(command.startswith("namespace ") for command in context):
        # Preserve existing context-free bundle identities and publications.
        return (), source
    return context, "\n".join(lines[count:])


def helper_promotion_context(source: str, commands: Sequence[str]) -> tuple[str, ...]:
    """Restore free universes exactly as the acceptance checker does."""

    context = validate_promotion_context(commands)
    universe = _free_universe_decl(source, declared_in="\n".join((*context, source)))
    return validate_promotion_context((*context, universe) if universe else context)


def lean_name_components(name: str) -> tuple[str, ...]:
    """Compare Lean names without conflating quoted dots with separators."""

    if re.fullmatch(_DOTTED_IDENT, name) is None:
        return ()
    return tuple(
        segment[1:-1] if segment.startswith("«") else segment
        for segment in re.findall(_IDENT_COMPONENT, name)
    )
