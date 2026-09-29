"""Offset-preserving Lean lexical masks shared by source consumers."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, Optional


_RAW_STRING_START_RE = re.compile(r'r(?P<hashes>#+)?"')
_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff\u0100-\u017f"
)
_IDENT_FIRST_RE = re.compile(rf"[A-Za-z_{_LETTER_LIKE}]")
_IDENT_REST_RE = re.compile(
    rf"[A-Za-z0-9_'!?{_LETTER_LIKE}\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c]"
)


def _mask_noncode(
    text: str, *, mask_quoted_identifiers: bool = False, preserve_doc_comments: bool = False,
) -> str:
    """Mask comments/literals, optionally names, preserving offsets/newlines."""

    src = str(text or "")
    out = list(src)
    n = len(src)
    i = 0

    def mask(start: int, end: int) -> None:
        for pos in range(start, min(end, n)):
            if out[pos] not in {"\n", "\r"}:
                out[pos] = " "

    while i < n:
        if src[i] == "«":
            # Lean's escaped identifier ends at the first »; its contents
            # cannot start comments, strings, or nested syntax quotations.
            close = src.find("»", i + 1)
            end = n if close < 0 else close + 1
            if mask_quoted_identifiers:
                mask(i, end)
            i = end
            continue
        if src.startswith("--", i):
            end = src.find("\n", i + 2)
            end = n if end < 0 else end
            mask(i, end)
            i = end
            continue
        if src.startswith("/-", i):
            depth = 1
            end = i + 2
            while end < n and depth:
                if src.startswith("/-", end):
                    depth += 1
                    end += 2
                elif src.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            # Documentation openers are parser syntax. Header consumers stop
            # before them so imports/helpers cannot detach a declaration's doc.
            documentation = preserve_doc_comments and src.startswith(("/--", "/-!"), i)
            mask(i + 3 if documentation else i, end)
            i = end
            continue
        raw_match = _RAW_STRING_START_RE.match(src, i) if src[i] == "r" else None
        if raw_match is not None and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_")):
            hashes = raw_match.group("hashes") or ""
            raw_delimiter = '"' + hashes
            body_start = raw_match.end()
            close_at = src.find(raw_delimiter, body_start)
            end = n if close_at < 0 else close_at + len(raw_delimiter)
            mask(i, end)
            i = end
            continue
        if src[i] == '"':
            end = i + 1
            while end < n:
                if src[end] == "\\":
                    end += 2
                    continue
                if src[end] == '"':
                    end += 1
                    break
                end += 1
            mask(i, end)
            i = end
            continue
        if src[i] == "`" and i + 1 < n and src[i + 1] in "([{":
            # Lean syntax quotations can contain command-shaped text, e.g.
            # `` `(theorem generated : True := by trivial) ``. These are
            # macro data, not declarations in the input module. Mask a
            # balanced quotation so a line-oriented declaration scan cannot
            # select a quoted theorem as the target.
            pairs = {"(": ")", "[": "]", "{": "}"}
            stack = [pairs[src[i + 1]]]
            end = i + 2
            while end < n and stack:
                if src[end] == "«":
                    close = src.find("»", end + 1)
                    end = n if close < 0 else close + 1
                    continue
                if src.startswith("--", end):
                    newline = src.find("\n", end + 2)
                    end = n if newline < 0 else newline
                    continue
                raw_match = _RAW_STRING_START_RE.match(src, end) if src[end] == "r" else None
                if raw_match is not None and (
                    end == 0
                    or not (src[end - 1].isalnum() or src[end - 1] == "_")
                ):
                    hashes = raw_match.group("hashes") or ""
                    raw_delimiter = '"' + hashes
                    body_start = raw_match.end()
                    close_at = src.find(raw_delimiter, body_start)
                    end = n if close_at < 0 else close_at + len(raw_delimiter)
                    continue
                if src[end] == "'" and (
                    end == 0
                    or not (src[end - 1].isalnum() or src[end - 1] in "_'")
                ):
                    char_end = end + 1
                    char_end += 2 if char_end < n and src[char_end] == "\\" else 1
                    if char_end < n and src[char_end] == "'":
                        end = char_end + 1
                        continue
                if src.startswith("/-", end):
                    depth = 1
                    end += 2
                    while end < n and depth:
                        if src.startswith("/-", end):
                            depth += 1
                            end += 2
                        elif src.startswith("-/", end):
                            depth -= 1
                            end += 2
                        else:
                            end += 1
                    continue
                if src[end] == '"':
                    end += 1
                    while end < n:
                        if src[end] == "\\":
                            end += 2
                            continue
                        if src[end] == '"':
                            end += 1
                            break
                        end += 1
                    continue
                char = src[end]
                if char in pairs:
                    stack.append(pairs[char])
                elif stack and char == stack[-1]:
                    stack.pop()
                end += 1
            mask(i, end)
            i = end
            continue
        if src[i] == "'" and (
            i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")
        ):
            end = i + 1
            if end < n and src[end] == "\\":
                end += 2
            else:
                end += 1
            if end < n and src[end] == "'":
                end += 1
                mask(i, end)
                i = end
                continue
        i += 1
    return "".join(out)


def _command_matches(
    pattern: re.Pattern[str], masked: str, *, end: Optional[int] = None,
) -> Iterable[re.Match[str]]:
    """Find commands outside escaped names without changing name spelling."""

    quoted = iter(re.finditer(r"«[^»]*(?:»|\Z)", masked))
    span = next(quoted, None)
    for match in pattern.finditer(masked, 0, len(masked) if end is None else end):
        start = match.start("kind") if "kind" in match.re.groupindex else match.start()
        while span is not None and span.end() <= start:
            span = next(quoted, None)
        if span is None or start < span.start():
            yield match


def _identifier_token_end(masked: str, *, quote_open: bool = False) -> int:
    """End of a name token, including qualified and escaped components.

    The caller supplies an offset-preserving mask so comments cannot become
    part of a name. An unfinished escaped component includes the entire line.
    """

    index = 0
    while index < len(masked):
        if quote_open or masked[index] == "«":
            close = masked.find("»", index if quote_open else index + 1)
            if close < 0:
                return len(masked)
            index = close + 1
            quote_open = False
        else:
            if _IDENT_FIRST_RE.fullmatch(masked[index]) is None:
                return index
            index += 1
            while index < len(masked) and _IDENT_REST_RE.fullmatch(masked[index]):
                index += 1
        if (
            index + 1 >= len(masked)
            or masked[index] != "."
            or (masked[index + 1] != "«" and not _IDENT_FIRST_RE.fullmatch(masked[index + 1]))
        ):
            return index
        index += 1
    return index


@dataclass(frozen=True)
class _HeaderCommand:
    kind: str
    start: int
    end: int
    code_spans: tuple[tuple[int, int], ...]
    module_start: Optional[int] = None
    decorated: bool = False


def _scan_lean_header(source: str) -> tuple[list[_HeaderCommand], int]:
    """Locate header commands using Lean tokens, independently of physical lines.

    Offsets refer to the original source. Comments remain outside code spans,
    including comments between an import keyword and its module. The optional
    quoted module label preserves incomplete editor preambles accepted by the
    existing source consumers.
    """

    masked = _mask_noncode(source, preserve_doc_comments=True)
    commands: list[_HeaderCommand] = []

    def skip(index: int) -> int:
        while index < len(masked) and masked[index].isspace():
            index += 1
        return index

    def word(index: int) -> tuple[str, int]:
        end = index + _identifier_token_end(masked[index:])
        return masked[index:end], end

    index = skip(0)
    while index < len(masked):
        start = index
        token, end = word(index)
        spans = [(index, end)]
        if token in {"module", "prelude"}:
            if token == "module":
                label = end
                while label < len(masked) and masked[label] in " \t\r":
                    label += 1
                if label < len(masked) and masked[label] == "«":
                    end = label + _identifier_token_end(masked[label:])
                    spans.append((label, end))
            commands.append(_HeaderCommand(token, start, end, tuple(spans)))
            index = skip(end)
            continue
        decorated = False
        for modifier in ("public", "meta"):
            if token == modifier:
                decorated = True
                index = skip(end)
                token, end = word(index)
                spans.append((index, end))
        if token != "import":
            return commands, start
        index = skip(end)
        token, end = word(index)
        if token == "all":
            decorated = True
            spans.append((index, end))
            index = skip(end)
            token, end = word(index)
        if not token:
            return commands, start
        spans.append((index, end))
        commands.append(_HeaderCommand("import", start, end, tuple(spans), index, decorated))
        index = skip(end)
    return commands, index


def _quoted_identifier_open_before(masked_lines: list[str], index: int) -> bool:
    """Whether an escaped identifier is still open at the start of ``index``."""

    open_quote = False
    for line in masked_lines[:index]:
        for char in line:
            if open_quote:
                if char == "»":
                    open_quote = False
            elif char == "«":
                open_quote = True
    return open_quote
