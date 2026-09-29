"""Offset-preserving Lean lexical masks shared by source consumers."""

from __future__ import annotations

import re
from typing import Iterable, Optional


_RAW_STRING_START_RE = re.compile(r'r(?P<hashes>#+)?"')


def _mask_noncode(text: str, *, mask_quoted_identifiers: bool = False) -> str:
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
            mask(i, end)
            i = end
            continue
        raw_match = _RAW_STRING_START_RE.match(src, i) if src[i] == "r" else None
        if raw_match is not None and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_")):
            hashes = raw_match.group("hashes") or ""
            close = '"' + hashes
            body_start = raw_match.end()
            close_at = src.find(close, body_start)
            end = n if close_at < 0 else close_at + len(close)
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
                    close = '"' + hashes
                    body_start = raw_match.end()
                    close_at = src.find(close, body_start)
                    end = n if close_at < 0 else close_at + len(close)
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


def _physical_source_lines(text: str) -> list[str]:
    """Split on ``\\n`` and ``\\r\\n`` only.

    ``str.splitlines()`` also splits Unicode separators that Lean keeps inside
    an escaped identifier or a ``--`` comment. A trailing newline is dropped,
    and a CR that belongs to CRLF is dropped with that newline.
    """

    source = str(text or "")
    if source == "":
        return []
    if source.endswith("\n"):
        source = source[:-1]
    return [line[:-1] if line.endswith("\r") else line for line in source.split("\n")]


def _unclosed_block_comment_at(line: str, *, quote_open: bool = False) -> Optional[int]:
    """Index of a ``/-`` that is still open at the end of one physical line.

    ``quote_open`` means this line begins inside an escaped identifier, so
    characters before its ``»`` cannot start a comment.
    """

    index = 0
    limit = len(line)
    depth = 0
    start: Optional[int] = None
    while index < limit:
        if quote_open:
            if line[index] == "»":
                quote_open = False
            index += 1
            continue
        if line[index] == "'" and (
            index == 0 or not (line[index - 1].isalnum() or line[index - 1] in "_'")
        ):
            end = index + 1
            if end < limit and line[end] == "\\":
                end += 2
            else:
                end += 1
            if end < limit and line[end] == "'":
                index = end + 1
                continue
        if line.startswith("«", index):
            quote_open = True
            index += 1
            continue
        if line.startswith("--", index):
            break
        if line.startswith("/-", index):
            if depth == 0:
                start = index
            depth += 1
            index += 2
            continue
        if line.startswith("-/", index) and depth:
            depth -= 1
            if depth == 0:
                start = None
            index += 2
            continue
        if line[index] == '"':
            index += 1
            while index < limit:
                if line[index] == "\\":
                    index += 2
                    continue
                if line[index] == '"':
                    index += 1
                    break
                index += 1
            continue
        index += 1
    if depth == 0:
        return None
    return start


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
