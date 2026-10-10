"""Apply answer visibility before paging while retaining exact JSON structure."""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
import re
from typing import Any, Iterator


@dataclass
class _PromptPageText:
    source: str
    visible: str
    tokens: list[re.Match[str]]
    children: list[_PromptPageText]
    isolated: bool = False
    escaped_positions: set[int] = field(default_factory=set)


def _prompt_page_tree(
    content: str, *, isolated_offsets: frozenset[int] = frozenset(), isolated: bool = False,
) -> _PromptPageText:
    from .mini_policy import (
        _GENERATED_SOLUTION_REF_ALIAS_RE, _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
        _provider_safe_chat_message,
    )

    value = None
    if not isolated:
        try:
            value = json.loads(content)
        except (ValueError, RecursionError):
            pass
    if isinstance(value, (dict, list, str)):
        tokens = list(re.finditer(r'"(?:[^"\\]|\\.)*"', content))
        if tokens:
            return _PromptPageText(content, content, tokens, [
                _prompt_page_tree(json.loads(token.group()), isolated=token.start() in isolated_offsets)
                for token in tokens
            ])
    visible = _provider_safe_chat_message({"role": "tool", "content": content})["content"]
    # A page cut can create either word boundary around a generated alias.
    aliases = _GENERATED_SOLUTION_REF_ALIAS_RE.pattern.removeprefix(r"\b").removesuffix(r"\b")
    visible = re.sub(aliases, _OFFICIAL_ANSWER_REFERENCE_HIDDEN, visible)
    return _PromptPageText(content, visible, [], [], isolated=isolated)


def _prompt_page_leaf_visibility(root: _PromptPageText) -> None:
    """Map answer suffixes only to innermost strings, never JSON delimiters."""
    from .mini_policy import _OFFICIAL_ANSWER_REFERENCE_HIDDEN
    from .proof_dossier import (
        _PROMPT_SPLIT_GAP_RE, _SPLIT_IDENTIFIER_PREFIX_RE, _SPLIT_SOLUTION_REF_RE,
        _prompt_security_skeleton_with_index_map,
    )

    pieces: list[str] = []
    spans: list[tuple[int, int, _PromptPageText]] = []
    total = 0

    def append(node: _PromptPageText) -> None:
        nonlocal total
        if not node.tokens:
            spans.append((total, total + len(node.visible), node))
            pieces.append(node.visible)
            total += len(node.visible)
            return
        cursor = 0
        for token, child in zip(node.tokens, node.children):
            prefix = node.source[cursor:token.start()] + '"'
            pieces.append(prefix)
            total += len(prefix)
            append(child)
            pieces.append('"')
            total += 1
            cursor = token.end()
        pieces.append(node.source[cursor:])
        total += len(node.source) - cursor

    append(root)
    skeleton, index_map = _prompt_security_skeleton_with_index_map("".join(pieces))
    # Any page cut can expose a suffix whose prefix is the enclosing tool
    # message's text field. Hide these suffixes before computing page offsets.
    # Reuse the shared suffix syntax, beginning at a literal underscore so
    # punctuation runs cannot cause repeated arbitrary-gap scans.
    _, prefix, suffix = _SPLIT_SOLUTION_REF_RE.pattern.partition(_SPLIT_IDENTIFIER_PREFIX_RE)
    if not prefix or not suffix.startswith(_PROMPT_SPLIT_GAP_RE + "_"):
        raise RuntimeError("answer-reference policy suffix is unavailable")
    pattern = re.compile(suffix.removeprefix(_PROMPT_SPLIT_GAP_RE))
    replacements: dict[int, list[tuple[int, int]]] = {}
    token_index = 0
    for match in pattern.finditer(skeleton):
        start, end = index_map[match.start()], index_map[match.end() - 1] + 1
        while token_index + 1 < len(spans) and spans[token_index][1] <= start:
            token_index += 1
        first_index = token_index
        while token_index + 1 < len(spans) and spans[token_index + 1][0] < end:
            token_index += 1
        participating = [
            (left, node) for left, right, node in spans[first_index:token_index + 1]
            if max(start, left) < min(end, right)
        ]
        if len(participating) > 1 and all(node.isolated for _, node in participating):
            # Separately validated identifiers are independent names. Their
            # JSON separators must not turn adjacent labels into one symbol.
            # Each name has already undergone the ordinary answer policy.
            # Escape one participating character without changing its decoded
            # value, so the final provider filter also preserves the boundary.
            left, node = participating[-1]
            node.escaped_positions.add(max(start, left) - left)
            continue
        left, right, _ = spans[token_index]
        if max(start, left) < min(end, right):
            replacements.setdefault(token_index, []).append((max(start, left) - left, min(end, right) - left))
    for index, ranges in replacements.items():
        node = spans[index][2]
        pieces = []
        cursor = 0
        for start, end in ranges:
            pieces.extend((node.visible[cursor:start], _OFFICIAL_ANSWER_REFERENCE_HIDDEN))
            cursor = end
        pieces.append(node.visible[cursor:])
        node.visible = "".join(pieces)


def _quoted_prompt_string(value: str, escaped_positions: set[int]) -> str:
    if not escaped_positions:
        return json.dumps(value, ensure_ascii=False)
    pieces = ['"']
    cursor = 0
    for index in sorted(escaped_positions):
        pieces.append(json.dumps(value[cursor:index], ensure_ascii=False)[1:-1])
        encoded = value[index].encode("utf-16-be", errors="surrogatepass").hex()
        pieces.extend("\\u" + encoded[start:start + 4] for start in range(0, len(encoded), 4))
        cursor = index + 1
    pieces.extend((json.dumps(value[cursor:], ensure_ascii=False)[1:-1], '"'))
    return "".join(pieces)


def _render_prompt_page_tree(node: _PromptPageText) -> str:
    if not node.tokens:
        return node.visible
    key_end = re.compile(r"\s*:")
    keys = {child.source for token, child in zip(node.tokens, node.children)
            if key_end.match(node.source, token.end())}
    aliases: dict[str, str] = {}
    pieces: list[str] = []
    cursor = 0
    for token, child in zip(node.tokens, node.children):
        visible = _render_prompt_page_tree(child)
        if visible != child.source or child.escaped_positions:
            if key_end.match(node.source, token.end()):
                if child.source not in aliases:
                    base = "answer_key_hidden_" + hashlib.sha256(
                        child.source.encode("utf-8", errors="surrogatepass"),
                    ).hexdigest()
                    alias = base
                    suffix = 2
                    while alias in keys:
                        alias = f"{base}_{suffix}"
                        suffix += 1
                    keys.add(alias)
                    aliases[child.source] = alias
                visible = aliases[child.source]
            replacement = _quoted_prompt_string(visible, child.escaped_positions)
            replacement = replacement.encode("utf-8", errors="backslashreplace").decode()
            pieces.extend((node.source[cursor:token.start()], replacement))
            cursor = token.end()
    pieces.append(node.source[cursor:])
    return "".join(pieces)


def prompt_page_text(content: str, *, redact_solution_refs: bool) -> str:
    """Filter the complete selected text while retaining nested JSON structure."""
    if not redact_solution_refs:
        return content
    tree = _prompt_page_tree(content)
    _prompt_page_leaf_visibility(tree)
    return _render_prompt_page_tree(tree)


def prompt_page_json(
    value: Any, *, redact_solution_refs: bool,
    isolated_string_paths: frozenset[tuple[str | int, ...]] = frozenset(),
) -> str:
    """Serialize structured host data with explicit independent-name boundaries.

    Callers may isolate only separately validated identifier fields. Free text
    and arbitrary research artifacts retain the cross-fragment answer policy.
    No policy bypass metadata is included in the resulting provider content.
    """
    content = json.dumps(value, ensure_ascii=False, allow_nan=False)
    if not redact_solution_refs:
        return content

    def strings(item: Any, path: tuple[str | int, ...]) -> Iterator[bool]:
        if isinstance(item, dict):
            for key, child in item.items():
                if not isinstance(key, str):
                    raise ValueError("prompt JSON keys must be strings")
                yield False
                yield from strings(child, (*path, key))
        elif isinstance(item, list):
            for index, child in enumerate(item):
                yield from strings(child, (*path, index))
        elif isinstance(item, str):
            yield path in isolated_string_paths

    tokens = list(re.finditer(r'"(?:[^"\\]|\\.)*"', content))
    offsets = frozenset(
        token.start() for token, isolate in zip(tokens, strings(value, ()), strict=True) if isolate
    )
    tree = _prompt_page_tree(content, isolated_offsets=offsets)
    _prompt_page_leaf_visibility(tree)
    return _render_prompt_page_tree(tree)
