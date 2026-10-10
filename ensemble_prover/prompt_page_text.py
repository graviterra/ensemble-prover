"""Apply answer visibility before paging while retaining exact JSON structure."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re


@dataclass
class _PromptPageText:
    source: str
    visible: str
    tokens: list[re.Match[str]]
    children: list[_PromptPageText]


def _prompt_page_tree(content: str) -> _PromptPageText:
    from .mini_policy import (
        _GENERATED_SOLUTION_REF_ALIAS_RE, _OFFICIAL_ANSWER_REFERENCE_HIDDEN,
        _provider_safe_chat_message,
    )

    try:
        value = json.loads(content)
    except (ValueError, RecursionError):
        value = None
    if isinstance(value, (dict, list, str)):
        tokens = list(re.finditer(r'"(?:[^"\\]|\\.)*"', content))
        if tokens:
            return _PromptPageText(content, content, tokens, [
                _prompt_page_tree(json.loads(token.group())) for token in tokens
            ])
    visible = _provider_safe_chat_message({"role": "tool", "content": content})["content"]
    # A page cut can create either word boundary around a generated alias.
    aliases = _GENERATED_SOLUTION_REF_ALIAS_RE.pattern.removeprefix(r"\b").removesuffix(r"\b")
    visible = re.sub(aliases, _OFFICIAL_ANSWER_REFERENCE_HIDDEN, visible)
    return _PromptPageText(content, visible, [], [])


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
        while token_index + 1 < len(spans) and spans[token_index + 1][0] < end:
            token_index += 1
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


def _render_prompt_page_tree(node: _PromptPageText) -> str:
    if not node.tokens:
        return node.visible
    key_end = re.compile(r"\s*:")
    keys = {child.source for token, child in zip(node.tokens, node.children)
            if key_end.match(node.source, token.end())}
    aliases: dict[str, str] = {}
    pieces = []
    cursor = 0
    for token, child in zip(node.tokens, node.children):
        visible = _render_prompt_page_tree(child)
        if visible != child.source:
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
            replacement = json.dumps(visible, ensure_ascii=False)
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
