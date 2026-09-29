"""Stack-independent, lexical operations for conservative contract comparison.

These are comparison keys, not proof certificates. Callers retain their own
domain, assumption, and Lean-evidence checks.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Mapping, Sequence

from .utils import _lean_lexical_skip_end


GROUPS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
IDENTIFIER = re.compile(r"[^\W\d][\w']*", re.UNICODE)
BOUND = re.compile(r"__bound(\d+)__\Z")


def numeric_contract_domains_compatible(left: str, right: str) -> bool:
    """Reject contradictory explicit numeric domains at corresponding terms.

    Cast-insensitive keys remain useful for advisory root adjacency and for
    matching unannotated numerals. Evidence reuse additionally compares the
    positions of explicit annotations: merely comparing sets of types would
    confuse Nat subtraction with Int subtraction when another cast is swapped.
    """
    numeric = re.compile(r"(?:ℚ|Rat|ℝ|Real|ℤ|Int|ℕ|Nat)(?![\w'])")
    aliases = {"ℚ": "Rat", "ℝ": "Real", "ℤ": "Int", "ℕ": "Nat"}

    def profile(text: str) -> tuple[
        tuple[str, ...], dict[tuple[int, int], tuple[str, ...]], set[tuple[int, int]],
    ]:
        tokens: list[str] = []
        starts: list[int] = []
        groups: set[tuple[int, int]] = set()
        annotations: dict[tuple[int, int], list[str]] = {}
        index = 0
        while index < len(text):
            end = _lean_lexical_skip_end(text, index)
            if end is not None:
                if not text.startswith(("/-", "--"), index):
                    tokens.append(text[index:end])
                index = end
                continue
            char = text[index]
            if char == "(":
                starts.append(len(tokens))
            elif char == ")" and starts:
                groups.add((starts.pop(), len(tokens)))
            elif char == ":" and starts:
                cursor = index + 1
                wrappers = 0
                while cursor < len(text) and (text[cursor].isspace() or text[cursor] == "("):
                    wrappers += text[cursor] == "("
                    cursor += 1
                match = numeric.match(text, cursor)
                if match is not None:
                    cursor = match.end()
                    while cursor < len(text) and text[cursor].isspace():
                        cursor += 1
                    while wrappers and cursor < len(text) and text[cursor] == ")":
                        wrappers -= 1
                        cursor += 1
                        while cursor < len(text) and text[cursor].isspace():
                            cursor += 1
                    if not wrappers and text[cursor:cursor + 1] == ")":
                        span = (starts[-1], len(tokens))
                        annotations.setdefault(span, []).append(aliases.get(match[0], match[0]))
                        index = cursor
                        continue
                tokens.append(char)
            elif not char.isspace():
                match = IDENTIFIER.match(text, index)
                if match is None:
                    match = re.compile(r"\d+").match(text, index)
                if match is not None:
                    tokens.append(match[0])
                    index = match.end()
                    continue
                tokens.append(char)
            index += 1
        return tuple(tokens), {span: tuple(types) for span, types in annotations.items()}, groups

    def grouping_safe(
        tokens: tuple[str, ...], annotations: Mapping[tuple[int, int], tuple[str, ...]],
        other_groups: set[tuple[int, int]],
    ) -> bool:
        boundaries = {"=", "≠", "<", ">", "≤", "≥", "→", "↔", "∧", "∨", ","}
        for (start, end) in annotations:
            if (start, end) in other_groups:
                continue
            expression = tokens[start:end]
            if len(expression) == 1 and (IDENTIFIER.fullmatch(expression[0]) or expression[0].isdigit()):
                continue
            # Complete arithmetic comparison operands may lose an outer group,
            # but function arguments and arithmetic subexpressions may not.
            ordinary = all(
                (IDENTIFIER.fullmatch(token) and token not in {"if", "then", "else", "let", "fun", "match"})
                or token.isdigit() or token in {"+", "-", "*", "/", "^", "%", "."}
                for token in expression
            )
            if (ordinary and (start == 0 or tokens[start - 1] in boundaries)
                    and (end == len(tokens) or tokens[end] in boundaries)):
                continue
            return False
        return True

    left_tokens, left_types, left_groups = profile(left)
    right_tokens, right_types, right_groups = profile(right)
    if not left_types and not right_types:
        return True
    if left_tokens != right_tokens:
        return False
    if not grouping_safe(left_tokens, left_types, right_groups) or not grouping_safe(
        right_tokens, right_types, left_groups,
    ):
        return False
    if not left_types or not right_types or left_types == right_types:
        return True
    # Optional annotations are harmless when every explicit domain agrees.
    # With mixed domains, require exact positions: casts on disjoint operands
    # can still constrain the same overloaded arithmetic expression.
    domains = {
        domain
        for annotations in (left_types, right_types)
        for types in annotations.values()
        for domain in types
    }
    return len(domains) == 1


def canonicalize_contract_type_aliases(text: str) -> str:
    """Canonicalize known numeric type notations outside literal contents."""
    aliases = (("ℝ≥0∞", "ENNReal"), ("ℝ≥0", "NNReal"),
               ("ℕ", "Nat"), ("ℤ", "Int"), ("ℝ", "Real"), ("ℚ", "Rat"))
    out: list[str] = []
    index = 0
    while index < len(text):
        end = _lean_lexical_skip_end(text, index)
        if end is not None:
            out.append(text[index:end])
            index = end
            continue
        alias = next(((source, target) for source, target in aliases
                      if text.startswith(source, index)
                      and (index == 0 or not (text[index - 1].isalnum() or text[index - 1] in "_'."))
                      and (index + len(source) == len(text)
                           or not (text[index + len(source)].isalnum() or text[index + len(source)] in "_'"))), None)
        if alias is not None:
            out.append(alias[1])
            index += len(alias[0])
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def compact_contract_surface(text: str) -> str:
    """Discard only insignificant whitespace; preserve literals and tokens."""
    out: list[str] = []
    index = 0
    while index < len(text):
        end = _lean_lexical_skip_end(text, index)
        if end is not None:
            if text.startswith(("/-", "--"), index):
                # Comments, like whitespace, separate identifiers.
                if out and out[-1] != " ":
                    out.append(" ")
            else:
                out.append(text[index:end])
            index = end
            continue
        if not text[index].isspace():
            out.append(text[index])
            index += 1
            continue
        end = index + 1
        while end < len(text) and text[end].isspace():
            end += 1
        if (out and end < len(text)
                and (out[-1][-1].isalnum() or out[-1][-1] in "_'»")
                and (text[end].isalnum() or text[end] in "_'«")):
            out.append(" ")
        index = end
    return "".join(out).strip()


def matching_group(text: str, start: int) -> int:
    """Find a balanced lexical group without descending the Python stack."""
    closer = GROUPS.get(text[start:start + 1])
    if closer is None:
        return -1
    stack = [closer]
    index = start + 1
    while index < len(text):
        end = _lean_lexical_skip_end(text, index)
        if end is not None:
            index = end
            continue
        char = text[index]
        if char in GROUPS:
            stack.append(GROUPS[char])
        elif char in GROUPS.values():
            if char != stack[-1]:
                return -1
            stack.pop()
            if not stack:
                return index
        index += 1
    return -1


def normalize_numeric_contract_casts(
    text: str, *, colon_index: Callable[[str], int],
    strip_parens: Callable[[str], str],
) -> str:
    """Normalize numeric casts with an explicit postorder stack."""
    # Each frame stores text pieces for one parenthesis. Literal contents are
    # opaque, including parentheses and apparent casts inside Lean strings.
    frames: list[list[str]] = [[]]
    index = 0
    while index < len(text):
        end = _lean_lexical_skip_end(text, index)
        if end is not None:
            frames[-1].append(text[index:end])
            index = end
            continue
        char = text[index]
        if char == "(":
            frames.append([])
        elif char == ")" and len(frames) > 1:
            body = "".join(frames.pop())
            colon = colon_index(body)
            expression = body[:colon].strip() if colon >= 0 else ""
            domain = strip_parens(body[colon + 1:].strip()) if colon >= 0 else ""
            if (expression and re.search(r"\d", expression)
                    and domain in {"ℚ", "Rat", "ℝ", "Real", "ℤ", "Int", "ℕ", "Nat"}):
                frames[-1].append(strip_parens(expression))
            else:
                frames[-1].append("(" + body + ")")
        else:
            frames[-1].append(char)
        index += 1
    while len(frames) > 1:
        body = "".join(frames.pop())
        frames[-1].append("(" + body)
    return "".join(frames[0])


def replace_scoped_contract_identifiers(
    text: str, mapping: Mapping[str, str], *,
    binder_groups: Callable[[str], Sequence[str]],
    binder_names: Callable[[str], Sequence[str]],
    comma_index: Callable[[str], int],
    colon_index: Callable[[str], int],
    unwrap_group: Callable[[str], str],
) -> str:
    """Alpha-rename quantified binders in lexical scope, using an explicit stack.

    A binder's type is normalized before introducing its names. Subsequent
    binder groups see preceding groups, never subsequent ones. Scanning groups
    and quantifier bodies uses work items instead of recursive function calls.
    """
    out: list[str] = []
    pending: list[tuple[str, Mapping[str, str] | None]] = [(text, mapping)]
    while pending:
        raw, scope = pending.pop()
        if scope is None:
            out.append(raw)
            continue
        index = 0
        while index < len(raw):
            end = _lean_lexical_skip_end(raw, index)
            if end is not None:
                token = raw[index:end]
                local_identifier = raw.startswith("«", index) and not (
                    index > 0 and raw[index - 1] == "."
                )
                out.append(scope.get(token, token) if local_identifier else token)
                index = end
                continue
            char = raw[index]
            if char in GROUPS:
                end = matching_group(raw, index)
                if end >= 0:
                    out.append(char)
                    pending.extend([(raw[end + 1:], scope), (raw[end], None),
                                    (raw[index + 1:end], scope)])
                    break
            # Filter notations (∀ᶠ, ∃ᶠ, ∀ᵐ) are not ordinary telescopes.
            # Keep unsupported contiguous notation opaque to binder parsing.
            quantifier = re.match(r"(?:[∀∃](?![ᶠᵐ∞])|(?:forall|exists)\b)", raw[index:])
            if quantifier and (index == 0 or not (raw[index - 1].isalnum() or raw[index - 1] in "_'.")):
                tail = index + len(quantifier[0])
                comma = comma_index(raw[tail:])
                if comma >= 0:
                    binder = raw[tail:tail + comma]
                    body = raw[tail + comma + 1:]
                    local = dict(scope)
                    next_index = 1 + max(
                        (int(match[1]) for value in local.values()
                         if (match := BOUND.fullmatch(value))), default=-1,
                    )
                    work: list[tuple[str, Mapping[str, str] | None]] = []
                    for group in binder_groups(binder):
                        group = group.strip()
                        unwrapped = unwrap_group(group)
                        colon = colon_index(unwrapped)
                        # Anonymous instance syntax supplies a class domain,
                        # not names that may shadow that class or its arguments.
                        anonymous_instance = group.startswith("[") and colon < 0
                        names = () if anonymous_instance else binder_names(group)
                        previous = local
                        local = dict(local)
                        for name in names:
                            local[name] = f"__bound{next_index}__"
                            next_index += 1
                        if work:
                            work.append((" ", None))
                        if colon >= 0 and names:
                            opener = group[0] if group[0] in "[{⦃" else "("
                            work.extend([
                                (opener + " ".join(local[name] for name in names) + ":", None),
                                (unwrapped[colon + 1:], previous),
                                (GROUPS[opener], None),
                            ])
                        else:
                            work.append((group, local))
                    out.append(quantifier[0])
                    work.extend([(",", None), (body, local)])
                    pending.extend(reversed(work))
                    break
            match = IDENTIFIER.match(raw, index)
            if match is not None:
                token = match[0]
                # A namespace suffix is not an occurrence of a local binder.
                qualified = index > 0 and raw[index - 1] == "."
                if not qualified and token in scope:
                    out.append(scope[token])
                elif BOUND.fullmatch(token):
                    out.append("\0mini-alpha-free-identifier:" + token + "\0")
                else:
                    out.append(token)
                index = match.end()
                continue
            out.append(char)
            index += 1
    return "".join(out)
