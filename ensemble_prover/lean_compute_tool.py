"""Answer-safe Lean computation/exploration tool for mini prover."""

from __future__ import annotations

import inspect
import re
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any, Callable, Dict, Mapping, Optional

from .proof_dossier import (
    _contains_solution_ref_for_prompt,
    _prompt_safe_lean_diagnostic_text,
    _strip_lean_comments_for_prompt,
)
from .mini_deadline_transaction import DeadlineMutationTransaction
from .utils import (
    _canonicalize_big_operator_binders,
    _lean_lexical_skip_end,
    extract_code_fences,
    has_sorry_or_admit,
)


COMPUTE_EXAMPLES_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "compute_examples",
        "description": (
            "OBSERVATION tool. Use Lean to compute small examples, reductions, "
            "or type observations before choosing a proof strategy. This is "
            "not proof evidence and cannot close goals or bank helpers. Pass "
            "bounded pure expressions or one-line #eval/#reduce/#check commands; "
            "do not use declarations, imports, IO, files, processes, axioms, "
            "or proof stubs."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "queries": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "Small Lean expressions or one-line #eval/#reduce/#check "
                        "commands to run. Expressions are wrapped using mode."
                    ),
                },
                "mode": {
                    "type": "string",
                    "enum": ["eval", "reduce", "check"],
                    "description": (
                        "Wrapper for expression-only queries (default: eval)."
                    ),
                },
                "purpose": {
                    "type": "string",
                    "description": "Short reason for the computation.",
                },
            },
            "required": ["queries"],
        },
    },
}


_COMMAND_RE = re.compile(r"^\s*#(eval|reduce|check)(?:\s+|$)(.*)$", re.DOTALL)
_LEAN_IDENT_RE = re.compile(r"(?:[^\W\d]|_)[\w']*", flags=re.UNICODE)
_LEAN_DOTTED_IDENT_PATTERN = (
    r"(?:«[^»]+»|(?:[^\W\d]|_)[\w']*)"
    r"(?:\.(?:«[^»]+»|(?:[^\W\d]|_)[\w']*))*"
)
_SAFE_CHECK_EXPR_RE = re.compile(
    r"^@?[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_BARE_BINDER_RE = _LEAN_IDENT_RE
_GROUP_CLOSERS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
_PREAMBLE_DECL_HEADS = (
    "abbrev",
    "axiom",
    "class",
    "constant",
    "def",
    "elab",
    "example",
    "inductive",
    "initialize",
    "instance",
    "lemma",
    "macro",
    "macro_rules",
    "notation",
    "opaque",
    "structure",
    "syntax",
    "theorem",
    "variable",
    "variables",
)
_PREAMBLE_DECL_BOUNDARY_HEADS = _PREAMBLE_DECL_HEADS + (
    "end",
    "import",
    "namespace",
    "open",
    "section",
    "set_option",
    "universe",
)
_PREAMBLE_MODIFIER_RE = (
    r"(?:(?:local|scoped|private|protected|noncomputable|unsafe|partial)\s+)*"
)
_PREAMBLE_DECL_RE = re.compile(
    r"(?ms)^\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    + _PREAMBLE_MODIFIER_RE
    + r"(?P<kind>"
    + "|".join(_PREAMBLE_DECL_HEADS)
    + r")\b"
    r"(?P<tail>.*?)(?=^\s*(?:@\[[^\]]*\]\s*)*"
    + _PREAMBLE_MODIFIER_RE
    + r"(?:"
    + "|".join(_PREAMBLE_DECL_BOUNDARY_HEADS)
    + r")\b|\Z)",
    flags=re.UNICODE,
)
_PREAMBLE_DECL_NAME_RE = re.compile(
    r"^\s*(?P<name>«[^»]+»|(?:[^\W\d]|_)[\w'.]*)(?P<signature>.*)\Z",
    flags=re.UNICODE | re.DOTALL,
)
_PREAMBLE_NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+(" + _LEAN_DOTTED_IDENT_PATTERN + r")\s*$",
    flags=re.UNICODE,
)
_PREAMBLE_END_RE = re.compile(
    r"^\s*end(?:\s+" + _LEAN_DOTTED_IDENT_PATTERN + r")?\s*$",
    flags=re.UNICODE,
)
_PREAMBLE_OPEN_RE = re.compile(
    r"^\s*open(?:\s+scoped)?\s+(?P<names>.+?)\s*$",
    flags=re.UNICODE,
)
_PREAMBLE_INERT_SOLUTION_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    + _PREAMBLE_MODIFIER_RE
    + r"(?P<kind>axiom|constant)\s+"
    r"(?P<name>«[^»]+»|(?:[^\W\d]|_)[\w'.]*)"
    r"(?P<rest>.*)\Z",
    flags=re.UNICODE,
)
_PREAMBLE_NOTATION_ALIAS_RE = re.compile(
    r"^\s*(?::[^\s\"“”]+)?\s*(?:\([^)]*\)\s*)?"
    r"[\"“”](?P<name>[^\"“”]+)[\"“”]\s*=>\s*(?P<body>.+)\Z",
    flags=re.UNICODE | re.DOTALL,
)
_PREAMBLE_MACRO_ALIAS_RE = re.compile(
    r"`\(\s*(?P<name>" + _LEAN_DOTTED_IDENT_PATTERN + r")\s*\)\s*=>\s*"
    r"`\(\s*(?P<body>[^\n]*)\)",
    flags=re.UNICODE,
)
_PREAMBLE_MACRO_DECL_ALIAS_RE = re.compile(
    r"^\s*(?:\([^)]*\)\s*)*[\"“”](?P<name>[^\"“”]+)[\"“”]\s*:\s*term\s*=>\s*"
    r"`\(\s*(?P<body>[^\n]*)\)",
    flags=re.UNICODE | re.DOTALL,
)
_PREAMBLE_ATTRIBUTE_RE = re.compile(r"@\[(?P<body>[^\]]*)\]", re.DOTALL)
_PREAMBLE_IMPLEMENTED_BY_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])implemented_by\s+(?P<name>"
    + _LEAN_DOTTED_IDENT_PATTERN
    + r")",
    flags=re.UNICODE,
)
_PREAMBLE_NATIVE_IMPLEMENTATION_ATTRS = frozenset({"extern", "builtin"})
_PROPOSITION_TYPE_MARKERS = {
    "<",
    "<=",
    "->",
    "=",
    ">",
    ">=",
    "∀",
    "∃",
    "¬",
    "∧",
    "∨",
    "≠",
    "≤",
    "≥",
    "→",
    "↔",
}
_FORBIDDEN_IDENTIFIERS = {
    "abbrev",
    "axiom",
    "class",
    "constant",
    "def",
    "deriving",
    "elab",
    "example",
    "export",
    "import",
    "include",
    "inductive",
    "initialize",
    "instance",
    "lemma",
    "local",
    "macro",
    "namespace",
    "notation",
    "opaque",
    "open",
    "section",
    "set_option",
    "structure",
    "syntax",
    "theorem",
    "universe",
    "unsafe",
    "variable",
    "variables",
}
_FORBIDDEN_EFFECT_IDENTIFIERS = {
    "BaseIO",
    "dbgTrace",
    "EIO",
    "FilePath",
    "IO",
    "IO_FS",
    "IO_Process",
    "Process",
    "System",
    "include_str",
    "run_cmd",
    "unsafeCast",
}
_FORBIDDEN_PROOF_IDENTIFIERS = {
    "aesop",
    "apply",
    "assumption",
    "by",
    "calc",
    "cases",
    "constructor",
    "exact",
    "Eq",
    "False",
    "have",
    "induction",
    "intro",
    "intros",
    "Iff",
    "linarith",
    "norm_num",
    "omega",
    "refine",
    "refl",
    "rfl",
    "ring",
    "rw",
    "show",
    "simp",
    "simpa",
    "Prop",
    "Sort",
    "suffices",
    "trivial",
    "True",
    "Type",
}
_PROOF_LIKE_TYPE_HEADS = {
    "Even",
    "Odd",
    "Nat.Prime",
    "Prime",
}
_MAX_QUERIES = 8
_MAX_QUERY_CHARS = 320
_MAX_TOTAL_CHARS = 1800
_DEFAULT_TIMEOUT_S = 30.0
_MAX_TIMEOUT_S = 45.0
_DEFAULT_MAX_HEARTBEATS = 200000


@dataclass(frozen=True)
class _PreparedQuery:
    index: int
    command: str
    mode: str
    expression: str


def _strip_fence(src: str) -> str:
    text = str(src or "").strip()
    blocks = extract_code_fences(text)
    if blocks:
        return blocks[0].strip()
    return text


def _queries_from_args(args: Mapping[str, Any]) -> tuple[list[str], str]:
    raw_queries = args.get("queries")
    if raw_queries is None and "query" in args:
        raw_queries = [args.get("query")]
    if raw_queries is None and "code" in args:
        raw_queries = [args.get("code")]
    if isinstance(raw_queries, str):
        raw_queries = [raw_queries]
    if not isinstance(raw_queries, Sequence):
        return [], "queries must be an array of strings"
    queries = []
    for item in raw_queries:
        if not isinstance(item, str):
            return [], "each query must be a string"
        text = _strip_fence(item)
        if text:
            queries.append(text)
    return queries, ""


def _interpolated_string_code(source: str, start: int) -> tuple[int, str]:
    """Return an interpolated string's end and executable interpolation text."""

    index = start + 3  # ``s!\"``
    fragments: list[str] = []
    while index < len(source):
        if source[index] == "\\":
            index += 2
            continue
        if source[index] == '"':
            return index + 1, " ".join(fragments)
        if source.startswith("{{", index) or source.startswith("}}", index):
            index += 2
            continue
        if source[index] != "{":
            index += 1
            continue
        expression_start = index + 1
        cursor = expression_start
        depth = 1
        while cursor < len(source):
            if source.startswith(('s!"', 'm!"'), cursor):
                nested_end, _nested_code = _interpolated_string_code(source, cursor)
                cursor = max(cursor + 1, nested_end)
                continue
            skip_to = _lean_lexical_skip_end(source, cursor)
            if skip_to is not None and source[cursor] != "«":
                cursor = max(cursor + 1, skip_to)
                continue
            if source[cursor] == "{":
                depth += 1
            elif source[cursor] == "}":
                depth -= 1
                if depth == 0:
                    fragments.append(source[expression_start:cursor])
                    index = cursor + 1
                    break
            cursor += 1
        else:
            # Malformed interpolation is rejected by Lean, but retain its tail
            # as executable text so safety checks still fail closed.
            fragments.append(source[expression_start:])
            return len(source), " ".join(fragments)
    return len(source), " ".join(fragments)


def _lean_executable_text(text: str) -> str:
    """Project Lean source onto executable tokens, preserving interpolations."""

    source = str(text or "")
    out: list[str] = []
    index = 0
    while index < len(source):
        if source.startswith(('s!"', 'm!"'), index):
            end, interpolation_code = _interpolated_string_code(source, index)
            out.append(" ")
            out.append(_lean_executable_text(interpolation_code))
            out.append(" ")
            index = max(index + 1, end)
            continue
        skip_to = _lean_lexical_skip_end(source, index)
        if skip_to is not None:
            if source[index] == "«":
                # Quoted identifiers are executable names, not inert strings.
                out.append(source[index:skip_to])
            else:
                out.append("\n" if "\n" in source[index:skip_to] else " ")
            index = max(index + 1, skip_to)
            continue
        out.append(source[index])
        index += 1
    return "".join(out)


def _identifier_tokens(text: str) -> set[str]:
    return {
        match.group(0)
        for match in _LEAN_IDENT_RE.finditer(_lean_executable_text(text))
    }


def _first_forbidden_identifier(text: str) -> str:
    tokens = _identifier_tokens(text)
    for item in sorted(
        _FORBIDDEN_IDENTIFIERS
        | _FORBIDDEN_EFFECT_IDENTIFIERS
        | _FORBIDDEN_PROOF_IDENTIFIERS
    ):
        if item in tokens:
            return item
    dotted = _lean_executable_text(text).replace(".", "_")
    tokens = _identifier_tokens(dotted)
    for item in sorted(_FORBIDDEN_EFFECT_IDENTIFIERS):
        if item in tokens:
            return item
    return ""


def _lambda_binder_spans(text: str) -> list[str]:
    source = str(text or "")
    return [source[start:end] for start, end in _lambda_binder_span_ranges(source)]


def _lambda_binder_span_ranges(text: str) -> list[tuple[int, int]]:
    source = str(text or "")
    ranges: list[tuple[int, int]] = []
    index = 0
    while index < len(source):
        marker_end = -1
        if source[index] == "λ":
            marker_end = index + 1
        elif source.startswith("fun", index):
            before = source[index - 1] if index > 0 else ""
            after = source[index + 3] if index + 3 < len(source) else ""
            if (not (before.isalnum() or before == "_")) and not (
                after.isalnum() or after == "_"
            ):
                marker_end = index + 3
        if marker_end < 0:
            index += 1
            continue
        closers: list[str] = []
        cursor = marker_end
        while cursor < len(source):
            ch = source[cursor]
            if ch in _GROUP_CLOSERS:
                closers.append(_GROUP_CLOSERS[ch])
            elif closers and ch == closers[-1]:
                closers.pop()
            elif (
                not closers
                and cursor + 1 < len(source)
                and ch == "="
                and source[cursor + 1] == ">"
            ):
                ranges.append((marker_end, cursor))
                index = cursor + 2
                break
            elif not closers and ch == "↦":
                ranges.append((marker_end, cursor))
                index = cursor + 1
                break
            cursor += 1
        else:
            index = marker_end
    return ranges


def _match_grouped_binder(text: str, start: int) -> tuple[list[str], str, int] | None:
    source = str(text or "")
    if start >= len(source) or source[start] not in _GROUP_CLOSERS:
        return None
    closers = [_GROUP_CLOSERS[source[start]]]
    cursor = start
    cursor += 1
    while cursor < len(source):
        ch = source[cursor]
        if ch in _GROUP_CLOSERS:
            closers.append(_GROUP_CLOSERS[ch])
        elif closers and ch == closers[-1]:
            closers.pop()
            if not closers:
                inside = source[start + 1 : cursor].strip()
                colon = inside.find(":")
                names_text = inside[:colon] if colon >= 0 else inside
                names = [
                    match.group(0)
                    for match in _LEAN_IDENT_RE.finditer(names_text)
                ]
                if not names:
                    return None
                type_text = inside[colon + 1 :] if colon >= 0 else ""
                return names, type_text, cursor + 1
        cursor += 1
    return None


def _type_text_for_guard(text: str) -> str:
    source = str(text or "")
    out: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
            if depth == 1 and (not out or out[-1] != " "):
                out.append(" ")
            continue
        if depth:
            if source.startswith("-/", index):
                depth -= 1
                index += 2
                if depth == 0 and (not out or out[-1] != " "):
                    out.append(" ")
                continue
            index += 1
            continue
        out.append(source[index])
        index += 1
    return " ".join("".join(out).split())


def _strip_wrapping_type_parens(text: str) -> str:
    source = _type_text_for_guard(text)
    while source.startswith("(") and source.endswith(")"):
        depth = 0
        wraps = True
        for index, ch in enumerate(source):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and index != len(source) - 1:
                    wraps = False
                    break
                if depth < 0:
                    wraps = False
                    break
        if not wraps or depth != 0:
            break
        source = _type_text_for_guard(source[1:-1])
    return source


def _type_text_is_proof_like(text: str) -> bool:
    source = _strip_wrapping_type_parens(text)
    if not source.strip():
        return False
    if any(marker in source for marker in _PROPOSITION_TYPE_MARKERS):
        return True
    dotted_tokens = {
        match.group(0)
        for match in re.finditer(_LEAN_DOTTED_IDENT_PATTERN, source, flags=re.UNICODE)
    }
    if dotted_tokens.intersection(_PROOF_LIKE_TYPE_HEADS):
        return True
    return bool(_identifier_tokens(source).intersection(_FORBIDDEN_PROOF_IDENTIFIERS))


def _type_text_matches_proof_alias(text: str, proof_aliases: set[str]) -> bool:
    source = _strip_wrapping_type_parens(text)
    if not source:
        return False
    if source in proof_aliases:
        return True
    first_match = re.search(_LEAN_DOTTED_IDENT_PATTERN, source, flags=re.UNICODE)
    first_token = first_match.group(0) if first_match else ""
    if first_token in proof_aliases:
        return True
    parts = [part for part in source.split(".") if part]
    for index in range(1, len(parts)):
        if ".".join(parts[:index]) in proof_aliases:
            return True
    return False


def _expression_references_proof_alias(text: str, proof_aliases: set[str]) -> bool:
    if not proof_aliases:
        return False
    source = _type_text_for_guard(_lean_executable_text(text))
    tokens = _identifier_tokens(source)
    dotted_tokens = {
        match.group(0)
        for match in re.finditer(_LEAN_DOTTED_IDENT_PATTERN, source, flags=re.UNICODE)
    }
    for alias in proof_aliases:
        item = _strip_wrapping_type_parens(alias)
        if not item:
            continue
        if item in tokens or item in dotted_tokens:
            return True
        if "." in item and re.search(
            rf"(?<![\w'.]){re.escape(item)}(?![\w'.])",
            source,
            flags=re.UNICODE,
        ):
            return True
        if not _LEAN_IDENT_RE.fullmatch(item) and item in source:
            return True
    return False


def _expression_references_alias(text: str, aliases: set[str]) -> bool:
    """Lexically test an expression for one declaration alias."""

    return _expression_references_proof_alias(text, aliases)


def _type_ascription_type_text(source: str, start: int) -> str:
    text = str(source or "")
    closers: list[str] = []
    out: list[str] = []
    cursor = max(0, int(start or 0))
    stop_closers = set(_GROUP_CLOSERS.values())
    while cursor < len(text):
        ch = text[cursor]
        if ch in _GROUP_CLOSERS:
            closers.append(_GROUP_CLOSERS[ch])
            out.append(ch)
        elif closers and ch == closers[-1]:
            closers.pop()
            out.append(ch)
        elif not closers and ch in stop_closers.union({","}):
            break
        else:
            out.append(ch)
        cursor += 1
    return "".join(out)


def _decl_signature_type_and_body(signature: str) -> tuple[str, str]:
    source = str(signature or "")
    assign = source.find(":=")
    where_match = re.search(r"\bwhere\b", source)
    body_start = len(source)
    if assign >= 0:
        body_start = min(body_start, assign)
    if where_match is not None:
        body_start = min(body_start, where_match.start())
    header = source[:body_start]
    body = source[body_start:]
    type_text = ""
    colon = header.rfind(":")
    if colon >= 0:
        type_text = header[colon + 1 :].strip()
    return type_text, body


def _decl_tail_name_and_signature(kind: str, tail: str) -> tuple[str, str]:
    if str(kind or "") in {"elab", "example", "initialize", "instance", "macro", "notation", "syntax"}:
        return "", str(tail or "")
    match = _PREAMBLE_DECL_NAME_RE.match(str(tail or ""))
    if not match:
        return "", str(tail or "")
    return str(match.group("name") or "").strip(), str(match.group("signature") or "")


def _namespace_prefix_at(source: str, position: int) -> str:
    stack: list[str] = []
    for line in str(source or "")[: max(0, position)].splitlines():
        namespace_match = _PREAMBLE_NAMESPACE_RE.match(line)
        if namespace_match:
            stack.append(namespace_match.group(1))
            continue
        if _PREAMBLE_END_RE.match(line) and stack:
            stack.pop()
    return ".".join(item for item in stack if item)


def _decl_alias_names(name: str, namespace_prefix: str) -> set[str]:
    raw = str(name or "").strip()
    if not raw:
        return set()
    names = {raw}
    prefix = str(namespace_prefix or "").strip(".")
    if prefix and not raw.startswith(prefix + "."):
        names.add(f"{prefix}.{raw}")
    return names


def _open_namespace_prefixes_at(source: str, position: int) -> list[str]:
    prefixes: list[str] = []
    seen: set[str] = set()
    for line in str(source or "")[: max(0, position)].splitlines():
        match = _PREAMBLE_OPEN_RE.match(line)
        if not match:
            continue
        for item in re.finditer(_LEAN_DOTTED_IDENT_PATTERN, match.group("names")):
            name = str(item.group(0) or "").strip(".")
            if name and name not in seen:
                seen.add(name)
                prefixes.append(name)
    return prefixes


def _body_resolution_prefixes(
    source: str,
    position: int,
    namespace_prefix: str,
) -> list[str]:
    prefixes: list[str] = []
    seen: set[str] = set()
    for raw in [namespace_prefix, *_open_namespace_prefixes_at(source, position)]:
        prefix = str(raw or "").strip(".")
        if prefix and prefix not in seen:
            seen.add(prefix)
            prefixes.append(prefix)
    return prefixes


def _expand_namespace_body_aliases(text: str, prefixes: str | Sequence[str]) -> str:
    source = str(text or "")
    raw_prefixes = (
        [prefixes]
        if isinstance(prefixes, str)
        else list(prefixes or ())
    )
    clean_prefixes = [
        str(item or "").strip(".") for item in raw_prefixes if str(item or "").strip(".")
    ]
    additions: list[str] = []
    if clean_prefixes:
        for token in re.finditer(_LEAN_DOTTED_IDENT_PATTERN, source, flags=re.UNICODE):
            item = str(token.group(0) or "").strip()
            if item and "." not in item:
                additions.extend(f"{prefix}.{item}" for prefix in clean_prefixes)
    for match in re.finditer(
        r"\bopen\s+(?:scoped\s+)?(?P<ns>"
        + _LEAN_DOTTED_IDENT_PATTERN
        + r")\s+in\s+(?P<body>[^,\n;)]*)",
        source,
        flags=re.UNICODE,
    ):
        prefix = str(match.group("ns") or "").strip(".")
        body = str(match.group("body") or "")
        if not prefix:
            continue
        for token in re.finditer(_LEAN_DOTTED_IDENT_PATTERN, body, flags=re.UNICODE):
            item = str(token.group(0) or "").strip()
            if item and "." not in item:
                additions.append(f"{prefix}.{item}")
    if not additions:
        return source
    return source + " " + " ".join(additions)


def _decl_body_value_text(body: str) -> str:
    source = str(body or "")
    if ":=" in source:
        return source.split(":=", 1)[1]
    where_match = re.search(r"\bwhere\b", source)
    if where_match is not None:
        return source[where_match.end() :]
    return ""


def _line_is_inert_solution_decl(line: str) -> bool:
    match = _PREAMBLE_INERT_SOLUTION_DECL_RE.match(str(line or ""))
    if not match:
        return False
    name = str(match.group("name") or "")
    rest = str(match.group("rest") or "")
    if not _contains_solution_ref_for_prompt(name):
        return False
    if _contains_solution_ref_for_prompt(rest):
        return False
    return ":=" not in rest and not re.search(r"\bwhere\b", rest)


def _decl_materializes_solution_ref(
    *,
    kind: str,
    names: set[str],
    text: str,
    signature: str,
) -> bool:
    official_name = any(_contains_solution_ref_for_prompt(name) for name in names)
    if official_name:
        _type_text, body = _decl_signature_type_and_body(signature)
        body_value = _decl_body_value_text(body)
        if str(kind or "") in {"axiom", "constant"} and not body_value:
            return False
        return True
    return _contains_solution_ref_for_prompt(text)


def _preamble_materializes_solution_ref(preamble: str) -> bool:
    source = _strip_lean_comments_for_prompt(str(preamble or ""))
    direct_solution_ref = _contains_solution_ref_for_prompt(source)
    for match in _PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        namespace_prefix = _namespace_prefix_at(source, match.start())
        body_prefixes = _body_resolution_prefixes(
            source,
            match.start(),
            namespace_prefix,
        )
        name, signature = _decl_tail_name_and_signature(kind, tail)
        names = _decl_alias_names(name, namespace_prefix)
        expanded_text = _expand_namespace_body_aliases(
            str(match.group(0) or ""),
            body_prefixes,
        )
        if _decl_materializes_solution_ref(
            kind=kind,
            names=names,
            text=expanded_text,
            signature=signature,
        ):
            return True
    if not direct_solution_ref:
        return False
    for line in source.splitlines():
        if _contains_solution_ref_for_prompt(line) and not _line_is_inert_solution_decl(
            line
        ):
            return True
    return False


def _preamble_solution_ref_aliases(preamble: str) -> set[str]:
    source = _strip_lean_comments_for_prompt(str(preamble or ""))
    aliases: set[str] = set()
    for match in _PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        if kind not in {"axiom", "constant"}:
            continue
        namespace_prefix = _namespace_prefix_at(source, match.start())
        name, _signature = _decl_tail_name_and_signature(kind, tail)
        names = _decl_alias_names(name, namespace_prefix)
        official_names = {
            item for item in names if _contains_solution_ref_for_prompt(item)
        }
        for item in official_names:
            aliases.add(item)
            short = item.rsplit(".", 1)[-1].strip()
            if short:
                aliases.add(short)
    return aliases


def _variable_alias_declarations(
    tail: str,
    namespace_prefix: str,
) -> list[tuple[set[str], str, str]]:
    declarations: list[tuple[set[str], str, str]] = []
    source = str(tail or "")
    cursor = 0
    while cursor < len(source):
        group = _match_grouped_binder(source, cursor)
        if group:
            names, type_text, end = group
            for name in names:
                aliases = _decl_alias_names(name, namespace_prefix)
                if aliases:
                    declarations.append((aliases, type_text, ""))
            cursor = end
            continue
        cursor += 1
    return declarations


def _notation_alias_declaration(
    tail: str,
    namespace_prefix: str,
) -> tuple[set[str], str, str] | None:
    match = _PREAMBLE_NOTATION_ALIAS_RE.match(str(tail or ""))
    if not match:
        return None
    name = str(match.group("name") or "").strip()
    aliases = _decl_alias_names(name, namespace_prefix)
    if not aliases:
        return None
    return aliases, "", str(match.group("body") or "")


def _macro_alias_declarations(
    text: str,
    namespace_prefix: str,
) -> list[tuple[set[str], str, str]]:
    declarations: list[tuple[set[str], str, str]] = []
    for match in _PREAMBLE_MACRO_ALIAS_RE.finditer(str(text or "")):
        aliases = _decl_alias_names(str(match.group("name") or ""), namespace_prefix)
        if aliases:
            declarations.append((aliases, "", str(match.group("body") or "")))
    for match in _PREAMBLE_MACRO_DECL_ALIAS_RE.finditer(str(text or "")):
        aliases = _decl_alias_names(str(match.group("name") or ""), namespace_prefix)
        if aliases:
            declarations.append((aliases, "", str(match.group("body") or "")))
    return declarations


def _preamble_proof_type_aliases(preamble: str) -> set[str]:
    source = _strip_lean_comments_for_prompt(str(preamble or ""))
    declarations: list[tuple[set[str], str, str]] = []
    alias_kinds = {
        "abbrev",
        "axiom",
        "class",
        "constant",
        "def",
        "lemma",
        "opaque",
        "structure",
        "theorem",
    }
    for match in _PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        namespace_prefix = _namespace_prefix_at(source, match.start())
        body_prefixes = _body_resolution_prefixes(
            source,
            match.start(),
            namespace_prefix,
        )
        if kind in {"variable", "variables"}:
            declarations.extend(_variable_alias_declarations(tail, namespace_prefix))
            continue
        if kind == "notation":
            item = _notation_alias_declaration(tail, namespace_prefix)
            if item is not None:
                names, type_text, body = item
                declarations.append(
                    (names, type_text, _expand_namespace_body_aliases(body, body_prefixes))
                )
            continue
        if kind == "macro_rules":
            declarations.extend(
                (
                    names,
                    type_text,
                    _expand_namespace_body_aliases(body, body_prefixes),
                )
                for names, type_text, body in _macro_alias_declarations(tail, namespace_prefix)
            )
            continue
        if kind == "macro":
            declarations.extend(
                (
                    names,
                    type_text,
                    _expand_namespace_body_aliases(body, body_prefixes),
                )
                for names, type_text, body in _macro_alias_declarations(tail, namespace_prefix)
            )
            continue
        if kind not in alias_kinds:
            continue
        name, signature = _decl_tail_name_and_signature(
            kind,
            tail,
        )
        names = _decl_alias_names(name, namespace_prefix)
        if not names:
            continue
        type_text, body = _decl_signature_type_and_body(signature)
        declarations.append((names, type_text, _decl_body_value_text(body)))
    aliases: set[str] = set()
    changed = True
    while changed:
        changed = False
        for names, type_text, body_value in declarations:
            if names.issubset(aliases):
                continue
            if (
                _type_text_is_proof_like(type_text)
                or _type_text_matches_proof_alias(type_text, aliases)
                or _type_text_is_proof_like(body_value)
                or _type_text_matches_proof_alias(body_value, aliases)
            ):
                before = len(aliases)
                aliases.update(names)
                changed = changed or len(aliases) != before
    return aliases


def _preamble_effect_aliases(preamble: str) -> set[str]:
    """Return preamble names whose type/body transitively exposes effects."""

    source = _strip_lean_comments_for_prompt(str(preamble or ""))
    declarations: list[
        tuple[set[str], str, str, bool, set[str], bool]
    ] = []
    alias_kinds = {
        "abbrev",
        "axiom",
        "class",
        "constant",
        "def",
        "opaque",
        "structure",
    }
    for match in _PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        namespace_prefix = _namespace_prefix_at(source, match.start())
        body_prefixes = _body_resolution_prefixes(
            source,
            match.start(),
            namespace_prefix,
        )
        if kind in {"variable", "variables"}:
            declarations.extend(
                (names, type_text, "", False, set(), False)
                for names, type_text, _body in _variable_alias_declarations(
                    tail,
                    namespace_prefix,
                )
            )
            continue
        if kind == "notation":
            item = _notation_alias_declaration(tail, namespace_prefix)
            if item is not None:
                names, type_text, body = item
                declarations.append(
                    (
                        names,
                        type_text,
                        _expand_namespace_body_aliases(body, body_prefixes),
                        False,
                        set(),
                        False,
                    )
                )
            continue
        if kind in {"macro", "macro_rules"}:
            declarations.extend(
                (
                    names,
                    type_text,
                    _expand_namespace_body_aliases(body, body_prefixes),
                    False,
                    set(),
                    False,
                )
                for names, type_text, body in _macro_alias_declarations(
                    tail,
                    namespace_prefix,
                )
            )
            continue
        if kind not in alias_kinds:
            continue
        name, signature = _decl_tail_name_and_signature(kind, tail)
        names = _decl_alias_names(name, namespace_prefix)
        if not names:
            continue
        type_text, body = _decl_signature_type_and_body(signature)
        declaration_head = str(match.group(0) or "")[: match.start("tail") - match.start()]
        attribute_bodies = [
            str(attribute.group("body") or "")
            for attribute in _PREAMBLE_ATTRIBUTE_RE.finditer(declaration_head)
        ]
        implementation_targets: set[str] = set()
        unresolved_implementation_attribute = False
        native_implementation = False
        for attribute_body in attribute_bodies:
            attribute_tokens = _identifier_tokens(attribute_body)
            if attribute_tokens.intersection(
                _PREAMBLE_NATIVE_IMPLEMENTATION_ATTRS
            ):
                native_implementation = True
            if "implemented_by" not in attribute_tokens:
                continue
            matches = list(
                _PREAMBLE_IMPLEMENTED_BY_RE.finditer(attribute_body)
            )
            if not matches:
                unresolved_implementation_attribute = True
                continue
            for implementation_match in matches:
                implementation_name = str(
                    implementation_match.group("name") or ""
                ).strip()
                if not implementation_name:
                    unresolved_implementation_attribute = True
                    continue
                implementation_targets.add(implementation_name)
                if "." not in implementation_name:
                    implementation_targets.update(
                        f"{prefix}.{implementation_name}"
                        for prefix in body_prefixes
                    )
        declarations.append(
            (
                names,
                _expand_namespace_body_aliases(type_text, body_prefixes),
                _expand_namespace_body_aliases(
                    _decl_body_value_text(body),
                    body_prefixes,
                ),
                "unsafe" in _identifier_tokens(str(match.group(0) or "")),
                implementation_targets,
                native_implementation or unresolved_implementation_attribute,
            )
        )

    known_declaration_names = {
        name
        for names, _type_text, _body_value, _unsafe, _targets, _native in declarations
        for name in names
    }
    aliases: set[str] = set()
    changed = True
    while changed:
        changed = False
        for (
            names,
            type_text,
            body_value,
            unsafe_decl,
            implementation_targets,
            implementation_is_native_or_malformed,
        ) in declarations:
            if names.issubset(aliases):
                continue
            direct_effect = bool(
                _identifier_tokens(f"{type_text} {body_value}").intersection(
                    _FORBIDDEN_EFFECT_IDENTIFIERS
                )
            )
            transitive_effect = _expression_references_alias(
                f"{type_text} {body_value}",
                aliases,
            )
            implementation_effect = bool(
                implementation_targets.intersection(aliases)
            )
            unresolved_implementation = bool(
                implementation_targets
                and not implementation_targets.intersection(
                    known_declaration_names
                )
            )
            if (
                unsafe_decl
                or direct_effect
                or transitive_effect
                or implementation_effect
                or unresolved_implementation
                or implementation_is_native_or_malformed
            ):
                before = len(aliases)
                aliases.update(names)
                changed = changed or len(aliases) != before
    return aliases


def _proof_like_type_ascription_rejection(
    text: str,
    *,
    proof_aliases: set[str],
) -> str:
    source = str(text or "")
    binder_ranges = _lambda_binder_span_ranges(source)
    cursor = 0
    while cursor < len(source):
        if any(start <= cursor < end for start, end in binder_ranges):
            cursor += 1
            continue
        ch = source[cursor]
        if ch != ":":
            cursor += 1
            continue
        prev_ch = source[cursor - 1] if cursor > 0 else ""
        next_ch = source[cursor + 1] if cursor + 1 < len(source) else ""
        if next_ch in {"=", ":"} or prev_ch == ":":
            cursor += 1
            continue
        type_text = _type_ascription_type_text(source, cursor + 1)
        if _type_text_is_proof_like(type_text) or _type_text_matches_proof_alias(
            type_text,
            proof_aliases,
        ):
            return "proof-like type ascription"
        cursor += 1
    return ""


def _dependent_lambda_rejection(text: str, *, proof_aliases: set[str]) -> str:
    """Reject lambda binders whose later type depends on an inferred binder.

    Observation commands may use ordinary value-level lambdas for small-case
    computation, but not generic/dependent proof-term sketches such as
    ``fun (P) (h : P) => h`` where Lean infers ``P : Sort u``.
    """

    prior_names: set[str] = set()
    for binders in _lambda_binder_spans(str(text or "")):
        if "«" in binders or "»" in binders:
            return "escaped lambda binder"
        cursor = 0
        while cursor < len(binders):
            if binders[cursor].isspace():
                cursor += 1
                continue
            if binders[cursor] in _GROUP_CLOSERS:
                group = _match_grouped_binder(binders, cursor)
                if group:
                    names, type_text, end = group
                    type_tokens = _identifier_tokens(type_text)
                    if prior_names.intersection(type_tokens) or set(names).intersection(
                        type_tokens
                    ):
                        return "dependent lambda binder"
                    if _type_text_is_proof_like(
                        type_text
                    ) or _type_text_matches_proof_alias(type_text, proof_aliases):
                        return "proof-like lambda binder"
                    prior_names.update(names)
                    cursor = end
                    continue
            bare = _BARE_BINDER_RE.match(binders, cursor)
            if bare:
                prior_names.add(bare.group(0))
                cursor = bare.end()
                continue
            cursor += 1
    return ""


def _mode_command(mode: str) -> str:
    normalized = str(mode or "eval").strip().lower()
    if normalized == "reduce":
        return "#reduce"
    if normalized == "check":
        return "#check"
    return "#eval"


def _prepare_queries(
    args: Mapping[str, Any],
    *,
    redact_solution_refs: bool,
    allow_solution_refs: bool = False,
    preamble: str = "",
) -> tuple[list[_PreparedQuery], str]:
    queries, error = _queries_from_args(args)
    if error:
        return [], error
    if not queries:
        return [], "queries must contain at least one expression"
    if len(queries) > _MAX_QUERIES:
        return [], f"too many queries; maximum is {_MAX_QUERIES}"
    if redact_solution_refs and _preamble_materializes_solution_ref(preamble):
        return [], "preamble materializes a hidden official answer symbol"
    solution_aliases = (
        _preamble_solution_ref_aliases(preamble) if redact_solution_refs else set()
    )
    proof_aliases = _preamble_proof_type_aliases(preamble)
    effect_aliases = _preamble_effect_aliases(preamble)
    if allow_solution_refs:
        proof_aliases = {
            alias
            for alias in proof_aliases
            if not _contains_solution_ref_for_prompt(alias)
        }
    total_chars = sum(len(item) for item in queries)
    if total_chars > _MAX_TOTAL_CHARS:
        return [], f"queries are too large; maximum total is {_MAX_TOTAL_CHARS} chars"
    default_command = _mode_command(str(args.get("mode") or "eval"))
    prepared: list[_PreparedQuery] = []
    for index, raw in enumerate(queries, start=1):
        query = str(raw or "").strip()
        if "\n" in query or "\r" in query:
            return [], f"query {index} must be one line"
        if len(query) > _MAX_QUERY_CHARS:
            return [], f"query {index} is too large; maximum is {_MAX_QUERY_CHARS} chars"
        if has_sorry_or_admit(query):
            return [], f"query {index} contains sorry/admit"
        if ";" in query:
            return [], f"query {index} contains unsupported semicolon syntax"
        command = default_command
        expression = query
        match = _COMMAND_RE.match(query)
        if match:
            command = f"#{match.group(1).lower()}"
            expression = str(match.group(2) or "").strip()
        elif query.lstrip().startswith("#"):
            return [], f"query {index} uses an unsupported command"
        # Models commonly emit Lean-3-style finite big-operator binders such
        # as ``∑ i in s, f i``.  Lean 4 parses the ``in`` as the end of the
        # binder and then reports ``unexpected token 'in'; expected ','``.
        # Apply the same lexical, comment/string-safe canonicalization used at
        # subgoal ingestion before handing an observation to Lean.
        expression = _canonicalize_big_operator_binders(expression)
        if not expression:
            return [], f"query {index} has no expression"
        if "#" in _lean_executable_text(expression):
            return [], f"query {index} contains unsupported command marker"
        if redact_solution_refs and _contains_solution_ref_for_prompt(expression):
            return [], f"query {index} references a hidden official answer symbol"
        if solution_aliases and _expression_references_proof_alias(
            expression,
            solution_aliases,
        ):
            return [], f"query {index} references a hidden official answer symbol"
        if command == "#check" and not _SAFE_CHECK_EXPR_RE.fullmatch(expression):
            return [], (
                f"query {index} uses unsupported #check expression; "
                "use a declaration name"
            )
        forbidden = _first_forbidden_identifier(expression)
        if forbidden:
            return [], f"query {index} contains forbidden token `{forbidden}`"
        if _expression_references_alias(expression, effect_aliases):
            return [], f"query {index} references an effectful preamble alias"
        dependent_lambda = _dependent_lambda_rejection(
            expression,
            proof_aliases=proof_aliases,
        )
        if dependent_lambda:
            return [], f"query {index} contains unsupported {dependent_lambda}"
        type_ascription = _proof_like_type_ascription_rejection(
            expression,
            proof_aliases=proof_aliases,
        )
        if type_ascription:
            return [], f"query {index} contains unsupported {type_ascription}"
        if _expression_references_proof_alias(expression, proof_aliases):
            return [], f"query {index} references a proof-like preamble alias"
        prepared.append(
            _PreparedQuery(
                index=index,
                command=f"{command} {expression}",
                mode=command.lstrip("#"),
                expression=expression,
            )
        )
    return prepared, ""


def _increment_metric(dossier: Any, key: str, amount: int = 1) -> None:
    increment = getattr(dossier, "increment_tool_metric", None)
    if callable(increment):
        try:
            increment(key, int(amount))
            return
        except Exception:
            pass
    metrics = getattr(dossier, "tool_metrics", None)
    if isinstance(metrics, dict):
        metrics[key] = int(metrics.get(key, 0) or 0) + int(amount)


async def _run_observation_commands(
    lean: Any,
    commands: Sequence[str],
    *,
    preamble: str,
    timeout_s: float,
    max_heartbeats: int,
    allow_solution_refs: bool = False,
) -> Any:
    runner = getattr(lean, "run_observation_commands", None)
    if not callable(runner):
        raise AttributeError("lean object has no run_observation_commands(...) method")
    result = runner(
        list(commands),
        preamble_override=str(preamble or ""),
        timeout_s=float(timeout_s),
        max_heartbeats=int(max_heartbeats),
        check_kind="compute_examples",
        allow_solution_refs=allow_solution_refs,
    )
    if inspect.isawaitable(result):
        return await result
    return result


def _format_result(
    prepared: Sequence[_PreparedQuery],
    output: str,
    *,
    ok: bool,
    returncode: int,
    redact_solution_refs: bool,
    status: str = "",
) -> str:
    commands = "\n".join(
        "[{}] {}".format(
            item.index,
            _prompt_safe_lean_diagnostic_text(
                item.command,
                limit=360,
                redact_solution_refs=redact_solution_refs,
                strip_comments=False,
            ),
        )
        for item in prepared
    )
    safe_output = _prompt_safe_lean_diagnostic_text(
        str(output or "").strip() or "(Lean produced no output)",
        limit=1400,
        redact_solution_refs=redact_solution_refs,
    )
    status_label = status or ("accepted" if ok else "rejected")
    if status_label == "infrastructure_error":
        status_line = (
            "compute_examples infrastructure error: Lean runner reported an "
            "infrastructure failure (observations only; not proof evidence)."
        )
    else:
        status_line = (
            f"compute_examples {status_label} "
            "(observations only; not proof evidence)."
        )
    return (
        f"{status_line}\n"
        f"Commands:\n{commands}\n"
        f"Lean returncode: {int(returncode)}\n"
        f"Output:\n{safe_output}"
    )


async def _run_compute_examples_tool_impl(
    lean: Any,
    *,
    preamble: str,
    args: Mapping[str, Any],
    dossier: Any = None,
    timeout_s: float = _DEFAULT_TIMEOUT_S,
    max_heartbeats: int = _DEFAULT_MAX_HEARTBEATS,
    redact_solution_refs: bool = True,
    allow_solution_refs: Optional[bool] = None,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> str:
    """Execute bounded Lean computations for observation, never evidence."""

    def deadline_elapsed() -> bool:
        try:
            return bool(deadline_exhausted and deadline_exhausted())
        except Exception:
            return True

    _increment_metric(dossier, "mini_compute_examples_calls", 1)
    effective_allow_solution_refs = bool(
        not redact_solution_refs
        if allow_solution_refs is None
        else allow_solution_refs
    )
    prepared, error = _prepare_queries(
        args if isinstance(args, Mapping) else {},
        redact_solution_refs=redact_solution_refs,
        allow_solution_refs=effective_allow_solution_refs,
        preamble=preamble,
    )
    if error:
        _increment_metric(dossier, "mini_compute_examples_rejected", 1)
        return f"compute_examples error: {error}"
    _increment_metric(dossier, "mini_compute_examples_queries", len(prepared))
    commands = [item.command for item in prepared]
    try:
        result = await _run_observation_commands(
            lean,
            commands,
            preamble=preamble,
            timeout_s=max(
                1.0,
                min(float(timeout_s or _DEFAULT_TIMEOUT_S), _MAX_TIMEOUT_S),
            ),
            max_heartbeats=max(1000, min(int(max_heartbeats or 0), 1000000)),
            allow_solution_refs=effective_allow_solution_refs,
        )
    except Exception as exc:
        if deadline_elapsed():
            return (
                "compute_examples cancelled: llm_turn_elapsed_budget_exhausted "
                "before this observation error could be recorded."
            )
        _increment_metric(dossier, "mini_compute_examples_errors", 1)
        safe_exc_type = _prompt_safe_lean_diagnostic_text(
            type(exc).__name__,
            limit=120,
            redact_solution_refs=redact_solution_refs,
        )
        safe_exc = _prompt_safe_lean_diagnostic_text(
            str(exc),
            limit=500,
            redact_solution_refs=redact_solution_refs,
        )
        return (
            f"compute_examples infrastructure error: "
            f"{safe_exc_type}: {safe_exc}"
        )
    if deadline_elapsed():
        return (
            "compute_examples cancelled: llm_turn_elapsed_budget_exhausted "
            "before this observation could be recorded."
        )
    ok = bool(getattr(result, "ok", False))
    output = str(getattr(result, "output", "") or "")
    returncode = int(getattr(result, "returncode", 1) or 0)
    parsed = getattr(result, "parsed", None)
    infra_failure = bool(getattr(parsed, "infra_failure", False))
    if ok:
        _increment_metric(dossier, "mini_compute_examples_successes", 1)
    elif infra_failure:
        _increment_metric(dossier, "mini_compute_examples_errors", 1)
    else:
        _increment_metric(dossier, "mini_compute_examples_rejected", 1)
    return _format_result(
        prepared,
        output,
        ok=ok,
        returncode=returncode,
        redact_solution_refs=redact_solution_refs,
        status="infrastructure_error" if infra_failure else "",
    )


async def run_compute_examples_tool(*args: Any, **kwargs: Any) -> str:
    """Run an observation only if its Mini telemetry can commit atomically."""

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=kwargs.get("deadline_exhausted"),
        dossier=kwargs.get("dossier"),
        label="compute_examples_tool",
    )
    with transaction:
        if not transaction.can_mutate():
            return (
                "compute_examples cancelled: llm_turn_elapsed_budget_exhausted "
                "before this observation could start."
            )
        result = await _run_compute_examples_tool_impl(*args, **kwargs)
        if not transaction.can_mutate():
            return (
                "compute_examples cancelled: llm_turn_elapsed_budget_exhausted "
                "before this observation could be recorded."
            )
    if transaction.enabled and not transaction.committed:
        return (
            "compute_examples cancelled: "
            + (
                "llm_turn_elapsed_budget_exhausted"
                if transaction.deadline_won
                else "deadline_mutation_commit_failed"
            )
            + " before this observation could be recorded."
        )
    return result


__all__ = ["COMPUTE_EXAMPLES_TOOL", "run_compute_examples_tool"]
