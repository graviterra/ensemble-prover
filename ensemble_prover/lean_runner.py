"""Run bounded Lean checks and normalize diagnostics for proof search."""

from __future__ import annotations

import asyncio
import inspect
import json
import logging
import os
import re
import signal
import subprocess
import tempfile
import time
import uuid
from dataclasses import dataclass, field, replace as dataclass_replace
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Awaitable,
    Callable,
    Dict,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
)

from .config import (
    LeanConfig,
    _append_imports_to_preamble,
    _resolve_lean_scratch_root,
)
from .contract_identity import (
    LEAN_CONTRACT_IDENTITY_VERSION,
    make_lean_contract_identity,
)
from .domain import (
    build_problem_profile,
    enabled_opt_in_tactics_from_config,
    get_domain_opt_in_tactics,
    get_oracle_domain_specific_tactics,
    get_oracle_family_order_for_domains,
)
from .lean_parser import (
    LeanDiagnostic,
    LeanGoalState,
    LeanParseResult,
    canonical_error_type,
    diagnostic_preview,
    has_infra_failure,
    is_oracle_silent_success,
    parse_lean_output,
)
from .lean_syntax import lean_expression_delimiters_balanced
from .persistent_verifier import (
    PersistentVerifierPool,
    PersistentVerifierUnavailableError,
    VerifierRequest,
)
from .lean_server import LeanREPL
from .proof_dossier import _contains_solution_ref_for_prompt, helper_decl_name
from .runtime_context import mark_runtime_owned_callback
from .subprocess_cleanup import terminate_and_reap_process
from .theorem_project import decode_theorem_target_context
from .utils import (
    hash_text,
    has_sorry_or_admit,
    is_standalone_sort_like_lean_expr,
    short_id,
    strip_lean_comments_and_string_literals,
)

if TYPE_CHECKING:
    from .config import TacticOracleConfig

logger = logging.getLogger(__name__)

_LEAN_ENVIRONMENT_OPERATION_TIMEOUT_FLOOR_S = 300.0


def termination_signal_from_returncode(returncode: int) -> int:
    """Return the POSIX signal encoded by a direct or shell exit status."""

    normalized = int(returncode or 0)
    if normalized < 0:
        return -normalized
    shell_signal = normalized - 128
    if 0 < shell_signal < int(getattr(signal, "NSIG", 65)):
        return shell_signal
    return 0

# Mini's trusted proof boundary matches the independent theory and
# falsification verifiers.  In particular, compiler-backed native reduction
# introduces ``Lean.ofReduceBool`` / ``Lean.trustCompiler`` and is not part of
# this allowlist.
_ALLOWED_CHECK_AXIOMS = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)
_PRINT_AXIOMS_DEPENDS_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]"
)
_PRINT_AXIOMS_NONE_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms"
)

_SAFE_CHECK_COMPONENT = r"(?:«[^»\r\n]+»|(?:[^\W\d]|_)[\w']*)"
_SAFE_CHECK_NAME_RE = re.compile(
    rf"^{_SAFE_CHECK_COMPONENT}(?:\.{_SAFE_CHECK_COMPONENT})*$",
    flags=re.UNICODE,
)
_OBSERVATION_COMMAND_RE = re.compile(
    r"^\s*#(eval|reduce|check)(?:\s+|$)(.*)$",
    re.DOTALL,
)
_OBSERVATION_SAFE_CHECK_RE = re.compile(
    r"^@?(?:[^\W\d]|_)[\w']*(?:\.(?:[^\W\d]|_)[\w']*)*$",
    flags=re.UNICODE,
)
_OBSERVATION_IDENT_RE = re.compile(r"(?:[^\W\d]|_)[\w']*", flags=re.UNICODE)
_OBSERVATION_DOTTED_IDENT_PATTERN = (
    r"(?:«[^»]+»|(?:[^\W\d]|_)[\w']*)"
    r"(?:\.(?:«[^»]+»|(?:[^\W\d]|_)[\w']*))*"
)
_OBSERVATION_BARE_BINDER_RE = _OBSERVATION_IDENT_RE
_OBSERVATION_GROUP_CLOSERS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
_OBSERVATION_PREAMBLE_DECL_HEADS = (
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
_OBSERVATION_PREAMBLE_DECL_BOUNDARY_HEADS = _OBSERVATION_PREAMBLE_DECL_HEADS + (
    "end",
    "import",
    "namespace",
    "open",
    "section",
    "set_option",
    "universe",
)
_OBSERVATION_PREAMBLE_MODIFIER_RE = (
    r"(?:(?:local|scoped|private|protected|noncomputable|unsafe|partial)\s+)*"
)
_OBSERVATION_PREAMBLE_DECL_RE = re.compile(
    r"(?ms)^\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    + _OBSERVATION_PREAMBLE_MODIFIER_RE
    + r"(?P<kind>"
    + "|".join(_OBSERVATION_PREAMBLE_DECL_HEADS)
    + r")\b"
    r"(?P<tail>.*?)(?=^\s*(?:@\[[^\]]*\]\s*)*"
    + _OBSERVATION_PREAMBLE_MODIFIER_RE
    + r"(?:"
    + "|".join(_OBSERVATION_PREAMBLE_DECL_BOUNDARY_HEADS)
    + r")\b|\Z)",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_DECL_NAME_RE = re.compile(
    r"^\s*(?P<name>«[^»]+»|(?:[^\W\d]|_)[\w'.]*)(?P<signature>.*)\Z",
    flags=re.UNICODE | re.DOTALL,
)
_OBSERVATION_PREAMBLE_NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+(" + _OBSERVATION_DOTTED_IDENT_PATTERN + r")\s*$",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_END_RE = re.compile(
    r"^\s*end(?:\s+" + _OBSERVATION_DOTTED_IDENT_PATTERN + r")?\s*$",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_OPEN_RE = re.compile(
    r"^\s*open(?:\s+scoped)?\s+(?P<names>.+?)\s*$",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_INERT_SOLUTION_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    + _OBSERVATION_PREAMBLE_MODIFIER_RE
    + r"(?P<kind>axiom|constant)\s+"
    r"(?P<name>«[^»]+»|(?:[^\W\d]|_)[\w'.]*)"
    r"(?P<rest>.*)\Z",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_NOTATION_ALIAS_RE = re.compile(
    r"^\s*(?::[^\s\"“”]+)?\s*(?:\([^)]*\)\s*)?"
    r"[\"“”](?P<name>[^\"“”]+)[\"“”]\s*=>\s*(?P<body>.+)\Z",
    flags=re.UNICODE | re.DOTALL,
)
_OBSERVATION_PREAMBLE_MACRO_ALIAS_RE = re.compile(
    r"`\(\s*(?P<name>"
    + _OBSERVATION_DOTTED_IDENT_PATTERN
    + r")\s*\)\s*=>\s*"
    r"`\(\s*(?P<body>[^\n]*)\)",
    flags=re.UNICODE,
)
_OBSERVATION_PREAMBLE_MACRO_DECL_ALIAS_RE = re.compile(
    r"^\s*(?:\([^)]*\)\s*)*[\"“”](?P<name>[^\"“”]+)[\"“”]\s*:\s*term\s*=>\s*"
    r"`\(\s*(?P<body>[^\n]*)\)",
    flags=re.UNICODE | re.DOTALL,
)
_OBSERVATION_SOLUTION_REF_RE = re.compile(
    r"putnam_[A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*"
)
_OBSERVATION_PROPOSITION_TYPE_MARKERS = {
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
_OBSERVATION_DEFAULT_TIMEOUT_S = 30.0
_OBSERVATION_MAX_TIMEOUT_S = 45.0
_OBSERVATION_DEFAULT_MAX_HEARTBEATS = 200000
_OBSERVATION_MAX_HEARTBEATS = 1000000
_OBSERVATION_FORBIDDEN_TOKENS = {
    "abbrev",
    "aesop",
    "apply",
    "assumption",
    "axiom",
    "by",
    "calc",
    "cases",
    "class",
    "constant",
    "constructor",
    "dbgTrace",
    "def",
    "deriving",
    "elab",
    "example",
    "exact",
    "export",
    "import",
    "include",
    "inductive",
    "initialize",
    "induction",
    "intro",
    "intros",
    "instance",
    "lemma",
    "linarith",
    "local",
    "macro",
    "namespace",
    "norm_num",
    "notation",
    "opaque",
    "open",
    "omega",
    "refine",
    "section",
    "set_option",
    "structure",
    "syntax",
    "theorem",
    "trivial",
    "universe",
    "unsafe",
    "unsafeCast",
    "variable",
    "variables",
    "BaseIO",
    "EIO",
    "FilePath",
    "IO",
    "Process",
    "System",
    "include_str",
    "run_cmd",
    "Prop",
    "Sort",
    "Type",
    "False",
    "True",
    "Eq",
    "Iff",
    "show",
    "exact",
    "have",
    "suffices",
    "calc",
    "rfl",
    "refl",
    "ring",
    "rw",
    "simp",
    "simpa",
}
_OBSERVATION_PROOF_LIKE_TYPE_HEADS = {
    "Even",
    "Odd",
    "Nat.Prime",
    "Prime",
}


def _observation_identifier_tokens(text: str) -> set[str]:
    return {
        match.group(0)
        for match in _OBSERVATION_IDENT_RE.finditer(str(text or ""))
    }


def _observation_strip_lean_comments(text: str) -> str:
    source = str(text or "")
    out: List[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        ch = source[index]
        nxt = source[index + 1] if index + 1 < len(source) else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                index += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth = max(0, block_depth - 1)
                index += 2
                continue
            if ch in "\r\n":
                out.append("\n")
            index += 1
            continue
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            index += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            index += 1
            continue
        if ch == "-" and nxt == "-":
            index += 2
            while index < len(source) and source[index] not in "\r\n":
                index += 1
            if index < len(source):
                out.append("\n")
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            index += 2
            continue
        out.append(ch)
        index += 1
    return "".join(out)


def _observation_lambda_binder_spans(text: str) -> list[str]:
    source = str(text or "")
    return [
        source[start:end]
        for start, end in _observation_lambda_binder_span_ranges(source)
    ]


def _observation_lambda_binder_span_ranges(text: str) -> list[tuple[int, int]]:
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
            if ch in _OBSERVATION_GROUP_CLOSERS:
                closers.append(_OBSERVATION_GROUP_CLOSERS[ch])
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


def _observation_match_grouped_binder(
    text: str,
    start: int,
) -> tuple[list[str], str, int] | None:
    source = str(text or "")
    if start >= len(source) or source[start] not in _OBSERVATION_GROUP_CLOSERS:
        return None
    closers = [_OBSERVATION_GROUP_CLOSERS[source[start]]]
    cursor = start
    cursor += 1
    while cursor < len(source):
        ch = source[cursor]
        if ch in _OBSERVATION_GROUP_CLOSERS:
            closers.append(_OBSERVATION_GROUP_CLOSERS[ch])
        elif closers and ch == closers[-1]:
            closers.pop()
            if not closers:
                inside = source[start + 1 : cursor].strip()
                colon = inside.find(":")
                names_text = inside[:colon] if colon >= 0 else inside
                names = [
                    match.group(0)
                    for match in _OBSERVATION_IDENT_RE.finditer(names_text)
                ]
                if not names:
                    return None
                type_text = inside[colon + 1 :] if colon >= 0 else ""
                return names, type_text, cursor + 1
        cursor += 1
    return None


def _observation_type_text_for_guard(text: str) -> str:
    source = str(text or "")
    out: List[str] = []
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


def _observation_strip_wrapping_type_parens(text: str) -> str:
    source = _observation_type_text_for_guard(text)
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
        source = _observation_type_text_for_guard(source[1:-1])
    return source


def _observation_type_text_is_proof_like(text: str) -> bool:
    source = _observation_strip_wrapping_type_parens(text)
    if not source.strip():
        return False
    if any(marker in source for marker in _OBSERVATION_PROPOSITION_TYPE_MARKERS):
        return True
    dotted_tokens = {
        match.group(0)
        for match in re.finditer(
            _OBSERVATION_DOTTED_IDENT_PATTERN,
            source,
            flags=re.UNICODE,
        )
    }
    if dotted_tokens.intersection(_OBSERVATION_PROOF_LIKE_TYPE_HEADS):
        return True
    return bool(
        _observation_identifier_tokens(source).intersection(
            _OBSERVATION_FORBIDDEN_TOKENS
        )
    )


def _observation_type_text_matches_proof_alias(
    text: str,
    proof_aliases: set[str],
) -> bool:
    source = _observation_strip_wrapping_type_parens(text)
    if not source:
        return False
    if source in proof_aliases:
        return True
    first_match = re.search(
        _OBSERVATION_DOTTED_IDENT_PATTERN,
        source,
        flags=re.UNICODE,
    )
    first_token = first_match.group(0) if first_match else ""
    if first_token in proof_aliases:
        return True
    parts = [part for part in source.split(".") if part]
    for index in range(1, len(parts)):
        if ".".join(parts[:index]) in proof_aliases:
            return True
    return False


def _observation_expression_references_proof_alias(
    text: str,
    proof_aliases: set[str],
) -> bool:
    if not proof_aliases:
        return False
    source = _observation_type_text_for_guard(text)
    tokens = _observation_identifier_tokens(source)
    dotted_tokens = {
        match.group(0)
        for match in re.finditer(
            _OBSERVATION_DOTTED_IDENT_PATTERN,
            source,
            flags=re.UNICODE,
        )
    }
    for alias in proof_aliases:
        item = _observation_strip_wrapping_type_parens(alias)
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
        if not _OBSERVATION_IDENT_RE.fullmatch(item) and item in source:
            return True
    return False


def _observation_type_ascription_type_text(source: str, start: int) -> str:
    text = str(source or "")
    closers: List[str] = []
    out: List[str] = []
    cursor = max(0, int(start or 0))
    stop_closers = set(_OBSERVATION_GROUP_CLOSERS.values())
    while cursor < len(text):
        ch = text[cursor]
        if ch in _OBSERVATION_GROUP_CLOSERS:
            closers.append(_OBSERVATION_GROUP_CLOSERS[ch])
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


def _observation_decl_signature_type_and_body(signature: str) -> Tuple[str, str]:
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


def _observation_decl_tail_name_and_signature(
    kind: str,
    tail: str,
) -> Tuple[str, str]:
    if str(kind or "") in {
        "elab",
        "example",
        "initialize",
        "instance",
        "macro",
        "notation",
        "syntax",
    }:
        return "", str(tail or "")
    match = _OBSERVATION_PREAMBLE_DECL_NAME_RE.match(str(tail or ""))
    if not match:
        return "", str(tail or "")
    return str(match.group("name") or "").strip(), str(match.group("signature") or "")


def _observation_namespace_prefix_at(source: str, position: int) -> str:
    stack: List[str] = []
    for line in str(source or "")[: max(0, position)].splitlines():
        namespace_match = _OBSERVATION_PREAMBLE_NAMESPACE_RE.match(line)
        if namespace_match:
            stack.append(namespace_match.group(1))
            continue
        if _OBSERVATION_PREAMBLE_END_RE.match(line) and stack:
            stack.pop()
    return ".".join(item for item in stack if item)


def _observation_decl_alias_names(name: str, namespace_prefix: str) -> set[str]:
    raw = str(name or "").strip()
    if not raw:
        return set()
    names = {raw}
    prefix = str(namespace_prefix or "").strip(".")
    if prefix and not raw.startswith(prefix + "."):
        names.add(f"{prefix}.{raw}")
    return names


def _observation_open_namespace_prefixes_at(
    source: str,
    position: int,
) -> List[str]:
    prefixes: List[str] = []
    seen: set[str] = set()
    for line in str(source or "")[: max(0, position)].splitlines():
        match = _OBSERVATION_PREAMBLE_OPEN_RE.match(line)
        if not match:
            continue
        for item in re.finditer(
            _OBSERVATION_DOTTED_IDENT_PATTERN,
            match.group("names"),
            flags=re.UNICODE,
        ):
            name = str(item.group(0) or "").strip(".")
            if name and name not in seen:
                seen.add(name)
                prefixes.append(name)
    return prefixes


def _observation_body_resolution_prefixes(
    source: str,
    position: int,
    namespace_prefix: str,
) -> List[str]:
    prefixes: List[str] = []
    seen: set[str] = set()
    for raw in [
        namespace_prefix,
        *_observation_open_namespace_prefixes_at(source, position),
    ]:
        prefix = str(raw or "").strip(".")
        if prefix and prefix not in seen:
            seen.add(prefix)
            prefixes.append(prefix)
    return prefixes


def _observation_expand_namespace_body_aliases(
    text: str,
    prefixes: str | Sequence[str],
) -> str:
    source = str(text or "")
    raw_prefixes = (
        [prefixes]
        if isinstance(prefixes, str)
        else list(prefixes or ())
    )
    clean_prefixes = [
        str(item or "").strip(".") for item in raw_prefixes if str(item or "").strip(".")
    ]
    additions: List[str] = []
    if clean_prefixes:
        for token in re.finditer(
            _OBSERVATION_DOTTED_IDENT_PATTERN,
            source,
            flags=re.UNICODE,
        ):
            item = str(token.group(0) or "").strip()
            if item and "." not in item:
                additions.extend(f"{prefix}.{item}" for prefix in clean_prefixes)
    for match in re.finditer(
        r"\bopen\s+(?:scoped\s+)?(?P<ns>"
        + _OBSERVATION_DOTTED_IDENT_PATTERN
        + r")\s+in\s+(?P<body>[^,\n;)]*)",
        source,
        flags=re.UNICODE,
    ):
        prefix = str(match.group("ns") or "").strip(".")
        body = str(match.group("body") or "")
        if not prefix:
            continue
        for token in re.finditer(
            _OBSERVATION_DOTTED_IDENT_PATTERN,
            body,
            flags=re.UNICODE,
        ):
            item = str(token.group(0) or "").strip()
            if item and "." not in item:
                additions.append(f"{prefix}.{item}")
    if not additions:
        return source
    return source + " " + " ".join(additions)


def _observation_decl_body_value_text(body: str) -> str:
    source = str(body or "")
    if ":=" in source:
        return source.split(":=", 1)[1]
    where_match = re.search(r"\bwhere\b", source)
    if where_match is not None:
        return source[where_match.end() :]
    return ""


def _observation_line_is_inert_solution_decl(line: str) -> bool:
    match = _OBSERVATION_PREAMBLE_INERT_SOLUTION_DECL_RE.match(str(line or ""))
    if not match:
        return False
    name = str(match.group("name") or "")
    rest = str(match.group("rest") or "")
    if not _contains_solution_ref_for_prompt(name):
        return False
    if _contains_solution_ref_for_prompt(rest):
        return False
    return ":=" not in rest and not re.search(r"\bwhere\b", rest)


def _observation_decl_materializes_solution_ref(
    *,
    kind: str,
    names: set[str],
    text: str,
    signature: str,
) -> bool:
    official_name = any(_contains_solution_ref_for_prompt(name) for name in names)
    if official_name:
        _type_text, body = _observation_decl_signature_type_and_body(signature)
        body_value = _observation_decl_body_value_text(body)
        if str(kind or "") in {"axiom", "constant"} and not body_value:
            return False
        return True
    return _contains_solution_ref_for_prompt(text)


def _observation_preamble_materializes_solution_ref(preamble: str) -> bool:
    source = _observation_strip_lean_comments(str(preamble or ""))
    direct_solution_ref = _contains_solution_ref_for_prompt(source)
    for match in _OBSERVATION_PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        namespace_prefix = _observation_namespace_prefix_at(source, match.start())
        body_prefixes = _observation_body_resolution_prefixes(
            source,
            match.start(),
            namespace_prefix,
        )
        name, signature = _observation_decl_tail_name_and_signature(kind, tail)
        names = _observation_decl_alias_names(name, namespace_prefix)
        expanded_text = _observation_expand_namespace_body_aliases(
            str(match.group(0) or ""),
            body_prefixes,
        )
        if _observation_decl_materializes_solution_ref(
            kind=kind,
            names=names,
            text=expanded_text,
            signature=signature,
        ):
            return True
    if not direct_solution_ref:
        return False
    for line in source.splitlines():
        if _contains_solution_ref_for_prompt(
            line
        ) and not _observation_line_is_inert_solution_decl(line):
            return True
    return False


def _observation_preamble_solution_ref_aliases(preamble: str) -> set[str]:
    source = _observation_strip_lean_comments(str(preamble or ""))
    aliases: set[str] = set()
    for match in _OBSERVATION_PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        if kind not in {"axiom", "constant"}:
            continue
        namespace_prefix = _observation_namespace_prefix_at(source, match.start())
        name, _signature = _observation_decl_tail_name_and_signature(kind, tail)
        names = _observation_decl_alias_names(name, namespace_prefix)
        official_names = {
            item for item in names if _contains_solution_ref_for_prompt(item)
        }
        for item in official_names:
            aliases.add(item)
            short = item.rsplit(".", 1)[-1].strip()
            if short:
                aliases.add(short)
    return aliases


def _observation_variable_alias_declarations(
    tail: str,
    namespace_prefix: str,
) -> List[Tuple[set[str], str, str]]:
    declarations: List[Tuple[set[str], str, str]] = []
    source = str(tail or "")
    cursor = 0
    while cursor < len(source):
        group = _observation_match_grouped_binder(source, cursor)
        if group:
            names, type_text, end = group
            for name in names:
                aliases = _observation_decl_alias_names(name, namespace_prefix)
                if aliases:
                    declarations.append((aliases, type_text, ""))
            cursor = end
            continue
        cursor += 1
    return declarations


def _observation_notation_alias_declaration(
    tail: str,
    namespace_prefix: str,
) -> Optional[Tuple[set[str], str, str]]:
    match = _OBSERVATION_PREAMBLE_NOTATION_ALIAS_RE.match(str(tail or ""))
    if not match:
        return None
    name = str(match.group("name") or "").strip()
    aliases = _observation_decl_alias_names(name, namespace_prefix)
    if not aliases:
        return None
    return aliases, "", str(match.group("body") or "")


def _observation_macro_alias_declarations(
    text: str,
    namespace_prefix: str,
) -> List[Tuple[set[str], str, str]]:
    declarations: List[Tuple[set[str], str, str]] = []
    for match in _OBSERVATION_PREAMBLE_MACRO_ALIAS_RE.finditer(str(text or "")):
        aliases = _observation_decl_alias_names(
            str(match.group("name") or ""),
            namespace_prefix,
        )
        if aliases:
            declarations.append((aliases, "", str(match.group("body") or "")))
    for match in _OBSERVATION_PREAMBLE_MACRO_DECL_ALIAS_RE.finditer(str(text or "")):
        aliases = _observation_decl_alias_names(
            str(match.group("name") or ""),
            namespace_prefix,
        )
        if aliases:
            declarations.append((aliases, "", str(match.group("body") or "")))
    return declarations


def _observation_preamble_proof_type_aliases(preamble: str) -> set[str]:
    source = _observation_strip_lean_comments(str(preamble or ""))
    declarations: List[Tuple[set[str], str, str]] = []
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
    for match in _OBSERVATION_PREAMBLE_DECL_RE.finditer(source):
        kind = str(match.group("kind") or "")
        tail = str(match.group("tail") or "")
        namespace_prefix = _observation_namespace_prefix_at(source, match.start())
        body_prefixes = _observation_body_resolution_prefixes(
            source,
            match.start(),
            namespace_prefix,
        )
        if kind in {"variable", "variables"}:
            declarations.extend(
                _observation_variable_alias_declarations(tail, namespace_prefix)
            )
            continue
        if kind == "notation":
            item = _observation_notation_alias_declaration(tail, namespace_prefix)
            if item is not None:
                names, type_text, body = item
                declarations.append(
                    (
                        names,
                        type_text,
                        _observation_expand_namespace_body_aliases(
                            body,
                            body_prefixes,
                        ),
                    )
                )
            continue
        if kind == "macro_rules":
            declarations.extend(
                (
                    names,
                    type_text,
                    _observation_expand_namespace_body_aliases(
                        body,
                        body_prefixes,
                    ),
                )
                for names, type_text, body in _observation_macro_alias_declarations(
                    tail,
                    namespace_prefix,
                )
            )
            continue
        if kind == "macro":
            declarations.extend(
                (
                    names,
                    type_text,
                    _observation_expand_namespace_body_aliases(
                        body,
                        body_prefixes,
                    ),
                )
                for names, type_text, body in _observation_macro_alias_declarations(
                    tail,
                    namespace_prefix,
                )
            )
            continue
        if kind not in alias_kinds:
            continue
        name, signature = _observation_decl_tail_name_and_signature(
            kind,
            tail,
        )
        names = _observation_decl_alias_names(
            name,
            namespace_prefix,
        )
        if not names:
            continue
        type_text, body = _observation_decl_signature_type_and_body(signature)
        declarations.append(
            (names, type_text, _observation_decl_body_value_text(body))
        )
    aliases: set[str] = set()
    changed = True
    while changed:
        changed = False
        for names, type_text, body_value in declarations:
            if names.issubset(aliases):
                continue
            if (
                _observation_type_text_is_proof_like(type_text)
                or _observation_type_text_matches_proof_alias(type_text, aliases)
                or _observation_type_text_is_proof_like(body_value)
                or _observation_type_text_matches_proof_alias(body_value, aliases)
            ):
                before = len(aliases)
                aliases.update(names)
                changed = changed or len(aliases) != before
    return aliases


def _observation_proof_like_type_ascription_rejection(
    text: str,
    *,
    proof_aliases: set[str],
) -> str:
    source = str(text or "")
    binder_ranges = _observation_lambda_binder_span_ranges(source)
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
        type_text = _observation_type_ascription_type_text(source, cursor + 1)
        if _observation_type_text_is_proof_like(
            type_text
        ) or _observation_type_text_matches_proof_alias(type_text, proof_aliases):
            return "proof-like type ascription"
        cursor += 1
    return ""


def _observation_dependent_lambda_rejection(
    text: str,
    *,
    proof_aliases: set[str],
) -> str:
    prior_names: set[str] = set()
    for binders in _observation_lambda_binder_spans(str(text or "")):
        if "«" in binders or "»" in binders:
            return "escaped lambda binder"
        cursor = 0
        while cursor < len(binders):
            if binders[cursor].isspace():
                cursor += 1
                continue
            if binders[cursor] in _OBSERVATION_GROUP_CLOSERS:
                group = _observation_match_grouped_binder(binders, cursor)
                if group:
                    names, type_text, end = group
                    type_tokens = _observation_identifier_tokens(type_text)
                    if prior_names.intersection(type_tokens) or set(names).intersection(
                        type_tokens
                    ):
                        return "dependent lambda binder"
                    if _observation_type_text_is_proof_like(
                        type_text
                    ) or _observation_type_text_matches_proof_alias(
                        type_text,
                        proof_aliases,
                    ):
                        return "proof-like lambda binder"
                    prior_names.update(names)
                    cursor = end
                    continue
            bare = _OBSERVATION_BARE_BINDER_RE.match(binders, cursor)
            if bare:
                prior_names.add(bare.group(0))
                cursor = bare.end()
                continue
            cursor += 1
    return ""


def _validate_observation_commands(
    commands: Sequence[str],
    *,
    preamble: str = "",
    allow_solution_refs: bool = False,
) -> Tuple[List[str], str]:
    safe_commands = [
        str(command or "").strip()
        for command in list(commands or [])
        if str(command or "").strip()
    ]
    if not safe_commands:
        return [], "observation command list is empty"
    if len(safe_commands) > 8:
        return [], "too many observation commands"
    if (
        not allow_solution_refs
        and _observation_preamble_materializes_solution_ref(preamble)
    ):
        return [], "observation preamble materializes an official answer symbol"
    solution_aliases = (
        set()
        if allow_solution_refs
        else _observation_preamble_solution_ref_aliases(preamble)
    )
    proof_aliases = _observation_preamble_proof_type_aliases(preamble)
    if allow_solution_refs:
        proof_aliases = {
            alias
            for alias in proof_aliases
            if not _contains_solution_ref_for_prompt(alias)
        }
    total_chars = sum(len(command) for command in safe_commands)
    if total_chars > 1800:
        return [], "observation commands are too large"
    for index, command in enumerate(safe_commands, start=1):
        if "\n" in command or "\r" in command:
            return [], f"observation command {index} must be one line"
        if ";" in command:
            return [], f"observation command {index} contains unsupported semicolon"
        if len(command) > 360:
            return [], f"observation command {index} is too large"
        if has_sorry_or_admit(command):
            return [], f"observation command {index} contains sorry/admit"
        match = _OBSERVATION_COMMAND_RE.match(command)
        if not match:
            return [], f"observation command {index} must be #eval/#reduce/#check"
        kind = f"#{match.group(1).lower()}"
        expression = str(match.group(2) or "").strip()
        if not expression:
            return [], f"observation command {index} has no expression"
        if "#" in expression:
            return [], f"observation command {index} contains unsupported command marker"
        if (
            not allow_solution_refs
            and _contains_solution_ref_for_prompt(expression)
        ):
            return [], (
                f"observation command {index} references an official answer symbol"
            )
        if solution_aliases and _observation_expression_references_proof_alias(
            expression,
            solution_aliases,
        ):
            return [], (
                f"observation command {index} references an official answer symbol"
            )
        if kind == "#check" and not _OBSERVATION_SAFE_CHECK_RE.fullmatch(expression):
            return [], f"observation command {index} has unsupported #check expression"
        tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", expression))
        dotted_tokens = set(
            re.findall(
                r"[A-Za-z_][A-Za-z0-9_']*",
                expression.replace(".", "_"),
            )
        )
        forbidden = sorted(
            token
            for token in _OBSERVATION_FORBIDDEN_TOKENS
            if token in tokens or token in dotted_tokens
        )
        if forbidden:
            return [], (
                f"observation command {index} contains forbidden token "
                f"`{forbidden[0]}`"
            )
        dependent_lambda = _observation_dependent_lambda_rejection(
            expression,
            proof_aliases=proof_aliases,
        )
        if dependent_lambda:
            return [], (
                f"observation command {index} contains unsupported "
                f"{dependent_lambda}"
            )
        type_ascription = _observation_proof_like_type_ascription_rejection(
            expression,
            proof_aliases=proof_aliases,
        )
        if type_ascription:
            return [], (
                f"observation command {index} contains unsupported "
                f"{type_ascription}"
            )
        if _observation_expression_references_proof_alias(expression, proof_aliases):
            return [], (
                f"observation command {index} references a proof-like preamble alias"
            )
    return safe_commands, ""



def _captured_output_text(
    stdout_chunks: Sequence[bytes], stderr_chunks: Sequence[bytes]
) -> str:
    stdout_str = b"".join(stdout_chunks).decode(errors="replace")
    stderr_str = b"".join(stderr_chunks).decode(errors="replace")
    return stdout_str + ("\n" if stdout_str and stderr_str else "") + stderr_str


def _status_with_captured_output(
    status: str,
    stdout_chunks: Sequence[bytes],
    stderr_chunks: Sequence[bytes],
) -> str:
    detail = _captured_output_text(stdout_chunks, stderr_chunks).strip()
    if not detail:
        return status
    return f"{detail}\n{status}"


_LEAN_DIAGNOSTIC_HEADER_RE = re.compile(
    r"^.{0,4096}?:\d+:\d+:\s+error(?:\([^\r\n)]*\))?:\s*(?P<message>.*)$"
)
_LEAN_SEMANTIC_TIMEOUT_MESSAGE_RE = re.compile(
    r"^(?:(?:\(deterministic\)|deterministic)\s+)?(?:"
    r"maximum heartbeats exceeded"
    r"|maximum number of heartbeats\b.*\bhas been reached"
    r"|time limit exceeded"
    r"|timeout at `"
    r")",
    re.IGNORECASE,
)


def _execution_ended_without_complete_contract_output(
    execution: "_BackendExecutionResult",
) -> bool:
    """Recognize authenticated runner status or canonical Lean timeout."""

    if int(execution.returncode or 0) == 0:
        return False
    if str(getattr(execution, "backend", "") or "").strip().lower() == "deadline":
        return True
    terminal_status = ""
    for raw_line in str(execution.output or "").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        terminal_status = line
        # Generated structural markers can be megabytes long and may contain
        # arbitrary display text. Only bounded compiler diagnostic headers are
        # allowed to classify a semantic timeout.
        if line.startswith("MINI_CONTRACT_ANALYSIS_"):
            continue
        if len(line) > 8192:
            continue
        diagnostic = _LEAN_DIAGNOSTIC_HEADER_RE.match(line)
        if diagnostic is not None and _LEAN_SEMANTIC_TIMEOUT_MESSAGE_RE.match(
            str(diagnostic.group("message") or "").strip()
        ):
            return True
    return bool(
        terminal_status == "Lean timeout"
        or terminal_status.startswith("Lean subprocess error:")
        or terminal_status
        == "persistent verifier timed out waiting for Lean diagnostics"
    )


def _consume_future_exception(fut: "asyncio.Future") -> None:
    """Done-callback that marks a Future's exception as retrieved.

    Attached at creation to any coalescing Future in _inflight_exec whose
    exception may never reach an awaiter — e.g. a leader that runs solo
    and raises. Without this, asyncio.Future.__del__ logs "Future
    exception was never retrieved" at GC because set_exception flipped
    __log_traceback=True and nothing flipped it back. Real awaiters
    still receive the exception via their own await — .exception() is
    idempotent.
    """
    if fut.cancelled():
        return
    try:
        fut.exception()
    except BaseException:  # pragma: no cover — exception() on a done non-cancelled future cannot raise
        pass


_consume_future_exception = mark_runtime_owned_callback(
    _consume_future_exception
)


# ---------------------------------------------------------------------------
# Tactic Oracle — goal-aware vocabulary planning
# ---------------------------------------------------------------------------

# Tier 1: structural/trivial — tried as a combined `first | ... | sorry`
# in ONE Lean call. The trailing fallback lets misses compile, while the
# parser distinguishes real unresolved-sorry warnings from benign linter
# messages like "'sorry' tactic does nothing".
#
# Each alternative is prefixed by ``intros`` so goals with leading ∀/Π
# binders (e.g. scaffold slot targets like
# ``∀ (S : Type*) [CommSemigroup S] (a c d : S), a*(c*d) = (a*c)*d``)
# can be discharged. Without the intros prefix, tactics like ``rfl`` /
# ``ac_rfl`` / ``assumption`` run against the forall itself and fail
# with ``equality expected`` / ``no hypotheses`` — live trace
# 2012_a2_19apr_15.jsonl: 0/126 oracle calls produced a Tier-1 hit
# because every scaffold slot target carries leading ∀ binders.
# ``intros`` on a non-forall goal is a benign no-op (linter warning only)
# and does not change the outcome of subsequent tactics.
_TIER1_COMBINED = (
    "intros; first | rfl | trivial | assumption | contradiction | tauto | ac_rfl"
)
_TIER1_INDIVIDUAL = (
    "intros; rfl",
    "intros; trivial",
    "intros; assumption",
    "intros; contradiction",
    "intros; tauto",
    "intros; ac_rfl",
)


@dataclass(frozen=True)
class _OracleTacticSpec:
    tactic: str
    tier: str
    family: str
    suggestion_tactic: bool = False


@dataclass(frozen=True)
class _OracleGoalProfile:
    statement_domain: str
    learning_domains: Tuple[str, ...]
    domain_family: str
    has_hypotheses: bool
    has_arithmetic: bool
    has_structure: bool
    has_negation: bool
    has_extensional: bool
    has_equality: bool
    has_finite_objects: bool
    has_measure: bool
    has_probability: bool
    has_analysis: bool


@dataclass(frozen=True)
class _BackendExecutionResult:
    returncode: int
    output: str
    backend: str


@dataclass(frozen=True)
class _BuiltLeanFile:
    """Result of ``LeanRunner._build_file``.

    ``goal_start_line`` is the 1-indexed Lean source line where the goal
    block begins (after the preamble + universe decl + lemma block). It
    feeds ``parse_lean_output(..., goal_start_line=...)`` so ``Try this:``
    suggestions emitted by linters against context-lemma bodies are not
    promoted as candidate proofs for the goal.
    """

    content: str
    goal_start_line: int
    lemma_block_start_line: int = 0
    axiom_audit_names: Tuple[str, ...] = ()


_ORACLE_FAMILY_SPECS: Tuple[Tuple[str, Tuple[_OracleTacticSpec, ...]], ...] = (
    (
        "search",
        (
            _OracleTacticSpec("solve_by_elim", "tier2", "search"),
            _OracleTacticSpec("exact?", "tier4", "search", suggestion_tactic=True),
            _OracleTacticSpec("apply?", "tier4", "search", suggestion_tactic=True),
            _OracleTacticSpec("aesop", "tier4", "search"),
            _OracleTacticSpec("rw?", "tier4", "search", suggestion_tactic=True),
            _OracleTacticSpec("simp?", "tier4", "search", suggestion_tactic=True),
        ),
    ),
    (
        "structural",
        (
            _OracleTacticSpec("constructor <;> simp", "tier3", "structural"),
            _OracleTacticSpec("ext; simp", "tier3", "structural"),
            _OracleTacticSpec("constructor <;> aesop", "tier3", "structural"),
            _OracleTacticSpec("ext; aesop", "tier3", "structural"),
            _OracleTacticSpec("constructor <;> ring", "tier3", "structural"),
            _OracleTacticSpec("constructor <;> norm_num", "tier3", "structural"),
            _OracleTacticSpec("constructor <;> linarith", "tier3", "structural"),
            _OracleTacticSpec("constructor <;> omega", "tier3", "structural"),
            _OracleTacticSpec("ext; ring", "tier3", "structural"),
            _OracleTacticSpec("constructor", "tier2", "structural"),
            _OracleTacticSpec("ext", "tier2", "structural"),
            _OracleTacticSpec("funext", "tier3", "structural"),
            _OracleTacticSpec("fin_cases <;> simp", "tier3", "structural"),
            _OracleTacticSpec("fin_cases <;> norm_num", "tier3", "structural"),
        ),
    ),
    (
        "simp",
        (
            _OracleTacticSpec("simp", "tier2", "simp"),
            _OracleTacticSpec("simpa", "tier2", "simp"),
            _OracleTacticSpec("simp_all", "tier2", "simp"),
            _OracleTacticSpec("push_neg; simp", "tier3", "simp"),
            _OracleTacticSpec("simp; linarith", "tier3", "simp"),
            _OracleTacticSpec("simp; ring", "tier3", "simp"),
            _OracleTacticSpec("simp; omega", "tier3", "simp"),
        ),
    ),
    (
        "analysis",
        (
            _OracleTacticSpec("continuity", "tier3", "analysis"),
            _OracleTacticSpec("measurability", "tier3", "analysis"),
            _OracleTacticSpec("fun_prop", "tier3", "analysis"),
            _OracleTacticSpec("prove_integrable", "tier2", "analysis"),
            _OracleTacticSpec(
                "apply ContinuousOn.intervalIntegrable", "tier2", "analysis"
            ),
            _OracleTacticSpec(
                "apply DifferentiableOn.intervalIntegrable", "tier2", "analysis"
            ),
            _OracleTacticSpec("apply Summable.of_norm_bounded", "tier3", "analysis"),
            _OracleTacticSpec(
                "apply summable_geometric_of_lt_one", "tier3", "analysis"
            ),
            _OracleTacticSpec("mono", "tier3", "analysis"),
            _OracleTacticSpec("filter_upwards", "tier3", "analysis"),
        ),
    ),
    (
        "negation",
        (
            _OracleTacticSpec("contrapose!; simp", "tier3", "negation"),
            _OracleTacticSpec("push_neg; linarith", "tier3", "negation"),
            _OracleTacticSpec("push_neg; omega", "tier3", "negation"),
            _OracleTacticSpec("by_contra; linarith", "tier3", "negation"),
            _OracleTacticSpec("by_contra; omega", "tier3", "negation"),
            _OracleTacticSpec("exfalso; linarith", "tier3", "negation"),
            _OracleTacticSpec("exfalso; omega", "tier3", "negation"),
        ),
    ),
    (
        "arithmetic",
        (
            _OracleTacticSpec("omega", "tier2", "arithmetic"),
            _OracleTacticSpec("ring", "tier2", "arithmetic"),
            _OracleTacticSpec("ring_nf", "tier2", "arithmetic"),
            _OracleTacticSpec("norm_num", "tier2", "arithmetic"),
            _OracleTacticSpec("norm_cast", "tier2", "arithmetic"),
            _OracleTacticSpec("linarith", "tier2", "arithmetic"),
            _OracleTacticSpec("positivity", "tier2", "arithmetic"),
            _OracleTacticSpec("decide", "tier2", "arithmetic"),
            _OracleTacticSpec("native_decide", "tier2", "arithmetic"),
            _OracleTacticSpec("lia", "tier3", "arithmetic"),
            _OracleTacticSpec("bound", "tier3", "arithmetic"),
            _OracleTacticSpec("nlinarith", "tier3", "arithmetic"),
            _OracleTacticSpec("grind", "tier3", "arithmetic"),
            _OracleTacticSpec("field_simp", "tier3", "arithmetic"),
            _OracleTacticSpec("field_simp; ring", "tier3", "arithmetic"),
            _OracleTacticSpec("gcongr", "tier3", "arithmetic"),
            _OracleTacticSpec("abel", "tier3", "arithmetic"),
            _OracleTacticSpec("group", "tier3", "arithmetic"),
            _OracleTacticSpec("push_cast; ring", "tier3", "arithmetic"),
            _OracleTacticSpec("push_cast; omega", "tier3", "arithmetic"),
            _OracleTacticSpec("push_cast; norm_num", "tier3", "arithmetic"),
            _OracleTacticSpec("norm_cast; omega", "tier3", "arithmetic"),
            _OracleTacticSpec("norm_cast; ring", "tier3", "arithmetic"),
            _OracleTacticSpec("norm_num; ring", "tier3", "arithmetic"),
            _OracleTacticSpec("simp; norm_num", "tier3", "arithmetic"),
            _OracleTacticSpec("zify; omega", "tier3", "arithmetic"),
            _OracleTacticSpec("interval_cases <;> norm_num", "tier3", "arithmetic"),
            _OracleTacticSpec("interval_cases <;> simp", "tier3", "arithmetic"),
            _OracleTacticSpec("interval_cases <;> omega", "tier3", "arithmetic"),
        ),
    ),
    (
        "putnam",
        (
            _OracleTacticSpec("putnam_logic", "tier2", "putnam"),
            _OracleTacticSpec("putnam_interval", "tier2", "putnam"),
            _OracleTacticSpec("putnam_analysis", "tier2", "putnam"),
            _OracleTacticSpec("putnam_fun_prop", "tier2", "putnam"),
            _OracleTacticSpec("putnam_continuousOn", "tier2", "putnam"),
            _OracleTacticSpec("putnam_measurable", "tier2", "putnam"),
            _OracleTacticSpec("putnam_mono", "tier2", "putnam"),
            _OracleTacticSpec("putnam", "tier3", "putnam"),
            _OracleTacticSpec("putnam_field", "tier3", "putnam"),
            _OracleTacticSpec("putnam_ring", "tier3", "putnam"),
            _OracleTacticSpec("putnam_order", "tier3", "putnam"),
            _OracleTacticSpec("putnam_cast", "tier3", "putnam"),
            _OracleTacticSpec("putnam_finite", "tier3", "putnam"),
            _OracleTacticSpec("putnam_bigops", "tier3", "putnam"),
        ),
    ),
    (
        "domain_specific",
        (),
    ),
)

_ORACLE_FAMILY_ORDER = tuple(name for name, _ in _ORACLE_FAMILY_SPECS)
_ORACLE_SPECS_BY_FAMILY = {name: specs for name, specs in _ORACLE_FAMILY_SPECS}
_ORACLE_CORE_SPECS = tuple(spec for _, specs in _ORACLE_FAMILY_SPECS for spec in specs)

# Tier labels now represent per-tactic budget classes, not a strict global
# execution order.  The actual scan order is goal-aware and family-balanced.
_TIER2_TACTICS = tuple(
    spec.tactic for spec in _ORACLE_CORE_SPECS if spec.tier == "tier2"
)
_TIER3_TACTICS = tuple(
    spec.tactic for spec in _ORACLE_CORE_SPECS if spec.tier == "tier3"
)
_TIER4_TACTICS = tuple(
    spec.tactic for spec in _ORACLE_CORE_SPECS if spec.tier == "tier4"
)

# Set of tactics whose success is detected via "Try this:" suggestions rather
# than silent success (returncode=0 and sorry_count=0).
_SUGGESTION_TACTICS = frozenset(
    spec.tactic for spec in _ORACLE_CORE_SPECS if spec.suggestion_tactic
)

# Compiled regex for matching the first `sorry` in a proof.
_SORRY_PATTERN = re.compile(r"\bsorry\b")

# Free universe-variable detection (structural fix, 2026-04-16):
# Match `Type u`, `Type u_1`, `Sort u_2`, `Type.{u}`, etc. where the
# universe identifier is a lowercase token starting with a letter.
# We exclude bound names like `Type 0`, `Type _`, `Type max u v` from
# the simple detection — collected names are filtered through a
# stoplist of Lean keywords.
_UNIVERSE_VAR_RE = re.compile(
    r"\b(?:Type|Sort)(?:\.\{)?\s*\(?\s*([a-z][A-Za-z0-9_']*)\b"
)
# Lean keywords / common identifiers that look like universe vars
# but aren't free universes when they appear in a Type/Sort position.
_UNIVERSE_VAR_STOPLIST: frozenset[str] = frozenset(
    {"max", "imax", "of", "Type", "Sort", "Prop", "in", "let", "fun", "do"}
)


def _free_universe_names(statement: str) -> tuple[str, ...]:
    """Return free universe identifiers in deterministic schema order."""

    text = str(statement or "")
    if not text:
        return ()
    seen: List[str] = []

    def collect(fragment: str) -> None:
        for name in re.findall(r"\b[a-z][A-Za-z0-9_']*\b", fragment):
            if name not in _UNIVERSE_VAR_STOPLIST and name not in seen:
                seen.append(name)

    for match in re.finditer(r"\.\{([^{}]*)\}", text):
        collect(match.group(1))
    for match in re.finditer(r"\b(?:Type|Sort)\b", text):
        cursor = match.end()
        while cursor < len(text) and text[cursor].isspace():
            cursor += 1
        if cursor >= len(text) or text.startswith(".{", cursor):
            continue
        if text[cursor] == "(":
            depth = 0
            end = cursor
            while end < len(text):
                if text[end] == "(":
                    depth += 1
                elif text[end] == ")":
                    depth -= 1
                    if depth == 0:
                        end += 1
                        break
                end += 1
            collect(text[cursor:end])
        else:
            level = re.match(r"[a-z][A-Za-z0-9_']*", text[cursor:])
            if level:
                collect(level.group(0))
    # Lean's delaborator assigns u_1, u_2, ... by declaration parameter
    # order, even when their first textual occurrences are reversed.
    if seen and all(re.fullmatch(r"u_[0-9]+", name) for name in seen):
        seen.sort(key=lambda name: int(name[2:]))
    return tuple(seen)


def _declared_universe_names(source: str) -> frozenset[str]:
    names: set[str] = set()
    scan = strip_lean_comments_and_string_literals(str(source or ""))
    for match in re.finditer(r"(?m)^\s*universe\s+([^\r\n]+)", scan):
        for name in re.findall(r"\b[a-z][A-Za-z0-9_']*\b", match.group(1)):
            names.add(name)
    return frozenset(names)


def _free_universe_decl(statement: str, *, declared_in: str = "") -> str:
    """Return a `universe ...` declaration line for free universe vars.

    Lean's PutnamBench project uses `autoImplicit: false`, so a stray
    `Type u_1` in a wrapped `example :` will fail to elaborate without
    an explicit `universe u_1` declaration.  This helper extracts those
    free universe identifiers from the statement and emits the
    corresponding declaration.  Returns "" when no free universes are
    present (the common case for fully-monomorphic statements).
    """
    declared = _declared_universe_names(declared_in)
    names = [name for name in _free_universe_names(statement) if name not in declared]
    if not names:
        return ""
    return "universe " + " ".join(names)


_PROP_LOGIC_RE = re.compile(
    r"(?:¬|∧|∨|→|↔|->|<->|=>|/\\|\\/)" r"|(?:\b(?:True|False|Not|not|And|Or|Iff)\b)"
)
_NONPROP_BINDER_RE = re.compile(
    r"(?:[∀∃]|\b(?:forall|exists)\b)\s*\([^)]*:\s*(?!Prop\b)[^)]*\)"
)
_BARE_QUANTIFIER_RE = re.compile(
    r"^\s*(?:[∀∃]|\b(?:forall|exists)\b)\s+[A-Za-z0-9_`']+"
)


def _build_oracle_goal_profile(
    statement: str,
    *,
    goal_text: str | None = None,
    goal_hypotheses: Sequence[str] = (),
) -> _OracleGoalProfile:
    root_profile = build_problem_profile(
        statement,
        goal_text=goal_text,
        goal_hypotheses=goal_hypotheses,
    )
    focus_text = str(goal_text or statement or "").strip()
    focus_profile = build_problem_profile(
        focus_text or str(statement or "").strip(),
        goal_hypotheses=goal_hypotheses,
    )
    learning_domains = tuple(focus_profile.learning_domains) or tuple(
        root_profile.learning_domains
    )
    domain_family = (
        str(focus_profile.learning_family)
        if str(focus_profile.learning_family) != "general"
        else str(root_profile.learning_family)
    )
    return _OracleGoalProfile(
        statement_domain=str(root_profile.statement_domain),
        learning_domains=learning_domains,
        domain_family=domain_family,
        has_hypotheses=bool(focus_profile.has_hypotheses),
        has_arithmetic=bool(focus_profile.has_arithmetic),
        has_structure=bool(focus_profile.has_structure),
        has_negation=bool(focus_profile.has_negation),
        has_extensional=bool(focus_profile.has_extensional),
        has_equality=bool(focus_profile.has_equality),
        has_finite_objects=bool(focus_profile.has_finite_objects),
        has_measure=bool(focus_profile.has_measure),
        has_probability=bool(focus_profile.has_probability),
        has_analysis="analysis" in learning_domains,
    )


def _oracle_family_priority(profile: _OracleGoalProfile) -> Tuple[str, ...]:
    domain_priority = get_oracle_family_order_for_domains(
        profile.learning_domains,
        statement_domain=profile.statement_domain,
    )
    if profile.has_probability or profile.has_measure:
        return domain_priority or (
            "domain_specific",
            "analysis",
            "search",
            "structural",
            "simp",
            "negation",
            "arithmetic",
        )
    if profile.has_finite_objects:
        return domain_priority or (
            "domain_specific",
            "structural",
            "search",
            "simp",
            "analysis",
            "negation",
            "arithmetic",
        )
    if profile.domain_family in {"topology", "geometry", "linear_algebra"} or any(
        domain in {"topology", "geometry", "linear_algebra"}
        for domain in profile.learning_domains
    ):
        return domain_priority or (
            "domain_specific",
            "structural",
            "analysis",
            "search",
            "simp",
            "negation",
            "arithmetic",
        )
    if profile.has_arithmetic and any(
        domain in {"number_theory", "algebra"} for domain in profile.learning_domains
    ):
        return domain_priority or (
            "domain_specific",
            "arithmetic",
            "structural",
            "search",
            "negation",
            "simp",
            "analysis",
        )
    if profile.has_arithmetic:
        return (
            "arithmetic",
            "simp",
            "search",
            "structural",
            "domain_specific",
            "negation",
            "analysis",
        )
    if profile.has_negation:
        return (
            "negation",
            "domain_specific",
            "search",
            "structural",
            "simp",
            "analysis",
            "arithmetic",
        )
    if profile.has_structure or profile.has_extensional:
        return (
            "structural",
            "search",
            "domain_specific",
            "simp",
            "analysis",
            "negation",
            "arithmetic",
        )
    if profile.has_equality and not profile.has_hypotheses:
        return (
            "search",
            "simp",
            "structural",
            "domain_specific",
            "analysis",
            "arithmetic",
            "negation",
        )
    if profile.has_analysis:
        return domain_priority or (
            "analysis",
            "domain_specific",
            "search",
            "structural",
            "simp",
            "negation",
            "arithmetic",
        )
    return (
        "search",
        "domain_specific",
        "structural",
        "simp",
        "analysis",
        "negation",
        "arithmetic",
    )


def _family_specs_for_goal_profile(
    profile: _OracleGoalProfile,
) -> Dict[str, List[_OracleTacticSpec]]:
    specs_by_family: Dict[str, List[_OracleTacticSpec]] = {
        family: list(_ORACLE_SPECS_BY_FAMILY.get(family, ()))
        for family in _ORACLE_FAMILY_ORDER
    }
    core_tactics = {
        spec.tactic
        for family, specs in specs_by_family.items()
        if family != "domain_specific"
        for spec in specs
    }
    domain_specific_tactics = get_oracle_domain_specific_tactics(
        profile.learning_domains,
        statement_domain=profile.statement_domain,
    )
    specs_by_family["domain_specific"] = [
        _OracleTacticSpec(tactic, "tier3", "domain_specific")
        for tactic in domain_specific_tactics
        if tactic not in core_tactics
    ]
    if profile.has_measure:
        analysis = specs_by_family.get("analysis", [])
        specs_by_family["analysis"] = [
            *[spec for spec in analysis if spec.tactic == "measurability"],
            *[spec for spec in analysis if spec.tactic != "measurability"],
        ]
    elif profile.domain_family == "topology" or "topology" in profile.learning_domains:
        analysis = specs_by_family.get("analysis", [])
        specs_by_family["analysis"] = [
            *[spec for spec in analysis if spec.tactic == "continuity"],
            *[spec for spec in analysis if spec.tactic != "continuity"],
        ]
    if profile.has_extensional and profile.has_equality:
        structural = specs_by_family.get("structural", [])
        specs_by_family["structural"] = [
            *[spec for spec in structural if spec.tactic.startswith("ext;")],
            *[spec for spec in structural if not spec.tactic.startswith("ext;")],
        ]
    return specs_by_family


_PROP_FRAGMENT_FORBIDDEN_RE = re.compile(
    r"\b(?:"
    r"Set|Type|Sort|Nat|Int|Rat|Real|Complex|NNReal|ENNReal|"
    r"Matrix|Finset|Fintype|List|Multiset|Array|Vector|Subtype|Submodule|"
    r"Polynomial|Ideal|Ring|Field|Group|Monoid|MeasureTheory|ProbabilityTheory|"
    r"Filter|TopologicalSpace|Metric|Continuous|Differentiable|Measurable|IsOpen|IsClosed"
    r")\b"
    r"|[∈⊆∪∩≤≥+\*/]"
)


def _prop_complete_applicable(
    statement: str,
    *,
    goal_text: str | None = None,
    goal_hypotheses: Sequence[str] = (),
) -> bool:
    """Conservative gate for proposition-only tactics like ``prop_complete``.

    The goal and its local hypotheses must look like propositional logic, not
    set/algebra/analysis formulas. We accept both Unicode and ASCII logical
    syntax so telemetry and scheduling behave the same on parsed and synthetic
    goal text.
    """
    snippets = [
        str(goal_text or statement or "").strip(),
        *[str(h).strip() for h in goal_hypotheses if str(h).strip()],
    ]
    combined = "\n".join(part for part in snippets if part)
    focus = str(goal_text or statement or "").strip()
    if not combined:
        return False
    if is_standalone_sort_like_lean_expr(focus):
        return False
    if not (_PROP_LOGIC_RE.search(combined) or "Prop" in combined):
        return False
    if _NONPROP_BINDER_RE.search(combined):
        return False
    if _BARE_QUANTIFIER_RE.search(focus) and "Prop" not in focus:
        return False
    return not _PROP_FRAGMENT_FORBIDDEN_RE.search(combined)


def _goal_aware_opt_in_specs(
    profile: _OracleGoalProfile,
    *,
    tactic_oracle_cfg: "Optional[TacticOracleConfig]" = None,
) -> List[_OracleTacticSpec]:
    enabled_flags = enabled_opt_in_tactics_from_config(tactic_oracle_cfg)
    if not enabled_flags:
        return []
    return [
        _OracleTacticSpec(tactic, "tier5", "opt_in")
        for tactic in get_domain_opt_in_tactics(
            profile.learning_domains,
            statement_domain=profile.statement_domain,
            enabled_opt_in_tactics=enabled_flags,
        )
    ]


def _goal_aware_oracle_specs(
    statement: str,
    *,
    goal_text: str | None = None,
    goal_hypotheses: Sequence[str] = (),
    tactic_oracle_cfg: "Optional[TacticOracleConfig]" = None,
) -> Tuple[_OracleTacticSpec, ...]:
    profile = _build_oracle_goal_profile(
        statement,
        goal_text=goal_text,
        goal_hypotheses=goal_hypotheses,
    )
    priority = list(_oracle_family_priority(profile))
    for family in _ORACLE_FAMILY_ORDER:
        if family not in priority:
            priority.append(family)

    family_specs = _family_specs_for_goal_profile(profile)
    queues: Dict[str, List[_OracleTacticSpec]] = {
        family: list(family_specs.get(family, ())) for family in priority
    }
    ordered: List[_OracleTacticSpec] = []

    primary_family = priority[0] if priority else None
    secondary_family = priority[1] if len(priority) > 1 else None
    if primary_family:
        burst_size = 1 if primary_family == "search" else 2
        for _ in range(burst_size):
            if queues[primary_family]:
                ordered.append(queues[primary_family].pop(0))

    # Front-load chained tier3 tactics from the primary and secondary
    # families immediately after the burst.  Without this, the round-robin
    # interleaves tier2 specs from every family, consuming the wall-clock
    # budget before any chained tactic is reached.
    for _fl_family in (primary_family, secondary_family):
        if _fl_family is None or _fl_family == "search":
            continue
        queue = queues[_fl_family]
        front_loaded = 0
        _remaining: List[_OracleTacticSpec] = []
        for spec in queue:
            if front_loaded < 3 and (";" in spec.tactic or "<;>" in spec.tactic):
                ordered.append(spec)
                front_loaded += 1
            else:
                _remaining.append(spec)
        queues[_fl_family] = _remaining

    defer_primary_once = primary_family == "search"
    while True:
        progressed = False
        families_this_round = list(priority)
        if defer_primary_once and primary_family is not None:
            families_this_round = [
                f for f in families_this_round if f != primary_family
            ] + [primary_family]
            defer_primary_once = False
        for family in families_this_round:
            queue = queues[family]
            if not queue:
                continue
            ordered.append(queue.pop(0))
            progressed = True
        if not progressed:
            break
    deduped: List[_OracleTacticSpec] = []
    seen_tactics: set[str] = set()
    for spec in ordered:
        if spec.tactic in seen_tactics:
            continue
        seen_tactics.add(spec.tactic)
        deduped.append(spec)
    for spec in _goal_aware_opt_in_specs(
        profile,
        tactic_oracle_cfg=tactic_oracle_cfg,
    ):
        if spec.tactic in seen_tactics:
            continue
        seen_tactics.add(spec.tactic)
        deduped.append(spec)
    return tuple(deduped)


@dataclass
class LeanResult:
    ok: bool
    output: str
    file_path: str
    returncode: int = 1
    parsed: Optional[LeanParseResult] = field(default=None, repr=False)
    axiom_audit_ok: Optional[bool] = None
    axiom_audit: Dict[str, Tuple[str, ...]] = field(default_factory=dict)
    unexpected_axioms: Tuple[str, ...] = ()
    axiom_audit_error: str = ""
    generated_declaration_name: str = ""
    generated_goal_start_line: int = 0
    generated_lemma_line_spans: Tuple[Tuple[int, int], ...] = ()


@dataclass(frozen=True)
class LeanStatementContractAnalysis:
    """Lean-authoritative identity and leading-binder classification.

    ``display_type`` is diagnostic-only pretty-printer output.  Mathematical
    identity is the versioned hash of ``Expr`` JSON emitted before
    delaboration, so notation such as ``ℝ[X]`` can never become an identity
    boundary. ``binder_sorts`` follows the elaborated outer Pi telescope after
    one initial head reduction. It covers binders after implication arrows but
    deliberately stops at the theorem conclusion instead of unfolding a
    reducible proposition such as ``Filter.Tendsto`` into implementation
    binders.
    """

    display_type: str = ""
    structural_identity: str = ""
    binder_sorts: tuple[str, ...] = ()
    # Display types for every binder in ``binder_sorts``.  Consumers must use
    # these only to select a conservative witness catalogue; ``binder_sorts``
    # and ``structural_identity`` remain the Lean-authoritative boundaries.
    binder_types: tuple[str, ...] = ()
    binder_normalized_types: tuple[str, ...] = ()
    proof_binder_types: tuple[str, ...] = ()
    # Full Expr hashes for proof-binder domains after Lean head reduction.
    # Unlike ``proof_binder_types`` these remain authoritative across reducible
    # aliases and pretty-printer notation.  Hashes containing local variables
    # naturally fail to match standalone closed helpers and fall back to the
    # existing contextual contract analysis.
    proof_binder_structural_hashes: tuple[str, ...] = ()
    # Structural hash of the proposition remaining after independent leading
    # proof binders are erased. This supports Lean-authoritative forward
    # chaining (`H → C` plus `H` supplies `C`) without trusting display text.
    # Empty means the conclusion is proof-dependent or otherwise unavailable.
    contract_conclusion_structural_hash: str = ""
    # Zero-based indices in the same analyzer batch whose elaborated
    # proposition types Lean accepted as definitionally equal.  Structural
    # hashes remain stable standalone identities; this batch-local relation
    # closes reducible aliases nested below the outer weak-head boundary.
    definitionally_equal_indices: tuple[int, ...] = ()
    # Same batch relation after Lean removes only leading proof binders while
    # retaining every data binder.  This recognizes executable assemblies
    # such as ``H → MyRoot`` against ``Root`` when ``MyRoot`` is reducible,
    # while proof-dependent propositions remain deliberately incomparable.
    contract_definitionally_equal_indices: tuple[int, ...] = ()
    definitionally_checked_indices: tuple[int, ...] = ()
    contract_definitionally_checked_indices: tuple[int, ...] = ()
    # Per-invocation timings are carried with the returned structural receipt
    # instead of sampled from LeanRunner's process-wide cumulative counters.
    # This keeps overlapping contract batches from charging each other's work.
    operation_telemetry: Mapping[str, Any] = field(
        default_factory=dict,
        repr=False,
        compare=False,
    )

    @property
    def elaborated(self) -> bool:
        return bool(self.structural_identity)


_LEAN_RESIDUAL_BATCH_FORMAT_VERSION = 2
_LEAN_RESIDUAL_BATCH_MAX_GOALS = 256
_LEAN_RESIDUAL_SOURCE_MAX_CHARS = 1_000_000
LEAN_RESIDUAL_VERIFIER_GENERATION = (
    f"lean-residual-batch-v{_LEAN_RESIDUAL_BATCH_FORMAT_VERSION}"
)


def lean_residual_elaboration_context_hash(
    lean: Any,
    *,
    preamble_override: str | None,
    ordered_lemmas: Sequence[str],
    proof_code: str,
) -> str:
    """Hash the exact environment used by typed residual extraction.

    This is intentionally route-specific: ``_resolve_preamble`` may add
    imports selected by the parent proof stub, in addition to configured
    preamble tactics.  Runtime dispatch validation and receipt production
    must call this same function or a valid receipt can be misclassified as
    stale immediately after admission.
    """

    resolver = getattr(lean, "_resolve_preamble", None)
    if callable(resolver):
        resolved_preamble = str(
            resolver(preamble_override, proof_code=str(proof_code or "")) or ""
        )
    else:
        cfg = getattr(lean, "cfg", None)
        base = (
            preamble_override
            if preamble_override is not None
            else str(getattr(cfg, "preamble_import", "") or "")
        )
        required_imports: Tuple[str, ...] = ()
        if re.search(r"\bprop_complete\b", str(proof_code or "")):
            raw_imports = getattr(cfg, "extra_imports", ())
            if isinstance(raw_imports, (list, tuple)):
                normalized_imports: List[str] = []
                for item in raw_imports:
                    text = str(item or "").strip()
                    if text.startswith("import "):
                        text = text[len("import ") :].strip()
                    if text:
                        normalized_imports.append(text)
                required_imports = tuple(normalized_imports)
        resolved_preamble = _append_imports_to_preamble(base, required_imports)
        tactics = str(getattr(cfg, "preamble_tactics", "") or "").strip()
        if tactics:
            resolved_preamble = resolved_preamble.rstrip() + "\n\n" + tactics + "\n"
    return hash_text(
        json.dumps(
            {
                "format": _LEAN_RESIDUAL_BATCH_FORMAT_VERSION,
                "resolved_preamble": resolved_preamble,
                "ordered_lemmas": [str(item or "") for item in ordered_lemmas],
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    )


@dataclass(frozen=True)
class LeanResidualGoalReceipt:
    """Lean-authoritative, independently replayed source for one open goal.

    ``statement`` is executable input. ``canonical_expr_json`` is the
    closed elaborated ``Expr`` captured before delaboration and canonicalized
    by Python after strict schema/open-expression validation. Neither field is
    reconstructed from Lean's human goal diagnostics.
    """

    slot_index: int
    slot_count: int
    statement: str
    statement_sha256: str
    canonical_expr_json: str
    expr_hash: str
    structural_identity: str

    def to_record(self) -> dict[str, Any]:
        return {
            "slot_index": self.slot_index,
            "slot_count": self.slot_count,
            "statement": self.statement,
            "statement_sha256": self.statement_sha256,
            "canonical_expr_json": self.canonical_expr_json,
            "expr_hash": self.expr_hash,
            "structural_identity": self.structural_identity,
        }


@dataclass(frozen=True)
class LeanResidualBatchReceipt:
    """Atomic residual-goal evidence emitted by one Lean command."""

    format_version: int
    marker_nonce: str
    parent_statement_sha256: str
    parent_canonical_expr_json: str
    parent_expr_hash: str
    parent_structural_identity: str
    proof_stub_sha256: str
    elaboration_context_hash: str
    goals: tuple[LeanResidualGoalReceipt, ...]
    batch_digest: str

    def to_record(self) -> dict[str, Any]:
        return {
            "format_version": self.format_version,
            "marker_nonce": self.marker_nonce,
            "parent_statement_sha256": self.parent_statement_sha256,
            "parent_canonical_expr_json": self.parent_canonical_expr_json,
            "parent_expr_hash": self.parent_expr_hash,
            "parent_structural_identity": self.parent_structural_identity,
            "proof_stub_sha256": self.proof_stub_sha256,
            "elaboration_context_hash": self.elaboration_context_hash,
            "goals": [goal.to_record() for goal in self.goals],
            "batch_digest": self.batch_digest,
        }


@dataclass(frozen=True)
class LeanResidualBatchResult:
    """Fail-closed result of extracting typed residual goals."""

    ok: bool
    receipt: Optional[LeanResidualBatchReceipt]
    output: str
    returncode: int
    file_path: str = ""
    error: str = ""
    failure_phase: str = ""
    failure_kind: str = ""
    failure_fingerprint: str = ""
    diagnostic_preview: str = ""
    attempted: bool = False


def _residual_failure_evidence(
    phase: str,
    kind: str,
    output: str,
) -> tuple[str, str]:
    """Return stable, bounded private evidence for verifier retry identity.

    Nonces, temporary paths, source locations, and generated metavariable ids
    are deliberately normalized so a deterministic backend failure remains
    the same durable fingerprint after process/session recreation.
    """

    normalized = str(output or "").replace("\x00", "")
    normalized = re.sub(
        r"(?m)^.*MINI_RESIDUAL_BATCH_[0-9a-f]+:.*$",
        "MINI_RESIDUAL_BATCH_<nonce>:<payload>",
        normalized,
    )
    normalized = re.sub(
        r"MINI_RESIDUAL_(?:PROOF_REJECTION|POSTPROCESS_FAILURE)_[0-9a-f]+",
        "MINI_RESIDUAL_FAILURE_<nonce>",
        normalized,
    )
    normalized = re.sub(r"miniResidual_[0-9a-f]+", "miniResidual_<nonce>", normalized)
    normalized = re.sub(
        r"residual_receipt_[A-Za-z0-9_'-]+",
        "residual_receipt_<id>",
        normalized,
    )
    normalized = re.sub(r"(?:/[^\s:]+)+\.lean", "<lean-file>.lean", normalized)
    normalized = re.sub(r"(?m)(?<=\.lean):\d+:\d+", ":<line>:<col>", normalized)
    normalized = re.sub(r"\?m\.\d+", "?m.<id>", normalized)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    preview = f"{str(phase or '')}:{str(kind or '')}"[:480]
    fingerprint = hash_text(
        json.dumps(
            {
                "phase": str(phase or ""),
                "kind": str(kind or ""),
                "diagnostic": normalized[:4096],
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    )
    return fingerprint, preview


_JSON_NUMBER_TOKEN_RE = re.compile(
    r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?"
)


def _decode_json_iterative(source: str) -> Any:
    """Decode JSON with an explicit container stack.

    Lean expressions are naturally much deeper than Python call stacks. The
    standard decoder rejects otherwise valid, bounded receipt payloads around
    that implementation limit, so the receipt boundary uses a non-recursive
    decoder rather than imposing a mathematical expression-depth cap.
    """

    text = str(source)
    length = len(text)
    position = 0
    unset = object()
    root: Any = unset
    # frame: [kind, container, state, pending_key]
    stack: list[list[Any]] = []

    def skip_space(index: int) -> int:
        while index < length and text[index] in " \t\r\n":
            index += 1
        return index

    def parse_value(index: int) -> tuple[Any, Optional[list[Any]], int]:
        index = skip_space(index)
        if index >= length:
            raise ValueError("unexpected end of JSON input")
        token = text[index]
        if token == "[":
            container: list[Any] = []
            return container, ["array", container, "value_or_end", None], index + 1
        if token == "{":
            container = {}
            return container, ["object", container, "key_or_end", None], index + 1
        if token == '"':
            value, end = json.decoder.scanstring(text, index + 1, True)
            return value, None, end
        for literal, value in (("true", True), ("false", False), ("null", None)):
            if text.startswith(literal, index):
                return value, None, index + len(literal)
        match = _JSON_NUMBER_TOKEN_RE.match(text, index)
        if match is None:
            raise ValueError(f"invalid JSON token at offset {index}")
        token_text = match.group(0)
        value = (
            float(token_text)
            if any(marker in token_text for marker in ".eE")
            else int(token_text)
        )
        return value, None, match.end()

    while True:
        position = skip_space(position)
        if not stack:
            if root is not unset:
                if position != length:
                    raise ValueError(f"trailing JSON data at offset {position}")
                return root
            root, frame, position = parse_value(position)
            if frame is not None:
                stack.append(frame)
            continue

        frame = stack[-1]
        kind, container, state, pending_key = frame
        position = skip_space(position)
        if kind == "array":
            if state in {"value_or_end", "value"}:
                if (
                    state == "value_or_end"
                    and position < length
                    and text[position] == "]"
                ):
                    stack.pop()
                    position += 1
                    continue
                value, child_frame, position = parse_value(position)
                container.append(value)
                frame[2] = "comma_or_end"
                if child_frame is not None:
                    stack.append(child_frame)
                continue
            if position < length and text[position] == ",":
                frame[2] = "value"
                position += 1
                continue
            if position < length and text[position] == "]":
                stack.pop()
                position += 1
                continue
            raise ValueError(f"expected ',' or ']' at offset {position}")

        if state in {"key_or_end", "key"}:
            if (
                state == "key_or_end"
                and position < length
                and text[position] == "}"
            ):
                stack.pop()
                position += 1
                continue
            if position >= length or text[position] != '"':
                raise ValueError(f"expected object key at offset {position}")
            key, position = json.decoder.scanstring(text, position + 1, True)
            frame[3] = key
            frame[2] = "colon"
            continue
        if state == "colon":
            if position >= length or text[position] != ":":
                raise ValueError(f"expected ':' at offset {position}")
            frame[2] = "value"
            position += 1
            continue
        if state == "value":
            value, child_frame, position = parse_value(position)
            if pending_key in container:
                raise ValueError(f"duplicate object key {pending_key!r}")
            container[pending_key] = value
            frame[3] = None
            frame[2] = "comma_or_end"
            if child_frame is not None:
                stack.append(child_frame)
            continue
        if position < length and text[position] == ",":
            frame[2] = "key"
            position += 1
            continue
        if position < length and text[position] == "}":
            stack.pop()
            position += 1
            continue
        raise ValueError(f"expected ',' or '}}' at offset {position}")


def _is_nonnegative_json_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _lean_serialized_level_is_closed(value: Any) -> bool:
    stack = [value]
    while stack:
        item = stack.pop()
        if not isinstance(item, list) or not item or not isinstance(item[0], str):
            return False
        tag = item[0]
        if tag == "zero":
            if len(item) != 1:
                return False
        elif tag == "succ":
            if len(item) != 2:
                return False
            stack.append(item[1])
        elif tag in {"max", "imax"}:
            if len(item) != 3:
                return False
            stack.extend((item[1], item[2]))
        elif tag == "param":
            if len(item) != 2 or not isinstance(item[1], str) or not item[1]:
                return False
        else:
            # Universe metavariables are open evidence, even if Lean happened
            # to assign a similarly named metavariable elsewhere.
            return False
    return True


def _lean_serialized_expr_is_closed(value: Any, *, depth: int = 0) -> bool:
    """Validate the exact serializer grammar and reject every open ``Expr``."""
    stack: list[tuple[Any, int]] = [(value, depth)]
    binder_infos = {"default", "implicit", "strictImplicit", "instImplicit"}
    while stack:
        item, item_depth = stack.pop()
        if not isinstance(item, list) or not item or not isinstance(item[0], str):
            return False
        tag = item[0]
        if tag == "bvar":
            if not (
                len(item) == 2
                and _is_nonnegative_json_int(item[1])
                and item[1] < item_depth
            ):
                return False
        elif tag in {"fvar", "mvar"}:
            return False
        elif tag == "sort":
            if len(item) != 2 or not _lean_serialized_level_is_closed(item[1]):
                return False
        elif tag == "const":
            if not (
                len(item) == 3
                and isinstance(item[1], str)
                and item[1]
                and isinstance(item[2], list)
                and all(_lean_serialized_level_is_closed(level) for level in item[2])
            ):
                return False
        elif tag == "app":
            if len(item) != 3:
                return False
            stack.extend(((item[1], item_depth), (item[2], item_depth)))
        elif tag in {"lam", "forall"}:
            if len(item) != 4 or item[1] not in binder_infos:
                return False
            stack.extend(((item[2], item_depth), (item[3], item_depth + 1)))
        elif tag == "let":
            if len(item) != 5 or not isinstance(item[1], bool):
                return False
            stack.extend(
                (
                    (item[2], item_depth),
                    (item[3], item_depth),
                    (item[4], item_depth + 1),
                )
            )
        elif tag == "lit":
            if len(item) != 2 or not isinstance(item[1], list) or len(item[1]) != 2:
                return False
            literal = item[1]
            if not (
                (literal[0] == "nat" and _is_nonnegative_json_int(literal[1]))
                or (literal[0] == "str" and isinstance(literal[1], str))
            ):
                return False
        elif tag == "proj":
            if not (
                len(item) == 4
                and isinstance(item[1], str)
                and item[1]
                and _is_nonnegative_json_int(item[2])
            ):
                return False
            stack.append((item[3], item_depth))
        else:
            return False
    return True


def _canonical_residual_expr_json(expr: Any) -> str:
    """Canonical Expr JSON without Python-recursive traversal/encoding."""

    level_params: dict[str, str] = {}
    output: list[str] = []
    stack: list[tuple[str, Any]] = [("value", expr)]
    while stack:
        operation, item = stack.pop()
        if operation == "raw":
            output.append(str(item))
            continue
        if isinstance(item, list):
            if (
                len(item) == 2
                and item[0] == "param"
                and isinstance(item[1], str)
            ):
                item = [
                    "param",
                    level_params.setdefault(item[1], f"u{len(level_params)}"),
                ]
            output.append("[")
            stack.append(("raw", "]"))
            operations: list[tuple[str, Any]] = []
            for index, child in enumerate(item):
                if index:
                    operations.append(("raw", ","))
                operations.append(("value", child))
            stack.extend(reversed(operations))
            continue
        if isinstance(item, dict):
            entries = sorted(item.items(), key=lambda pair: str(pair[0]))
            output.append("{")
            stack.append(("raw", "}"))
            operations = []
            for index, (key, child) in enumerate(entries):
                if index:
                    operations.append(("raw", ","))
                operations.extend(
                    (
                        ("raw", json.dumps(str(key), ensure_ascii=True)),
                        ("raw", ":"),
                        ("value", child),
                    )
                )
            stack.extend(reversed(operations))
            continue
        output.append(json.dumps(item, ensure_ascii=True, separators=(",", ":")))
    return "".join(output)


def _residual_expr_identity(canonical_expr_json: str) -> tuple[str, str]:
    expr_hash = hash_text(
        "{\"expr\":"
        + canonical_expr_json
        + ",\"format\":"
        + json.dumps(_CONTRACT_ANALYSIS_FORMAT_VERSION, ensure_ascii=True)
        + "}"
    )
    return (
        expr_hash,
        make_lean_contract_identity(
            expr_hash,
            None,
            version=_CONTRACT_ANALYSIS_FORMAT_VERSION,
        ),
    )


def _residual_batch_receipt_from_payload(
    payload: Any,
    *,
    marker_nonce: str,
    parent_statement_sha256: str,
    proof_stub_sha256: str,
    elaboration_context_hash: str,
) -> tuple[Optional[LeanResidualBatchReceipt], str]:
    """Validate one nonce-authenticated Lean payload without partial salvage."""

    if not isinstance(payload, Mapping):
        return None, "residual_marker_payload_not_object"
    if set(payload) != {"version", "parentExpr", "goals"}:
        return None, "residual_marker_payload_schema_mismatch"
    if payload.get("version") != _LEAN_RESIDUAL_BATCH_FORMAT_VERSION:
        return None, "residual_marker_version_mismatch"
    parent_expr = payload.get("parentExpr")
    if not _lean_serialized_expr_is_closed(parent_expr):
        return None, "residual_parent_expr_open_or_malformed"
    raw_goals = payload.get("goals")
    if not isinstance(raw_goals, list):
        return None, "residual_goals_not_array"
    if len(raw_goals) > _LEAN_RESIDUAL_BATCH_MAX_GOALS:
        return None, "residual_goal_count_exceeds_limit"

    parent_expr_json = _canonical_residual_expr_json(parent_expr)
    parent_expr_hash, parent_identity = _residual_expr_identity(parent_expr_json)
    if not parent_identity:
        return None, "residual_parent_identity_unavailable"

    slot_count = len(raw_goals)
    goals: list[LeanResidualGoalReceipt] = []
    for expected_slot, raw_goal in enumerate(raw_goals):
        if not isinstance(raw_goal, Mapping):
            return None, "residual_goal_payload_not_object"
        if set(raw_goal) != {"slot", "source", "expr"}:
            return None, "residual_goal_payload_schema_mismatch"
        slot = raw_goal.get("slot")
        # Requiring emitted array order to be the canonical slot order rejects
        # duplicates, gaps, and reorder attacks in one check.
        if not _is_nonnegative_json_int(slot) or slot != expected_slot:
            return None, "residual_goal_slots_not_contiguous"
        source = raw_goal.get("source")
        if (
            not isinstance(source, str)
            or not source.strip()
            or len(source) > _LEAN_RESIDUAL_SOURCE_MAX_CHARS
        ):
            return None, "residual_goal_source_missing_or_oversize"
        expr = raw_goal.get("expr")
        if not _lean_serialized_expr_is_closed(expr):
            return None, "residual_goal_expr_open_or_malformed"
        expr_json = _canonical_residual_expr_json(expr)
        expr_hash, structural_identity = _residual_expr_identity(expr_json)
        if not structural_identity:
            return None, "residual_goal_identity_unavailable"
        goals.append(
            LeanResidualGoalReceipt(
                slot_index=expected_slot,
                slot_count=slot_count,
                statement=source,
                statement_sha256=hash_text(source),
                canonical_expr_json=expr_json,
                expr_hash=expr_hash,
                structural_identity=structural_identity,
            )
        )

    digest_payload = {
        "format_version": _LEAN_RESIDUAL_BATCH_FORMAT_VERSION,
        "parent_statement_sha256": parent_statement_sha256,
        "parent_canonical_expr_json": parent_expr_json,
        "parent_expr_hash": parent_expr_hash,
        "parent_structural_identity": parent_identity,
        "proof_stub_sha256": proof_stub_sha256,
        "elaboration_context_hash": elaboration_context_hash,
        "goals": [goal.to_record() for goal in goals],
    }
    batch_digest = hash_text(
        json.dumps(
            digest_payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    )
    return (
        LeanResidualBatchReceipt(
            format_version=_LEAN_RESIDUAL_BATCH_FORMAT_VERSION,
            marker_nonce=str(marker_nonce or ""),
            parent_statement_sha256=parent_statement_sha256,
            parent_canonical_expr_json=parent_expr_json,
            parent_expr_hash=parent_expr_hash,
            parent_structural_identity=parent_identity,
            proof_stub_sha256=proof_stub_sha256,
            elaboration_context_hash=elaboration_context_hash,
            goals=tuple(goals),
            batch_digest=batch_digest,
        ),
        "",
    )


def _axiom_report_name_matches(reported: str, requested: str) -> bool:
    reported_name = str(reported or "").strip()
    requested_name = str(requested or "").strip()
    # `#print axioms` may pretty-print an escaped identifier without its
    # guillemets when the surrounding qualified name makes it unambiguous
    # (for example `MiniQuoted.«lemma»` is reported as
    # `MiniQuoted.lemma`). Match that presentation to the exact declaration
    # name we emitted, while keeping the existing namespace-suffix behavior.
    requested_pretty_name = re.sub(
        r"«([^»\n]+)»",
        lambda match: str(match.group(1) or ""),
        requested_name,
    )
    return bool(
        reported_name == requested_name
        or reported_name == requested_pretty_name
        or (
            requested_name
            and reported_name.endswith(f".{requested_name}")
        )
        or (
            requested_pretty_name
            and reported_name.endswith(f".{requested_pretty_name}")
        )
    )


def _parse_complete_axiom_audit(
    output: str,
    requested_names: Sequence[str],
) -> tuple[Dict[str, Tuple[str, ...]], str]:
    """Parse one complete ``#print axioms`` report per requested declaration."""

    reports: List[tuple[str, Tuple[str, ...]]] = []
    for match in _PRINT_AXIOMS_DEPENDS_RE.finditer(str(output or "")):
        reports.append(
            (
                str(match.group(1) or "").strip(),
                tuple(
                    item.strip()
                    for item in str(match.group(2) or "").split(",")
                    if item.strip()
                ),
            )
        )
    for match in _PRINT_AXIOMS_NONE_RE.finditer(str(output or "")):
        reports.append((str(match.group(1) or "").strip(), ()))

    unused = list(reports)
    parsed: Dict[str, Tuple[str, ...]] = {}
    missing: List[str] = []
    requested = dict.fromkeys(
        str(name or "").strip()
        for name in requested_names
        if str(name or "").strip()
    )
    for requested_name in requested:
        matched_index = None
        matched_axioms: Tuple[str, ...] = ()
        for position, (reported, axioms) in enumerate(unused):
            if _axiom_report_name_matches(reported, requested_name):
                matched_index = position
                matched_axioms = tuple(axioms)
                break
        if matched_index is None:
            missing.append(requested_name)
            continue
        unused.pop(matched_index)
        parsed[requested_name] = matched_axioms
    if missing:
        return parsed, "missing_axiom_report:" + ",".join(missing)
    return parsed, ""


_CONTRACT_ANALYSIS_FORMAT_VERSION = LEAN_CONTRACT_IDENTITY_VERSION


def _canonical_contract_expr_payload(value: Any) -> Any:
    """Canonicalize universe-parameter names in serialized Lean ``Expr`` JSON."""

    level_params: dict[str, str] = {}

    def visit(item: Any) -> Any:
        if isinstance(item, list):
            if (
                len(item) == 2
                and item[0] == "param"
                and isinstance(item[1], str)
            ):
                normalized = level_params.setdefault(
                    item[1], f"u{len(level_params)}"
                )
                return ["param", normalized]
            return [visit(child) for child in item]
        if isinstance(item, dict):
            return {
                str(key): visit(child)
                for key, child in sorted(item.items(), key=lambda pair: str(pair[0]))
            }
        return item

    return visit(value)


def _contract_expr_has_open_universe(value: Any) -> bool:
    """Whether a component Expr carries a non-concrete universe level.

    Premise/conclusion hashes are compared independently during structural
    forward chaining. Independently alpha-normalizing universe parameters
    would erase the correlation in `A.{u} → B.{u}` and could combine an
    `A.{u}` premise with a `B.{v}` consumer. Whole-statement identities retain
    their existing universe-alpha semantics; component support evidence fails
    closed whenever such cross-component correlation may matter.
    """

    if isinstance(value, list):
        if (
            len(value) >= 1
            and isinstance(value[0], str)
            and value[0] in {"param", "mvar"}
        ):
            return True
        return any(_contract_expr_has_open_universe(item) for item in value)
    if isinstance(value, dict):
        return any(
            _contract_expr_has_open_universe(item)
            for item in value.values()
        )
    return False


def _shift_contract_bvars_after_removed_binder(
    expr: Any,
    *,
    depth: int = 0,
) -> Any | None:
    """Remove one enclosing de Bruijn slot, failing if its proof is referenced."""

    if not isinstance(expr, list) or not expr:
        return expr
    tag = expr[0]
    if (
        isinstance(tag, str)
        and tag == "bvar"
        and len(expr) == 2
        and isinstance(expr[1], int)
    ):
        index = expr[1]
        if index == depth:
            return None
        return ["bvar", index - 1 if index > depth else index]
    if isinstance(tag, str) and tag in {"forall", "lam"} and len(expr) == 4:
        domain = _shift_contract_bvars_after_removed_binder(
            expr[2],
            depth=depth,
        )
        body = _shift_contract_bvars_after_removed_binder(
            expr[3],
            depth=depth + 1,
        )
        if domain is None or body is None:
            return None
        return [tag, expr[1], domain, body]
    if isinstance(tag, str) and tag == "let" and len(expr) == 5:
        type_expr = _shift_contract_bvars_after_removed_binder(
            expr[2],
            depth=depth,
        )
        value = _shift_contract_bvars_after_removed_binder(
            expr[3],
            depth=depth,
        )
        body = _shift_contract_bvars_after_removed_binder(
            expr[4],
            depth=depth + 1,
        )
        if type_expr is None or value is None or body is None:
            return None
        return [tag, expr[1], type_expr, value, body]
    shifted: list[Any] = [tag]
    for child in expr[1:]:
        normalized = _shift_contract_bvars_after_removed_binder(
            child,
            depth=depth,
        )
        if normalized is None:
            return None
        shifted.append(normalized)
    return shifted


def _proof_erased_contract_expr(
    expr: Any,
    binder_sorts: Sequence[str],
) -> Any | None:
    """Erase leading proof Pi binders while preserving data telescope structure.

    This gives root-route matching a Lean-derived conclusion profile.  It
    equates an assembly ``H → root`` with ``root`` without letting surface
    normalization erase genuine type differences in their conclusions.
    Proof-dependent types deliberately have no profile and therefore fail
    closed unless their complete structural identities match.
    """

    sorts = tuple(str(item or "").strip().lower() for item in binder_sorts)

    def visit(node: Any, index: int) -> tuple[Any | None, int]:
        if index >= len(sorts):
            return node, index
        if (
            not isinstance(node, list)
            or len(node) != 4
            or node[0] != "forall"
        ):
            return None, index
        body, next_index = visit(node[3], index + 1)
        if body is None:
            return None, next_index
        if sorts[index] == "proof":
            return (
                _shift_contract_bvars_after_removed_binder(body),
                next_index,
            )
        if sorts[index] != "data":
            return None, next_index
        return ["forall", node[1], node[2], body], next_index

    normalized, consumed = visit(expr, 0)
    if normalized is None or consumed != len(sorts):
        return None
    return normalized


def _contract_analysis_from_payload(
    payload: Any,
    *,
    display_type: str,
) -> LeanStatementContractAnalysis:
    if not isinstance(payload, dict):
        return LeanStatementContractAnalysis(display_type=display_type)
    payload_format = payload.get("format")
    if payload_format not in {2, _CONTRACT_ANALYSIS_FORMAT_VERSION}:
        return LeanStatementContractAnalysis(display_type=display_type)
    expr = payload.get("expr")
    if expr is None:
        return LeanStatementContractAnalysis(display_type=display_type)
    canonical_expr = _canonical_contract_expr_payload(expr)
    full_identity_payload = json.dumps(
        {
            "format": payload_format,
            "expr": canonical_expr,
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )
    raw_binders = payload.get("binders")
    if not isinstance(raw_binders, list):
        return LeanStatementContractAnalysis(display_type=display_type)
    binders = raw_binders
    binder_sorts: list[str] = []
    binder_types: list[str] = []
    binder_normalized_types: list[str] = []
    proof_binder_types: list[str] = []
    proof_binder_structural_hashes: list[str] = []
    for binder in binders:
        if not isinstance(binder, dict):
            return LeanStatementContractAnalysis(display_type=display_type)
        binder_sort = str(binder.get("sort") or "").strip().lower()
        if binder_sort not in {"proof", "data"}:
            return LeanStatementContractAnalysis(display_type=display_type)
        rendered = str(binder.get("type") or "").strip()
        if not rendered:
            return LeanStatementContractAnalysis(display_type=display_type)
        binder_sorts.append(binder_sort)
        binder_types.append(rendered)
        binder_normalized_types.append(
            str(binder.get("normalizedType") or rendered).strip()
        )
        if binder_sort == "proof":
            proof_binder_types.append(rendered)
            binder_expr = binder.get("expr")
            if binder_expr is None:
                proof_binder_structural_hashes.append("")
            else:
                canonical_binder_expr = _canonical_contract_expr_payload(
                    binder_expr
                )
                proof_binder_structural_hashes.append(
                    ""
                    if _contract_expr_has_open_universe(
                        canonical_binder_expr
                    )
                    else hash_text(
                        json.dumps(
                            {
                                "format": payload_format,
                                "expr": canonical_binder_expr,
                            },
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=True,
                        )
                    )
                )
    contract_expr = _proof_erased_contract_expr(
        canonical_expr,
        binder_sorts,
    )
    contract_profile_hash = None
    contract_conclusion_structural_hash = ""
    if contract_expr is not None:
        # Proof-only premises may introduce universe parameters before the
        # retained data telescope. Re-alpha-normalize after erasure so those
        # discarded parameters cannot renumber an otherwise identical profile.
        contract_expr = _canonical_contract_expr_payload(contract_expr)
        contract_profile_payload = json.dumps(
            {
                "format": payload_format,
                "contract_expr": contract_expr,
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        contract_profile_hash = hash_text(contract_profile_payload)
        # Only a proof-only telescope yields a closed proposition conclusion.
        # Data binders retain local-variable context and continue through the
        # existing contextual surface/Lean checks instead of manufacturing a
        # standalone support proposition.
        conclusion_expr = payload.get("contractConclusionExpr")
        if (
            all(sort == "proof" for sort in binder_sorts)
            and conclusion_expr is not None
        ):
            canonical_conclusion_expr = _canonical_contract_expr_payload(
                conclusion_expr
            )
            if not _contract_expr_has_open_universe(
                canonical_conclusion_expr
            ):
                contract_conclusion_structural_hash = hash_text(
                    json.dumps(
                        {
                            "format": payload_format,
                            "expr": canonical_conclusion_expr,
                        },
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=True,
                    )
                )
    return LeanStatementContractAnalysis(
        display_type=str(display_type or "").strip(),
        structural_identity=make_lean_contract_identity(
            hash_text(full_identity_payload),
            contract_profile_hash,
            version=int(payload_format),
        ),
        binder_sorts=tuple(binder_sorts),
        binder_types=tuple(binder_types),
        binder_normalized_types=tuple(binder_normalized_types),
        proof_binder_types=tuple(proof_binder_types),
        proof_binder_structural_hashes=tuple(
            proof_binder_structural_hashes
        ),
        contract_conclusion_structural_hash=(
            contract_conclusion_structural_hash
        ),
        definitionally_equal_indices=tuple(
            sorted(
                {
                    int(index)
                    for index in list(payload.get("defeq") or ())
                    if isinstance(index, int) and index >= 0
                }
            )
        ),
        contract_definitionally_equal_indices=tuple(
            sorted(
                {
                    int(index)
                    for index in list(payload.get("contractDefeq") or ())
                    if isinstance(index, int) and index >= 0
                }
            )
        ),
        definitionally_checked_indices=tuple(
            sorted(
                {
                    int(index)
                    for index in list(payload.get("defeqChecked") or ())
                    if isinstance(index, int) and index >= 0
                }
            )
        ),
        contract_definitionally_checked_indices=tuple(
            sorted(
                {
                    int(index)
                    for index in list(
                        payload.get("contractDefeqChecked") or ()
                    )
                    if isinstance(index, int) and index >= 0
                }
            )
        ),
    )


class _LeanRunnerGenerationRef:
    def __init__(self, current: "LeanRunner") -> None:
        self.current = current


class LeanRunner:
    # Long enough for a killed Lean subprocess/process group to reap under
    # ordinary load, finite so a broken pipe waiter cannot retain build and
    # adapter leases forever.
    _killed_process_reap_timeout_s = 30.0
    _generation_forwarded_methods = frozenset(
        {
            "ensure_project_imports_built",
            "revalidate_theorem_project_environment",
            "ensure_support_projects_built",
            "mark_project_imports_ready",
            "bind_resolved_lean_environment",
            "check",
            "run_observation_commands",
            "check_with_sorry",
            "check_with_sorry_raw",
            "suggest_tactics",
            "check_term_type",
            "check_source_declaration_type",
            "check_source_declaration_type_equivalence",
            "extract_typed_residual_batch",
            "analyze_statement_contracts",
            "canonicalize_statement_types",
            "check_statement_type_raw",
            "apply_decl_to_goal",
            "supports_silence_fast_fail",
            "get_stats",
            "reset_stats",
        }
    )

    def __getattribute__(self, name: str) -> Any:
        # Captured factory/controller locals can outlive a generation swap.
        # Forward only public theorem-operation surfaces; private methods of
        # an already-running late tail remain bound to the quarantined object.
        forwarded = object.__getattribute__(self, "_generation_forwarded_methods")
        if name in forwarded:
            try:
                replacement = object.__getattribute__(
                    self,
                    "_generation_ref",
                ).current
            except AttributeError:
                replacement = None
            if replacement is not None and replacement is not self:
                return getattr(replacement, name)
        return object.__getattribute__(self, name)

    def __init__(self, cfg: LeanConfig, *, oracle_max_concurrent: int = 2):
        self.cfg = cfg
        self._oracle_max_concurrent = max(1, int(oracle_max_concurrent or 1))
        # Kept only for compatibility with captured pre-indirection runners.
        # New rotations publish through the stable generation ref; teardown
        # iteratively detaches any historical pointer chain without recursing.
        self._replacement_runner: Optional["LeanRunner"] = None
        self._generation_ref = _LeanRunnerGenerationRef(self)
        self.project_dir = Path(cfg.project_dir).resolve()
        self.temp_dir = _resolve_lean_scratch_root(cfg)
        self.temp_dir.mkdir(parents=True, exist_ok=True)
        self.sem = asyncio.Semaphore(cfg.max_parallel)
        # Separate semaphore for tactic oracle calls (exact?, apply?) so they
        # don't starve normal proof checks.  Configured via TacticOracleConfig.
        self.suggest_sem = asyncio.Semaphore(self._oracle_max_concurrent)
        self._repl: Optional[LeanREPL] = None
        self._closed = False
        self._quiesced = False
        self._close_generation = 0
        self._persistent_pool: Optional[PersistentVerifierPool] = None
        self._repl_init = False
        self._repl_lock = asyncio.Lock()
        self._repl_startup_time_s: float = 0.0
        self._repl_start_failures: int = 0
        self._repl_runtime_failures: int = 0
        self._repl_restart_count: int = 0
        self._repl_fallback_count: int = 0
        self._repl_disabled_until_s: float = 0.0
        self._repl_generation: int = 0
        self._persistent_check_count: int = 0
        self._persistent_fallback_count: int = 0
        self._last_backend_key: str = self._preferred_backend_key()
        self._inflight_exec_lock = asyncio.Lock()
        self._inflight_exec: Dict[
            str, asyncio.Future[tuple[tuple[int, str], str, str]]
        ] = {}
        self._completed_exec: Dict[str, tuple[tuple[int, str], str, str]] = {}
        self._completed_exec_max_entries = 256
        self._execution_environment_generation = 0
        self._environment_transition_condition = asyncio.Condition()
        self._environment_transitioning = False
        self._environment_active_executions = 0
        self._inflight_exec_tasks: set[asyncio.Task[Any]] = set()
        self._owned_temp_files: set[Path] = set()
        self._request_dedup_hits: int = 0
        self._request_dedup_hits_full: int = 0
        self._request_dedup_hits_sorry: int = 0
        self._request_dedup_hits_oracle: int = 0
        self._request_dedup_hits_raw: int = 0
        # Throughput instrumentation (Phase 3)
        self._check_count: int = 0
        self._check_ok_count: int = 0
        self._check_fail_count: int = 0
        self._full_check_count: int = 0
        self._full_check_ok_count: int = 0
        self._full_check_fail_count: int = 0
        self._precheck_check_count: int = 0
        self._precheck_ok_count: int = 0
        self._precheck_fail_count: int = 0
        self._sorry_check_count: int = 0
        self._sorry_check_ok_count: int = 0
        self._sorry_check_fail_count: int = 0
        self._oracle_check_count: int = 0
        # RCA 2026-04-24: count of "Try this:" suggestions dropped because
        # their source line was BEFORE the goal block. Catches Mathlib
        # introMerge linter (and similar) emitting against context-lemma
        # bodies preceding the goal — historically harvested as cross-goal
        # proof candidates that produced binder_arity_mismatch cascades.
        # See WORK_VALIDATION_LOG_2026-04-24_oracle_try_this_harvest_root_fix.md.
        self._oracle_suggestions_off_block_dropped: int = 0
        self._total_check_time_s: float = 0.0
        self._total_queue_wait_s: float = 0.0

        self._max_check_time_s: float = 0.0
        self._max_queue_wait_s: float = 0.0
        self._active_checks: int = 0
        self._peak_active_checks: int = 0
        self._repl_check_count: int = 0
        self._lake_check_count: int = 0
        self._extra_imports_ready: bool = False
        self._extra_imports_lock = asyncio.Lock()
        self._project_imports_ready: bool = False
        self._project_imports_lock = asyncio.Lock()
        self._support_projects_ready: bool = False
        self._support_projects_lock = asyncio.Lock()

    def current_generation(self) -> "LeanRunner":
        """Return the newest published replacement without mutating callers."""

        current = self._generation_ref.current
        return current if isinstance(current, LeanRunner) else self

    def _detach_replacement_chain(self) -> None:
        """Drop retired-to-live pointer chains without closing anyone.

        ``_generation_ref`` is the stable live handle.  The historical
        ``_replacement_runner`` linked list only retains retired objects and
        must never be followed recursively during quiesce or close.
        """

        node: Optional["LeanRunner"] = self
        seen: set[int] = set()
        while node is not None:
            node_id = id(node)
            if node_id in seen:
                break
            seen.add(node_id)
            nxt = node._replacement_runner
            node._replacement_runner = None
            node = nxt if nxt is not node else None

    def _cfg_attr(self, name: str, default: Any) -> Any:
        try:
            return inspect.getattr_static(self.cfg, name)
        except AttributeError:
            return default

    def _legacy_use_repl(self) -> bool:
        value = self._cfg_attr("use_repl", True)
        return value if isinstance(value, bool) else False

    def _configured_backend_mode(self) -> str:
        mode = str(self._cfg_attr("backend_mode", "") or "").strip().lower()
        if mode in {"lake", "env_cached_subprocess", "persistent_process"}:
            return mode
        return "env_cached_subprocess" if self._legacy_use_repl() else "lake"

    def _configured_use_repl(self) -> bool:
        return self._configured_backend_mode() == "env_cached_subprocess"

    def _preferred_backend_key(self) -> str:
        mode = self._configured_backend_mode()
        if mode == "persistent_process":
            return "persistent"
        if mode == "env_cached_subprocess":
            return "repl"
        return "lake"

    def _backend_capabilities(
        self, backend_key: Optional[str] = None
    ) -> Dict[str, Any]:
        key = str(
            backend_key or self._last_backend_key or self._preferred_backend_key()
        )
        if key == "persistent":
            return {
                "backend_key": "persistent",
                "backend_kind": "persistent_process",
                "caches_environment": True,
                "persistent_process": True,
                "supports_silence_fast_fail": False,
            }
        if key == "repl":
            return {
                "backend_key": "repl",
                "backend_kind": "env_cached_subprocess",
                "caches_environment": True,
                "persistent_process": False,
                "supports_silence_fast_fail": False,
            }
        return {
            "backend_key": "lake",
            "backend_kind": "lake_subprocess",
            "caches_environment": False,
            "persistent_process": False,
            "supports_silence_fast_fail": False,
        }

    def supports_silence_fast_fail(self) -> bool:
        return bool(
            self._backend_capabilities().get("supports_silence_fast_fail", False)
        )

    @staticmethod
    def _normalized_timeout_key_part(value: Optional[float]) -> str:
        if value is None:
            return ""
        try:
            scalar = float(value)
        except Exception:
            return ""
        return f"{scalar:.6f}"

    def _execution_deadline(self, timeout_s: Optional[float]) -> float:
        """Return the absolute deadline for the complete Lean operation.

        Backend timeouts historically began only after environment admission
        and semaphore acquisition.  A blocked transition or saturated queue
        could therefore outlive the advertised timeout indefinitely.  Keep a
        single monotonic deadline from entry so every admission stage consumes
        the same wall-clock budget as the backend.
        """

        configured = (
            timeout_s
            if timeout_s is not None
            else getattr(self.cfg, "timeout_s", 1.0)
        )
        try:
            timeout = float(configured)
        except (TypeError, ValueError):
            timeout = 1.0
        if timeout <= 0.0:
            timeout = 1.0
        return time.monotonic() + timeout

    @staticmethod
    def _execution_time_remaining(deadline_monotonic: float) -> float:
        return max(0.0, float(deadline_monotonic) - time.monotonic())

    @staticmethod
    def _execution_deadline_result(
        phase: str,
        *,
        file_path: Optional[Path] = None,
    ) -> tuple[tuple[int, str], str, str]:
        return (
            (1, f"Lean timeout while waiting for {str(phase or 'execution')}"),
            str(file_path or ""),
            "deadline",
        )

    def _execution_cache_key(
        self,
        *,
        mode: str,
        content: str,
        timeout_s: Optional[float],
        fast_fail_timeout_s: Optional[float],
        warning_as_error: Optional[bool] = None,
        use_oracle_sem: bool = False,
        retry_repl_termination: bool = True,
        environment_epoch: Optional[int] = None,
    ) -> str:
        if environment_epoch is None:
            environment_epoch = LeanREPL.global_env_epoch(
                str(self.project_dir.resolve())
            )
        return hash_text(
            "\0".join(
                [
                    str(mode or ""),
                    self._preferred_backend_key(),
                    "oracle" if use_oracle_sem else "main",
                    (
                        "repl-termination:retry"
                        if retry_repl_termination
                        else "repl-termination:return"
                    ),
                    self._normalized_timeout_key_part(timeout_s),
                    self._normalized_timeout_key_part(fast_fail_timeout_s),
                    (
                        "warnings:default"
                        if warning_as_error is None
                        else "warnings:error"
                        if warning_as_error
                        else "warnings:allow"
                    ),
                    f"environment:{self._execution_environment_generation}",
                    f"global-environment:{int(environment_epoch)}",
                    str(content or ""),
                ]
            )
        )

    def _record_request_dedup_hit(self, mode: str) -> None:
        self._request_dedup_hits += 1
        mode_key = str(mode or "").strip().lower()
        if mode_key == "full":
            self._request_dedup_hits_full += 1
        elif mode_key == "sorry":
            self._request_dedup_hits_sorry += 1
        elif mode_key == "oracle":
            self._request_dedup_hits_oracle += 1
        elif mode_key == "raw":
            self._request_dedup_hits_raw += 1

    def _required_extra_imports_for_proof(self, proof_code: str) -> Tuple[str, ...]:
        if not re.search(r"\bprop_complete\b", str(proof_code or "")):
            return ()
        return self._configured_extra_imports()

    def _resolve_preamble(
        self,
        preamble_override: str | None = None,
        *,
        proof_code: str = "",
    ) -> str:
        base = (
            preamble_override
            if preamble_override is not None
            else self.cfg.preamble_import
        )
        resolved = _append_imports_to_preamble(
            base,
            self._required_extra_imports_for_proof(proof_code),
        )
        # Append preamble tactics (custom automation macros)
        tactics = str(getattr(self.cfg, "preamble_tactics", "") or "").strip()
        if tactics:
            resolved = resolved.rstrip() + "\n\n" + tactics + "\n"
        return resolved

    def _configured_extra_imports(self) -> Tuple[str, ...]:
        extra_imports = getattr(self.cfg, "extra_imports", ())
        if not isinstance(extra_imports, (list, tuple)):
            return ()
        modules: List[str] = []
        for item in extra_imports:
            text = str(item or "").strip()
            if not text:
                continue
            if text.startswith("import "):
                text = text[len("import ") :].strip()
            if text:
                modules.append(text)
        return tuple(modules)

    async def _communicate_lake_build(
        self,
        proc: asyncio.subprocess.Process,
        *,
        timeout_s: float,
    ) -> tuple[bytes, bytes]:
        """Capture Lake output without turning a completed exit into a timeout.

        A short-lived Lake descendant can inherit the output pipes. At the
        watchdog boundary ``communicate`` may still be awaiting EOF even
        though the process transport already has a real return code. Preserve
        that completed result; callers still reject nonzero codes, and only a
        genuinely live process is treated as hung.
        """

        communicate_task = asyncio.create_task(proc.communicate())
        exit_task = asyncio.create_task(proc.wait())
        try:
            deadline = time.monotonic() + max(0.01, float(timeout_s))
            while True:
                if communicate_task.done():
                    return communicate_task.result()
                # asyncio Process.wait() may itself wait for inherited output
                # pipes after process_exited() has already set returncode.
                # Poll that authoritative exit state independently so a
                # completed Lake build is never mistaken for a live hang.
                if proc.returncode is not None or exit_task.done():
                    done, _pending = await asyncio.wait(
                        {communicate_task},
                        timeout=0.25,
                    )
                    if communicate_task in done:
                        return communicate_task.result()
                    await self._kill_proc(
                        proc,
                        wait_task=exit_task,
                        auxiliary_tasks=(communicate_task,),
                    )
                    return b"", b""
                remaining = deadline - time.monotonic()
                if remaining <= 0.0:
                    raise asyncio.TimeoutError
                await asyncio.wait(
                    {communicate_task, exit_task},
                    timeout=min(0.05, remaining),
                    return_when=asyncio.FIRST_COMPLETED,
                )
        except asyncio.CancelledError:
            await self._finish_cleanup_despite_cancellation(
                self._kill_proc(
                    proc,
                    wait_task=exit_task,
                    auxiliary_tasks=(communicate_task,),
                )
            )
            raise
        except BaseException:
            await self._kill_proc(
                proc,
                wait_task=exit_task,
                auxiliary_tasks=(communicate_task,),
            )
            raise
        finally:
            if not exit_task.done():
                exit_task.cancel()
                exit_task.add_done_callback(_consume_future_exception)
            if not communicate_task.done():
                communicate_task.cancel()
                communicate_task.add_done_callback(_consume_future_exception)

    async def _ensure_extra_imports_built(self, modules: Sequence[str]) -> None:
        modules = tuple(
            str(mod or "").strip() for mod in modules if str(mod or "").strip()
        )
        if not modules or self._extra_imports_ready:
            return
        async with self._extra_imports_lock:
            if self._extra_imports_ready:
                return
            proc = await asyncio.create_subprocess_exec(
                "lake",
                "build",
                cwd=str(self.project_dir),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                start_new_session=True,
            )
            try:
                stdout, stderr = await self._communicate_lake_build(
                    proc,
                    timeout_s=max(
                        _LEAN_ENVIRONMENT_OPERATION_TIMEOUT_FLOOR_S,
                        float(getattr(self.cfg, "timeout_s", 300)),
                    ),
                )
            except asyncio.TimeoutError as exc:
                raise RuntimeError(
                    f"Timed out building Lean project for extra imports: {', '.join(modules)}"
                ) from exc
            except asyncio.CancelledError:
                raise
            except BaseException:
                raise
            if proc.returncode != 0:
                out = stdout.decode(errors="replace")
                err = stderr.decode(errors="replace")
                detail = (out + ("\n" if out and err else "") + err).strip()
                raise RuntimeError(
                    "Failed to build Lean project for extra imports "
                    f"({', '.join(modules)}): {detail or 'unknown error'}"
                )
            self._extra_imports_ready = True

    async def ensure_project_imports_built(self, *, force: bool = False) -> None:
        """Build configured project module targets once, under a watchdog."""

        modules = tuple(
            dict.fromkeys(
                str(module or "").strip()
                for module in list(getattr(self.cfg, "project_imports", ()) or ())
                if str(module or "").strip()
            )
        )
        if not modules or (self._project_imports_ready and not force):
            return
        async with self._project_imports_lock:
            if self._project_imports_ready and not force:
                return
            if force:
                # Forced validation starts a new readiness generation.  The
                # previous success cannot authorize checks if this build
                # fails or is cancelled.
                self._project_imports_ready = False
            proc = await asyncio.create_subprocess_exec(
                "lake",
                "build",
                *modules,
                cwd=str(self.project_dir),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                start_new_session=True,
            )
            try:
                stdout, stderr = await self._communicate_lake_build(
                    proc,
                    timeout_s=max(
                        _LEAN_ENVIRONMENT_OPERATION_TIMEOUT_FLOOR_S,
                        float(getattr(self.cfg, "timeout_s", 300)),
                    ),
                )
            except asyncio.TimeoutError as exc:
                raise RuntimeError(
                    "Timed out building theorem-project imports: "
                    + ", ".join(modules)
                ) from exc
            except asyncio.CancelledError:
                raise
            except BaseException:
                raise
            if proc.returncode != 0:
                output = stdout.decode(errors="replace")
                error = stderr.decode(errors="replace")
                detail = (output + ("\n" if output and error else "") + error).strip()
                raise RuntimeError(
                    "Failed to build theorem-project imports "
                    f"({', '.join(modules)}): {detail or 'unknown error'}"
                )
            self._project_imports_ready = True

    async def revalidate_theorem_project_environment(self) -> None:
        """Rebuild local targets and invalidate every cached Lean environment."""

        transition_acquired = False
        operation_error: Optional[BaseException] = None
        cleanup_cancellation: Optional[asyncio.CancelledError] = None
        cleanup_errors: list[BaseException] = []

        async def finish_environment_transition() -> None:
            try:
                async with self._environment_transition_condition:
                    while self._environment_active_executions:
                        await self._environment_transition_condition.wait()
                async with self._repl_lock:
                    repl = self._repl
                    self._repl = None
                    self._repl_init = False
                    self._repl_disabled_until_s = 0.0
                    if repl is not None:
                        try:
                            repl.close()
                        except BaseException as exc:
                            cleanup_errors.append(exc)
                    self._repl_generation += 1
                pool = self._persistent_pool
                self._persistent_pool = None
                if pool is not None:
                    try:
                        await pool.close()
                    except BaseException as exc:
                        cleanup_errors.append(exc)
                try:
                    setattr(self.cfg, "resolved_lean_path", "")
                    setattr(self.cfg, "resolved_lean_executable", "")
                except BaseException as exc:
                    cleanup_errors.append(exc)
                try:
                    LeanREPL._clear_global_env_cache(
                        str(self.project_dir.resolve())
                    )
                except BaseException as exc:
                    cleanup_errors.append(exc)
                async with self._inflight_exec_lock:
                    self._execution_environment_generation += 1
                    self._completed_exec.clear()
            finally:
                async with self._environment_transition_condition:
                    self._environment_transitioning = False
                    self._environment_transition_condition.notify_all()
        try:
            async with self._environment_transition_condition:
                while self._environment_transitioning:
                    await self._environment_transition_condition.wait()
                self._environment_transitioning = True
                transition_acquired = True
                while self._environment_active_executions:
                    await self._environment_transition_condition.wait()
            await self.ensure_support_projects_built(force=True)
            await self.ensure_project_imports_built(force=True)
        except BaseException as exc:
            operation_error = exc
        finally:
            if transition_acquired:
                cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                    finish_environment_transition()
                )
        if cleanup_cancellation is not None:
            if operation_error is not None:
                cleanup_cancellation.add_note(
                    "environment revalidation also failed before cancellation: "
                    f"{type(operation_error).__name__}: {operation_error}"
                )
            for cleanup_error in cleanup_errors:
                cleanup_cancellation.add_note(
                    "environment cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise cleanup_cancellation
        if operation_error is not None:
            for cleanup_error in cleanup_errors:
                operation_error.add_note(
                    "environment cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise operation_error
        if cleanup_errors:
            primary = cleanup_errors[0]
            for cleanup_error in cleanup_errors[1:]:
                primary.add_note(
                    f"additional cleanup failure: {type(cleanup_error).__name__}: "
                    f"{cleanup_error}"
                )
            raise primary

    async def ensure_support_projects_built(self, *, force: bool = False) -> None:
        """Ask each external Lake project to validate its dependency graph."""

        raw_builds = dict(getattr(self.cfg, "support_project_builds", {}) or {})
        builds = tuple(
            (
                Path(str(project)).expanduser().resolve(),
                tuple(
                    dict.fromkeys(
                        str(target or "").strip()
                        for target in list(targets or ())
                        if str(target or "").strip()
                    )
                ),
            )
            for project, targets in raw_builds.items()
            if str(project or "").strip()
        )
        if not builds or (self._support_projects_ready and not force):
            return
        async with self._support_projects_lock:
            if self._support_projects_ready and not force:
                return
            if force:
                # All configured support projects form one readiness unit;
                # retain False unless every target below succeeds.
                self._support_projects_ready = False
            for project, targets in builds:
                proc = await asyncio.create_subprocess_exec(
                    "lake",
                    "build",
                    *targets,
                    cwd=str(project),
                    stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.PIPE,
                    start_new_session=True,
                )
                try:
                    stdout, stderr = await self._communicate_lake_build(
                        proc,
                        timeout_s=max(
                            _LEAN_ENVIRONMENT_OPERATION_TIMEOUT_FLOOR_S,
                            float(getattr(self.cfg, "timeout_s", 300)),
                        ),
                    )
                except asyncio.TimeoutError as exc:
                    await self._kill_proc(proc)
                    raise RuntimeError(
                        f"Timed out building supporting Lean project: {project}"
                    ) from exc
                except asyncio.CancelledError:
                    await self._finish_cleanup_despite_cancellation(
                        self._kill_proc(proc)
                    )
                    raise
                except BaseException:
                    await self._kill_proc(proc)
                    raise
                if proc.returncode != 0:
                    output = stdout.decode(errors="replace")
                    error = stderr.decode(errors="replace")
                    detail = (output + ("\n" if output and error else "") + error).strip()
                    raise RuntimeError(
                        f"Failed to build supporting Lean project {project}: "
                        f"{detail or 'unknown error'}"
                    )
            self._support_projects_ready = True

    def mark_project_imports_ready(self) -> None:
        """Record that an exact source probe resolved configured imports."""

        self._project_imports_ready = True

    def bind_resolved_lean_environment(
        self,
        lean_path: str,
        lean_executable: str,
        *,
        expected_epoch: Optional[int] = None,
    ) -> bool:
        """Bind a pre-resolved Lake environment to its current cache epoch."""

        cache_key = str(self.project_dir.resolve())
        with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
            current_epoch = int(
                LeanREPL._GLOBAL_ENV_EPOCH.get(cache_key, 0) or 0
            )
            if (
                expected_epoch is not None
                and int(expected_epoch) != current_epoch
            ):
                return False
            setattr(
                self.cfg,
                "resolved_lean_path",
                str(lean_path or "").strip(),
            )
            setattr(
                self.cfg,
                "resolved_lean_executable",
                str(lean_executable or "").strip(),
            )
            setattr(
                self.cfg,
                "resolved_lean_environment_epoch",
                current_epoch,
            )
            return True

    def _configured_resolved_lean_environment(self) -> tuple[str, str, int]:
        """Return only epoch-authenticated pre-resolved Lake coordinates."""

        lean_path = str(
            getattr(self.cfg, "resolved_lean_path", "") or ""
        ).strip()
        lean_executable = str(
            getattr(self.cfg, "resolved_lean_executable", "") or ""
        ).strip()
        cache_key = str(self.project_dir.resolve())
        current_epoch = LeanREPL.global_env_epoch(cache_key)
        configured_epoch = getattr(
            self.cfg,
            "resolved_lean_environment_epoch",
            None,
        )
        epoch_matches = bool(
            type(configured_epoch) is int
            and int(configured_epoch) == current_epoch
        )
        if configured_epoch is None and current_epoch == 0:
            # Legacy/bootstrap callers may supply an environment before the
            # first invalidation. Bind that one-time authority now.
            epoch_matches = True
        if lean_path and lean_executable and epoch_matches:
            setattr(
                self.cfg,
                "resolved_lean_environment_epoch",
                current_epoch,
            )
            return lean_path, lean_executable, current_epoch
        if lean_path or lean_executable:
            setattr(self.cfg, "resolved_lean_path", "")
            setattr(self.cfg, "resolved_lean_executable", "")
        return "", "", current_epoch

    async def _get_persistent_pool(self) -> Optional[PersistentVerifierPool]:
        if self._closed or self._configured_backend_mode() != "persistent_process":
            return None
        if self._persistent_pool is None:
            self._persistent_pool = PersistentVerifierPool(self.cfg)
        pool = self._persistent_pool
        ok = await pool.start()
        if self._closed:
            await pool.close()
            if self._persistent_pool is pool:
                self._persistent_pool = None
            return None
        if ok:
            return pool
        return None

    async def _get_repl(self) -> Optional[LeanREPL]:
        """Lazily initialize the env-cached Lean backend if enabled."""
        if self._closed or not self._configured_use_repl():
            return None
        now = time.monotonic()
        if self._repl is not None and self._repl.available:
            return self._repl
        if self._repl_disabled_until_s > now:
            return None
        async with self._repl_lock:
            if self._closed:
                return None
            close_generation = self._close_generation
            now = time.monotonic()
            if self._repl is not None and self._repl.available:
                return self._repl
            if self._repl_disabled_until_s > now:
                return None
            repl = LeanREPL(
                self.project_dir,
                timeout_s=self.cfg.timeout_s,
                fast_fail_timeout_s=getattr(self.cfg, "fast_fail_timeout_s", 20),
                fast_fail_enabled=getattr(self.cfg, "fast_fail_enabled", True),
                extra_lean_paths=tuple(
                    str(path)
                    for path in getattr(self.cfg, "module_search_paths", ())
                    if str(path).strip()
                ),
            )
            # Mini-theory activation and other environment preflights may
            # already have resolved the exact Lake environment. Reuse that
            # authoritative result instead of launching duplicate `lake env`
            # probes with an independent startup timeout. LeanREPL composes
            # this raw project LEAN_PATH with its instance-specific module
            # roots when it consumes the cache entry.
            (
                resolved_lean_path,
                resolved_lean_bin,
                resolved_environment_epoch,
            ) = self._configured_resolved_lean_environment()
            if resolved_lean_path and resolved_lean_bin:
                published = LeanREPL._set_global_env_cache(
                    repl.project_cache_key,
                    resolved_lean_path,
                    resolved_lean_bin,
                    expected_epoch=resolved_environment_epoch,
                )
                if not published:
                    setattr(self.cfg, "resolved_lean_path", "")
                    setattr(self.cfg, "resolved_lean_executable", "")
            start_t0 = time.monotonic()
            ok = await repl.start()
            if self._closed or self._close_generation != close_generation:
                repl.close()
                return None
            self._repl_startup_time_s = max(
                self._repl_startup_time_s,
                time.monotonic() - start_t0,
            )
            if ok:
                self._repl = repl
                self._repl_init = True
                self._repl_start_failures = 0
                self._repl_disabled_until_s = 0.0
                self._repl_generation += 1
                logger.info("LeanRunner: REPL mode active")
                return repl
            self._repl = None
            self._repl_init = False
            self._repl_start_failures += 1
            cooldown_s = min(30.0, max(1.0, 2.0 ** min(self._repl_start_failures - 1, 4)))
            self._repl_disabled_until_s = time.monotonic() + cooldown_s
            logger.info(
                "LeanRunner: REPL unavailable, using lake subprocess for %.1fs",
                cooldown_s,
            )
            return None

    async def _restart_repl_backend(
        self,
        *,
        expected_generation: Optional[int] = None,
        invalidate_environment: bool = True,
    ) -> Optional[LeanREPL]:
        """Try to restart the env-cached backend after a runtime failure."""
        if self._closed or not self._configured_use_repl():
            return None
        async with self._repl_lock:
            if self._closed:
                return None
            repl = self._repl
            if (
                repl is not None
                and repl.available
                and expected_generation is not None
                and self._repl_generation != int(expected_generation)
            ):
                return repl
            if repl is None:
                self._repl_init = False
                self._repl_disabled_until_s = 0.0
                return None
            start_t0 = time.monotonic()
            ok = await (
                repl.restart()
                if invalidate_environment
                else repl.refresh_current_environment()
            )
            if self._closed:
                repl.close()
                return None
            self._repl_startup_time_s = max(
                self._repl_startup_time_s,
                time.monotonic() - start_t0,
            )
            if ok and repl.available:
                self._repl = repl
                self._repl_init = True
                self._repl_restart_count += 1
                self._repl_disabled_until_s = 0.0
                self._repl_generation += 1
                return repl
            self._repl = None
            self._repl_init = False
            self._repl_start_failures += 1
            cooldown_s = min(30.0, max(1.0, 2.0 ** min(self._repl_start_failures - 1, 4)))
            self._repl_disabled_until_s = time.monotonic() + cooldown_s
            return None

    def _write_temp_lean_file(self, file_path: Path, content: str) -> Optional[OSError]:
        """Write a scratch Lean file, self-healing a deleted ``temp_dir``.

        The scratch dir (``.lean_tmp``) is created once at init.  If it is
        removed out from under a live run (e.g. an external cleanup deleting the
        run's ``.lean_tmp``), a plain ``write_text`` then fails for EVERY
        subsequent check.  Recreate the dir and retry once so a single deletion
        costs at most one transient miss instead of bricking the run.  Returns
        ``None`` on success or the final :class:`OSError` on failure.
        """

        try:
            file_path.write_text(content, encoding="utf-8")
            return None
        except OSError as first_exc:
            if self._closed or self._quiesced:
                # Cancellation barrier: never resurrect the scratch dir for
                # a late writer after teardown began.
                return first_exc
        try:
            self.temp_dir.mkdir(parents=True, exist_ok=True)
            file_path.write_text(content, encoding="utf-8")
            logger.warning("Recreated missing Lean scratch dir %s", self.temp_dir)
            return None
        except OSError as exc:
            return exc

    async def _admit_uncached_execution(
        self,
        execution_task: Optional[asyncio.Task[Any]] = None,
    ) -> Optional[asyncio.Task[Any]]:
        """Join the runner lifecycle barrier for a multi-process transaction."""

        async with self._environment_transition_condition:
            while self._environment_transitioning:
                await self._environment_transition_condition.wait()
            if self._closed or self._quiesced:
                raise RuntimeError(
                    "LeanRunner is closed"
                    if self._closed
                    else "LeanRunner is quiesced (cancellation barrier)"
                )
            self._environment_active_executions += 1
            if execution_task is None:
                execution_task = asyncio.current_task()
            if execution_task is not None:
                self._inflight_exec_tasks.add(execution_task)
            return execution_task

    async def _release_uncached_execution(
        self,
        execution_task: Optional[asyncio.Task[Any]],
    ) -> None:
        """Leave the lifecycle barrier entered by `_admit_uncached_execution`."""

        if execution_task is not None:
            self._inflight_exec_tasks.discard(execution_task)
        async with self._environment_transition_condition:
            self._environment_active_executions = max(
                0,
                self._environment_active_executions - 1,
            )
            self._environment_transition_condition.notify_all()

    async def _execute_content(
        self,
        *,
        mode: str,
        goal_name: str,
        content: str,
        timeout_s: Optional[float],
        fast_fail_timeout_s: Optional[float],
        warning_as_error: Optional[bool] = None,
        use_oracle_sem: bool = False,
        retry_repl_termination: bool = True,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> tuple[tuple[int, str], str, str]:
        deadline_monotonic = self._execution_deadline(timeout_s)
        environment_admitted = False

        async def admit_environment_execution() -> None:
            nonlocal environment_admitted
            async with self._environment_transition_condition:
                while self._environment_transitioning:
                    await self._environment_transition_condition.wait()
                self._environment_active_executions += 1
                environment_admitted = True

        try:
            remaining = self._execution_time_remaining(deadline_monotonic)
            if remaining <= 0.0:
                return self._execution_deadline_result("environment transition")
            try:
                await asyncio.wait_for(
                    admit_environment_execution(),
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                return self._execution_deadline_result("environment transition")
            return await self._execute_content_unbarriered(
                mode=mode,
                goal_name=goal_name,
                content=content,
                timeout_s=timeout_s,
                fast_fail_timeout_s=fast_fail_timeout_s,
                warning_as_error=warning_as_error,
                use_oracle_sem=use_oracle_sem,
                retry_repl_termination=retry_repl_termination,
                deadline_monotonic=deadline_monotonic,
                dispatch_observer=dispatch_observer,
            )
        finally:
            if environment_admitted:
                async with self._environment_transition_condition:
                    self._environment_active_executions = max(
                        0,
                        self._environment_active_executions - 1,
                    )
                    self._environment_transition_condition.notify_all()

    async def _execute_content_unbarriered(
        self,
        *,
        mode: str,
        goal_name: str,
        content: str,
        timeout_s: Optional[float],
        fast_fail_timeout_s: Optional[float],
        warning_as_error: Optional[bool] = None,
        use_oracle_sem: bool = False,
        retry_repl_termination: bool = True,
        deadline_monotonic: float,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> tuple[tuple[int, str], str, str]:
        if self._closed or self._quiesced:
            raise RuntimeError(
                "LeanRunner is closed"
                if self._closed
                else "LeanRunner is quiesced (cancellation barrier)"
            )
        leader = False
        async with self._inflight_exec_lock:
            if self._closed or self._quiesced:
                raise RuntimeError(
                    "LeanRunner is closed"
                    if self._closed
                    else "LeanRunner is quiesced (cancellation barrier)"
                )
            cache_key_project = str(self.project_dir.resolve())
            with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
                execution_global_epoch = int(
                    LeanREPL._GLOBAL_ENV_EPOCH.get(cache_key_project, 0) or 0
                )
                cache_key = self._execution_cache_key(
                    mode=mode,
                    content=content,
                    timeout_s=timeout_s,
                    fast_fail_timeout_s=fast_fail_timeout_s,
                    warning_as_error=warning_as_error,
                    use_oracle_sem=use_oracle_sem,
                    retry_repl_termination=retry_repl_termination,
                    environment_epoch=execution_global_epoch,
                )
                completed = self._completed_exec.get(cache_key)
                if completed is not None:
                    self._completed_exec.pop(cache_key, None)
                    self._completed_exec[cache_key] = completed
                    self._record_request_dedup_hit(mode)
                    return completed
                future = self._inflight_exec.get(cache_key)
                if future is None:
                    future = asyncio.get_running_loop().create_future()
                    # Guarantee exception retrieval even if no waiter ever
                    # attaches — otherwise set_exception on a solo leader
                    # produces "Future exception was never retrieved"
                    # warnings at GC.
                    future.add_done_callback(_consume_future_exception)
                    self._inflight_exec[cache_key] = future
                    leader = True
                    execution_task = asyncio.current_task()
                    if execution_task is not None:
                        self._inflight_exec_tasks.add(execution_task)
                else:
                    self._record_request_dedup_hit(mode)
        if not leader:
            remaining = self._execution_time_remaining(deadline_monotonic)
            if remaining <= 0.0:
                return self._execution_deadline_result(
                    "shared Lean execution",
                )
            try:
                return await asyncio.wait_for(
                    asyncio.shield(future),
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                # This caller exhausted its own deadline.  Do not cancel the
                # shared leader: another caller may still have budget and the
                # leader owns the subprocess and coalescing receipt.
                return self._execution_deadline_result(
                    "shared Lean execution",
                )
        execution_task = asyncio.current_task()

        file_path = self.temp_dir / f"{goal_name}_{uuid.uuid4().hex}.lean"
        write_error = self._write_temp_lean_file(file_path, content)
        if write_error is not None:
            exc = write_error
            logger.error("Failed to write temp Lean file %s: %s", file_path, exc)
            payload = ((1, f"disk write failed: {exc}"), str(file_path), "disk_error")
            if not future.done():
                future.set_result(payload)
            if execution_task is not None:
                self._inflight_exec_tasks.discard(execution_task)
            async with self._inflight_exec_lock:
                self._inflight_exec.pop(cache_key, None)
            try:
                file_path.unlink(missing_ok=True)
            except OSError:
                pass
            return payload
        self._owned_temp_files.add(file_path)

        queue_start = time.monotonic()
        sem = self.suggest_sem if use_oracle_sem else self.sem
        sem_acquired = False
        queue_admission_timed_out = False

        async def settle_queue_admission(
            acquire_task: asyncio.Task[bool],
        ) -> None:
            try:
                await acquire_task
            except BaseException:
                pass

        def queue_admission_owns_permit(
            acquire_task: asyncio.Task[bool],
        ) -> bool:
            if not acquire_task.done() or acquire_task.cancelled():
                return False
            try:
                return bool(acquire_task.result())
            except BaseException:
                return False

        try:
            remaining = self._execution_time_remaining(deadline_monotonic)
            if remaining > 0.0:
                acquire_task = asyncio.ensure_future(sem.acquire())
                try:
                    await asyncio.wait_for(acquire_task, timeout=remaining)
                    sem_acquired = True
                except asyncio.TimeoutError:
                    queue_admission_timed_out = True
                    cleanup_cancellation = None
                    if not acquire_task.done():
                        acquire_task.cancel()
                        cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                            settle_queue_admission(acquire_task)
                        )
                    sem_acquired = queue_admission_owns_permit(acquire_task)
                    if cleanup_cancellation is not None:
                        raise cleanup_cancellation
                except BaseException:
                    # wait_for normally settles its child before propagating,
                    # but ownership must also be recovered across the narrow
                    # race where acquisition completed as cancellation landed.
                    cleanup_cancellation = None
                    if not acquire_task.done():
                        acquire_task.cancel()
                        cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                            settle_queue_admission(acquire_task)
                        )
                    sem_acquired = queue_admission_owns_permit(acquire_task)
                    if cleanup_cancellation is not None:
                        raise cleanup_cancellation
                    raise
            queue_wait = time.monotonic() - queue_start
            self._total_queue_wait_s += queue_wait
            self._max_queue_wait_s = max(self._max_queue_wait_s, queue_wait)
            if queue_admission_timed_out or not sem_acquired:
                payload = self._execution_deadline_result(
                    "Lean execution queue",
                    file_path=file_path,
                )
                if not future.done():
                    future.set_result(payload)
                return payload
            if self._closed or self._quiesced:
                raise RuntimeError(
                    "LeanRunner is closed"
                    if self._closed
                    else "LeanRunner is quiesced (cancellation barrier)"
                )
            self._active_checks += 1
            self._peak_active_checks = max(
                self._peak_active_checks, self._active_checks
            )
            check_start = time.monotonic()
            try:
                preferred_backend = self._preferred_backend_key()
                result: Optional[tuple[int, str]] = None
                backend_key = "lake"
                if preferred_backend == "persistent":
                    remaining = self._execution_time_remaining(deadline_monotonic)
                    if remaining <= 0.0:
                        result = self._execution_deadline_result(
                            "Lean backend execution",
                            file_path=file_path,
                        )[0]
                        backend_key = "deadline"
                    else:
                        result = await self._run_via_persistent(
                            file_path,
                            mode=mode,
                            content=content,
                            timeout_s=remaining,
                            warning_as_error=warning_as_error,
                            queue_class="oracle" if use_oracle_sem else "main",
                            **(
                                {"dispatch_observer": dispatch_observer}
                                if dispatch_observer is not None
                                else {}
                            ),
                        )
                    if result is not None and backend_key != "deadline":
                        backend_key = "persistent"
                        self._persistent_check_count += 1
                    elif result is None:
                        remaining = self._execution_time_remaining(
                            deadline_monotonic
                        )
                        if remaining <= 0.0:
                            result = self._execution_deadline_result(
                                "Lean backend execution",
                                file_path=file_path,
                            )[0]
                            backend_key = "deadline"
                        else:
                            result = await self._run_via_repl(
                                file_path,
                                timeout_s=remaining,
                                fast_fail_timeout_s=fast_fail_timeout_s,
                                **(
                                    {"retry_termination": False}
                                    if not retry_repl_termination
                                    else {}
                                ),
                                **(
                                    {"dispatch_observer": dispatch_observer}
                                    if dispatch_observer is not None
                                    else {}
                                ),
                            )
                            if result is not None:
                                backend_key = "repl"
                                self._repl_check_count += 1
                elif preferred_backend == "repl":
                    remaining = self._execution_time_remaining(deadline_monotonic)
                    if remaining <= 0.0:
                        result = self._execution_deadline_result(
                            "Lean backend execution",
                            file_path=file_path,
                        )[0]
                        backend_key = "deadline"
                    else:
                        result = await self._run_via_repl(
                            file_path,
                            timeout_s=remaining,
                            fast_fail_timeout_s=fast_fail_timeout_s,
                            **(
                                {"retry_termination": False}
                                if not retry_repl_termination
                                else {}
                            ),
                            **(
                                {"dispatch_observer": dispatch_observer}
                                if dispatch_observer is not None
                                else {}
                            ),
                        )
                        if result is not None:
                            backend_key = "repl"
                            self._repl_check_count += 1
                if result is None:
                    if self._closed or self._quiesced:
                        raise RuntimeError(
                            "LeanRunner is closed"
                            if self._closed
                            else "LeanRunner is quiesced (cancellation barrier)"
                        )
                    remaining = self._execution_time_remaining(deadline_monotonic)
                    if remaining <= 0.0:
                        result = self._execution_deadline_result(
                            "Lean backend execution",
                            file_path=file_path,
                        )[0]
                        backend_key = "deadline"
                    else:
                        result = await self._run_via_lake(
                            file_path,
                            timeout_s=remaining,
                            fast_fail_timeout_s=fast_fail_timeout_s,
                            **(
                                {"dispatch_observer": dispatch_observer}
                                if dispatch_observer is not None
                                else {}
                            ),
                        )
                        backend_key = "lake"
                        self._lake_check_count += 1
                # A backend is expected to enforce the remaining timeout, but
                # publication is the trust boundary.  Reject any response that
                # arrives after the complete-operation deadline so a stalled or
                # cancellation-resistant backend cannot turn late work into a
                # cached success (or otherwise mutate downstream proof state).
                if (
                    backend_key != "deadline"
                    and self._execution_time_remaining(deadline_monotonic) <= 0.0
                ):
                    result = self._execution_deadline_result(
                        "Lean backend execution",
                        file_path=file_path,
                    )[0]
                    backend_key = "deadline"
                self._last_backend_key = backend_key
            finally:
                check_time = time.monotonic() - check_start
                self._total_check_time_s += check_time
                self._max_check_time_s = max(self._max_check_time_s, check_time)
                self._active_checks -= 1
            payload = (result, str(file_path), backend_key)
            if int(result[0]) == 0:
                cached_payload = (result, "", backend_key)
                async with self._inflight_exec_lock:
                    with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
                        current_global_epoch = int(
                            LeanREPL._GLOBAL_ENV_EPOCH.get(
                                cache_key_project,
                                0,
                            )
                            or 0
                        )
                        if current_global_epoch == execution_global_epoch:
                            self._completed_exec.pop(cache_key, None)
                            self._completed_exec[cache_key] = cached_payload
                            while (
                                len(self._completed_exec)
                                > self._completed_exec_max_entries
                            ):
                                oldest_key = next(iter(self._completed_exec))
                                self._completed_exec.pop(oldest_key, None)
            # Guard against the Future having been cancelled externally
            # (e.g. by _finalize_close_state during runner shutdown) —
            # set_result on a cancelled/done Future raises InvalidStateError.
            if not future.done():
                future.set_result(payload)
            return payload
        except BaseException as exc:
            # BaseException (not just Exception) so we also catch
            # asyncio.CancelledError — which in Python 3.8+ is a
            # BaseException subclass, not an Exception. Leaving
            # CancelledError unhandled here would previously leave the
            # coalescing Future in PENDING state forever, causing any
            # waiter inside asyncio.shield(future) to hang until its
            # own upstream cancellation fired.
            if not future.done():
                if isinstance(exc, asyncio.CancelledError):
                    # Cancel the coalescing Future so shielded waiters
                    # unblock with CancelledError immediately, rather
                    # than deadlock on a Future that will never be
                    # resolved.
                    future.cancel()
                else:
                    # Propagate real errors to waiters so they can
                    # fall back gracefully. _consume_future_exception
                    # (installed at creation) guarantees the exception
                    # is marked retrieved even if no waiter attaches.
                    future.set_exception(exc)
            raise
        finally:
            if sem_acquired:
                sem.release()
            if execution_task is not None:
                self._inflight_exec_tasks.discard(execution_task)
            async with self._inflight_exec_lock:
                self._inflight_exec.pop(cache_key, None)
            try:
                file_path.unlink(missing_ok=True)
            except OSError:
                pass
            self._owned_temp_files.discard(file_path)

    def _build_file(
        self,
        statement: str,
        proof_code: str,
        lemma_block: str,
        goal_name: str,
        *,
        preamble_override: str | None = None,
        warning_as_error: bool = True,
        max_heartbeats: Optional[int] = None,
        axiom_audit_names: Optional[Sequence[str]] = None,
    ) -> "_BuiltLeanFile":
        """Assemble the Lean source for a single check.

        Returns a ``_BuiltLeanFile`` carrying the file ``content`` and
        ``goal_start_line`` — the 1-indexed line at which the goal block
        (``set_option ... in`` wrappers + ``example``) begins. Callers
        thread ``goal_start_line`` into ``parse_lean_output`` so
        ``Try this:`` suggestion harvesting does not pick up linter
        warnings emitted from inside the lemma block (e.g. the Mathlib
        ``introMerge`` linter consolidating consecutive ``intro`` calls in
        a context lemma's proof body).
        """
        preamble = self._resolve_preamble(
            preamble_override,
            proof_code=proof_code,
        )
        preamble, target_scoped_prefix, target_omit_variables = (
            decode_theorem_target_context(preamble)
        )
        # ── Free-universe-variable binding (structural fix, 2026-04-16) ──
        # When ANY part of the generated file references a free universe
        # variable (e.g. `Type u_1`, `Sort u`), the fresh top-level scope
        # must declare those universes explicitly. PutnamBench's
        # lakefile.lean sets `autoImplicit: false`, and the persistent
        # verifier (LSP mode: `lake env lean --server`) STRICTLY enforces
        # that — universe auto-binding is gated on `autoImplicit`. CLI
        # mode (`lake env lean`) is more permissive (Mathlib import
        # appears to override), which is why this bug was invisible to
        # CLI tests yet cascaded under the live LSP runtime.
        #
        # Live trace 2001_a1_16apr_11.jsonl: solved lemmas like
        # `lemma lemma_X : ∀ (S : Type u) ..., ... := by tauto` were
        # injected into lemma_block. `_free_universe_decl(statement)` (the
        # earlier scope) only scanned `statement`, missing the `Type u`
        # in lemma_block. LSP rejected with `unknown universe level u`
        # at the lemma definition; downstream tactics cascaded to
        # "incorrect number of universe levels" on `check_type`.
        # Verified empirically: scanning `statement + lemma_block +
        # proof_code` collects all free universes and a single top-level
        # `universe ...` declaration unblocks elaboration.
        universe_scan_text = "\n".join(
            part for part in (statement, lemma_block, proof_code) if part
        )
        universe_decl = _free_universe_decl(universe_scan_text)
        # ── set_option scoping fix (2026-04-16) ──────────────────────
        # `set_option X in <command>` scopes the option AND any
        # declarations within it to a single command. Putting
        # `universe u_2` inside the scope means the universe variable
        # only exists for that one universe declaration — the
        # `example` that follows sees `Type u_2` as an undeclared
        # universe, falls back to `sorry`, and `intro` fails with
        # "no additional binders to introduce". The universe
        # declaration MUST be a top-level command before any
        # `set_option ... in` wrapper. (Live trace 2001_a1_16apr_8.jsonl
        # had 49 valid proofs rejected this way.)
        audit_requested = axiom_audit_names is not None
        goal_line = (
            # ``check`` also supports constructive/non-Prop targets, so a
            # theorem declaration is not universally legal. ``opaque`` has
            # theorem-like irreducibility, accepts any sort (matching the old
            # ``example`` wrapper), and remains visible to ``collectAxioms``.
            f"opaque {goal_name} : {statement} := {proof_code}\n"
            if audit_requested
            else f"example : {statement} := {proof_code}\n"
        )
        scoped_block = goal_line
        if target_omit_variables:
            scoped_block = (
                f"omit {' '.join(target_omit_variables)} in\n{scoped_block}"
            )
        if target_scoped_prefix:
            scoped_block = f"{target_scoped_prefix}\n{scoped_block}"
        # Belt-and-suspenders: when warnings aren't promoted to errors we
        # are running an oracle / sorry-fill check. Mathlib's
        # ``Mathlib.Tactic.TacticAnalysis.introMerge`` linter (and any
        # similar future linter) emits ``Try this: intro X Y Z`` suggestions
        # against context-lemma bodies that have consecutive ``intro``
        # tactics. The parser-side source-line filter (see lean_parser.py:
        # ``extract_tactic_suggestions``) is the load-bearing fix; this
        # ``set_option`` silences the noise at the source so the linter
        # never produces the spurious suggestion in the first place.
        if not warning_as_error:
            option_lines = ["set_option warningAsError false in"]
            # ``linter.tacticAnalysis.introMerge`` is registered by Mathlib,
            # not Lean core. Emitting it unconditionally makes otherwise valid
            # non-Mathlib theorem projects fail with ``Unknown option``.
            if re.search(r"(?m)^\s*import\s+Mathlib(?:\.|\s|$)", preamble):
                option_lines.insert(
                    0,
                    "set_option linter.tacticAnalysis.introMerge false in",
                )
            scoped_block = "\n".join((*option_lines, scoped_block))
        # `universe ...` must precede ANY declaration that references the
        # universe variable. Put it BEFORE lemma_block (and the example),
        # not after — Lean parses sequentially and would otherwise reject
        # the lemma_block's `Type u` references with `unknown universe
        # level u` under LSP-strict autoImplicit=false.
        head_universe_decl = f"{universe_decl}\n\n" if universe_decl else ""
        # The check budget applies to the complete generated environment, not
        # only to the final goal command. Context helpers are re-elaborated in
        # this file; leaving them at Lean's 200k default allowed a previously
        # verified helper to time out before the goal while the goal itself had
        # the caller's larger budget. Lean then recovered with ``sorryAx``,
        # making an unverified goal look like a harmless harness failure.
        heartbeat_option = (
            f"set_option maxHeartbeats {int(max_heartbeats)}\n\n"
            if isinstance(max_heartbeats, int) and max_heartbeats > 0
            else ""
        )
        # `example` supports both Prop-valued theorems and constructive goals.
        before_lemmas = (
            f"{preamble}\n\n"
            f"{head_universe_decl}"
            f"{heartbeat_option}"
        )
        lemma_block_start_line = (
            before_lemmas.count("\n") + 1 if lemma_block else 0
        )
        prefix = f"{before_lemmas}{lemma_block}\n\n"
        complete_audit_names = tuple(
            dict.fromkeys(
                [
                    *([goal_name] if audit_requested else []),
                    *(
                        str(name or "").strip()
                        for name in list(axiom_audit_names or ())
                        if str(name or "").strip()
                    ),
                ]
            )
        )
        audit_block = ""
        if complete_audit_names:
            audit_block = "\n" + "\n".join(
                f"#print axioms {name}" for name in complete_audit_names
            ) + "\n"
        content = f"{prefix}{scoped_block}{audit_block}"
        # 1-indexed line where the scoped block (set_option wrappers + example)
        # begins. ``Try this:`` suggestions on lines below this are accepted
        # by the parser; suggestions above are rejected as off-block linter
        # noise. ``count("\n")`` counts terminators in the prefix; +1 gives
        # the line number of the next character (start of scoped_block).
        goal_start_line = prefix.count("\n") + 1
        return _BuiltLeanFile(
            content=content,
            goal_start_line=goal_start_line,
            lemma_block_start_line=lemma_block_start_line,
            axiom_audit_names=complete_audit_names,
        )

    async def _run_via_persistent(
        self,
        file_path: Path,
        *,
        mode: str,
        content: str,
        timeout_s: Optional[float] = None,
        warning_as_error: Optional[bool] = None,
        queue_class: str = "main",
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> Optional[tuple[int, str]]:
        pool = await self._get_persistent_pool()
        if pool is None:
            self._persistent_fallback_count += 1
            return None
        total_timeout_s = (
            float(timeout_s) if timeout_s is not None else float(self.cfg.timeout_s)
        )
        if total_timeout_s <= 0.0:
            total_timeout_s = 1.0
        if warning_as_error is None:
            warning_as_error = "set_option warningAsError false" not in str(content or "")
        request = VerifierRequest(
            request_id=f"req-{uuid.uuid4().hex}",
            mode=str(mode or "raw"),
            content=str(content or ""),
            goal_name=str(file_path.stem or "goal"),
            timeout_s=float(total_timeout_s),
            warning_as_error=bool(warning_as_error),
            max_heartbeats=None,
            queue_class=str(queue_class or "main"),
            document_uri=file_path.resolve().as_uri(),
            metadata={"source": "LeanRunner._execute_content"},
        )
        try:
            response = await pool.execute(
                request,
                **(
                    {"dispatch_observer": dispatch_observer}
                    if dispatch_observer is not None
                    else {}
                ),
            )
        except PersistentVerifierUnavailableError as exc:
            logger.warning(
                "Persistent verifier backend unavailable, falling back: %s",
                exc,
            )
            self._persistent_fallback_count += 1
            return None
        except Exception:
            logger.warning(
                "Persistent verifier backend unavailable, falling back",
                exc_info=True,
            )
            self._persistent_fallback_count += 1
            return None
        output = str(response.output or "")
        failure_kind = str(getattr(response, "failure_kind", "") or "").strip()
        if int(response.returncode) != 0 and (
            bool(failure_kind) or has_infra_failure(output)
        ):
            logger.warning(
                "Persistent verifier returned infrastructure failure, falling back: %s",
                failure_kind or (output.splitlines()[-1] if output.splitlines() else output),
            )
            self._persistent_fallback_count += 1
            return None
        return (int(response.returncode), str(response.output or ""))

    async def _run_via_repl(
        self,
        file_path: Path,
        *,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        retry_termination: bool = True,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> Optional[tuple[int, str]]:
        """Try the env-cached backend, restart once on failure, then fall back."""

        def require_live_result(result: tuple[int, str]) -> tuple[int, str]:
            returncode = int(result[0])
            if retry_termination and returncode < 0:
                raise RuntimeError(f"REPL terminated by signal {-returncode}")
            return result

        repl = await self._get_repl()
        if repl is None:
            if self._configured_use_repl():
                self._repl_fallback_count += 1
            return None
        repl_generation = int(self._repl_generation)
        try:
            return require_live_result(
                await repl.check(
                    file_path,
                    timeout_s=timeout_s,
                    fast_fail_timeout_s=fast_fail_timeout_s,
                    **(
                        {"dispatch_observer": dispatch_observer}
                        if dispatch_observer is not None
                        else {}
                    ),
                )
            )
        except Exception as exc:
            self._repl_runtime_failures += 1
            stale_environment = bool(
                getattr(repl, "environment_epoch_stale", False)
            )
            logger.warning(
                "REPL check failed, attempting %s: %s",
                "environment refresh" if stale_environment else "restart",
                exc,
            )
            restarted = await self._restart_repl_backend(
                expected_generation=repl_generation,
                invalidate_environment=not stale_environment,
            )
            if restarted is not None:
                try:
                    return require_live_result(
                        await restarted.check(
                            file_path,
                            timeout_s=timeout_s,
                            fast_fail_timeout_s=fast_fail_timeout_s,
                            **(
                                {"dispatch_observer": dispatch_observer}
                                if dispatch_observer is not None
                                else {}
                            ),
                        )
                    )
                except Exception as retry_exc:
                    self._repl_runtime_failures += 1
                    logger.warning(
                        "REPL check still failing after restart, falling back: %s",
                        retry_exc,
                    )
            self._repl_fallback_count += 1
            return None

    async def _kill_proc(
        self,
        proc: asyncio.subprocess.Process,
        *,
        wait_task: "asyncio.Future[Any] | None" = None,
        auxiliary_tasks: Sequence["asyncio.Future[Any]"] = (),
    ) -> None:
        """Terminate one process generation without an unbounded pipe wait."""

        await terminate_and_reap_process(
            proc,
            wait_task=wait_task,
            auxiliary_tasks=auxiliary_tasks,
            kill_process_group=True,
            reap_timeout_s=max(
                0.01,
                float(self._killed_process_reap_timeout_s or 30.0),
            ),
            log=logger,
        )

    @staticmethod
    async def _finish_cleanup_despite_cancellation(
        cleanup: Awaitable[None],
    ) -> Optional[asyncio.CancelledError]:
        """Complete cleanup and report cancellation intercepted while waiting.

        Callers may need to reconcile semaphore or lifecycle ownership after
        cleanup settles, so cancellation is returned rather than raised here.
        They must re-raise it after that bookkeeping. Call sites already
        handling an earlier ``CancelledError`` can ignore the return value and
        re-raise their original exception.
        """

        caller_task = asyncio.current_task()
        cleanup_task = asyncio.ensure_future(cleanup)
        intercepted_cancellation: Optional[asyncio.CancelledError] = None
        while not cleanup_task.done():
            try:
                await asyncio.shield(cleanup_task)
            except asyncio.CancelledError as exc:
                if intercepted_cancellation is None:
                    intercepted_cancellation = exc
                continue
        try:
            cleanup_task.result()
        except BaseException:
            # Cleanup is best-effort. A caller cancellation remains the
            # primary control-flow signal and must not be replaced by a
            # secondary cleanup/reap failure.
            pass
        if (
            intercepted_cancellation is None
            and caller_task is not None
            and caller_task.cancelling() > 0
        ):
            intercepted_cancellation = asyncio.CancelledError()
        return intercepted_cancellation

    async def _run_via_lake(
        self,
        file_path: Path,
        *,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        dispatch_observer: Optional[Callable[[], None]] = None,
        output_path: Optional[Path] = None,
        extra_module_paths: Sequence[Path] = (),
    ) -> tuple[int, str]:
        """Standard ``lake env lean`` subprocess with hard-timeout protection.

        Direct Lean subprocesses are normally silent on successful checks, so
        silence is not a reliable stuck signal on this backend. The
        ``fast_fail_timeout_s`` argument is accepted for API compatibility, but
        direct lake checks rely on the hard timeout instead of silence-based
        early termination.
        """
        total_timeout_s = (
            float(timeout_s) if timeout_s is not None else float(self.cfg.timeout_s)
        )
        if total_timeout_s <= 0:
            total_timeout_s = 1.0
        operation_deadline = time.monotonic() + total_timeout_s

        try:
            process_env = os.environ.copy()
            configured_module_paths = tuple(
                getattr(self.cfg, "module_search_paths", ()) or ()
            )
            direct_environment_required = bool(
                extra_module_paths or configured_module_paths
            ) or output_path is not None
            resolved_lean_path = ""
            resolved_lean_executable = ""
            resolution_epoch = LeanREPL.global_env_epoch(
                str(self.project_dir.resolve())
            )

            async def capture_lake_env(*args: str) -> tuple[int, str]:
                with (
                    tempfile.TemporaryFile() as stdout_file,
                    tempfile.TemporaryFile() as stderr_file,
                ):
                    proc = subprocess.Popen(
                        ("lake", "env", *args),
                        cwd=str(self.project_dir),
                        stdout=stdout_file,
                        stderr=stderr_file,
                        start_new_session=True,
                    )

                    async def kill_and_reap() -> None:
                        try:
                            os.killpg(proc.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        reap_deadline = time.monotonic() + 5.0
                        while proc.poll() is None:
                            if time.monotonic() >= reap_deadline:
                                proc.kill()
                                break
                            await asyncio.sleep(0.01)
                        proc.poll()

                    try:
                        while proc.poll() is None:
                            remaining = operation_deadline - time.monotonic()
                            if remaining <= 0:
                                await kill_and_reap()
                                raise asyncio.TimeoutError
                            await asyncio.sleep(min(0.05, remaining))
                        returncode = int(proc.returncode or 0)
                    except asyncio.CancelledError:
                        await self._finish_cleanup_despite_cancellation(
                            kill_and_reap()
                        )
                        raise
                    stdout_file.seek(0)
                    stderr_file.seek(0)
                    stdout = stdout_file.read()
                    stderr = stderr_file.read()
                return returncode, (
                    stdout.decode("utf-8", errors="replace").strip()
                    or stderr.decode("utf-8", errors="replace").strip()
                )

            if direct_environment_required:
                cache_key = str(self.project_dir.resolve())
                while True:
                    if time.monotonic() >= operation_deadline:
                        return 1, "Lean timeout during environment resolution"
                    (
                        resolved_lean_path,
                        resolved_lean_executable,
                        resolution_epoch,
                    ) = self._configured_resolved_lean_environment()
                    if resolved_lean_path and resolved_lean_executable:
                        if LeanREPL.environment_epoch_is_current(
                            cache_key,
                            resolution_epoch,
                        ):
                            break
                        continue

                    path_rc, resolved_lean_path = await capture_lake_env(
                        "printenv",
                        "LEAN_PATH",
                    )
                    bin_rc, resolved_lean_executable = await capture_lake_env(
                        "which",
                        "lean",
                    )
                    if (
                        path_rc != 0
                        or bin_rc != 0
                        or not resolved_lean_path
                        or not resolved_lean_executable
                    ):
                        return 1, "could not resolve direct Lean environment"
                    if not LeanREPL.environment_epoch_is_current(
                        cache_key,
                        resolution_epoch,
                    ):
                        continue
                    if not self.bind_resolved_lean_environment(
                        resolved_lean_path,
                        resolved_lean_executable,
                        expected_epoch=resolution_epoch,
                    ):
                        continue
            module_paths = tuple(
                str(path)
                for path in (
                    *tuple(extra_module_paths),
                    *configured_module_paths,
                )
                if str(path).strip()
            )
            if module_paths:
                process_env["LEAN_PATH"] = os.pathsep.join(
                    (*module_paths, resolved_lean_path)
                ).rstrip(os.pathsep)
            lean_args = (
                *(("-R", str(extra_module_paths[0])) if extra_module_paths else ()),
                *(("-o", str(output_path)) if output_path is not None else ()),
                str(file_path),
            )
            total_timeout_s = operation_deadline - time.monotonic()
            if total_timeout_s <= 0:
                return 1, "Lean timeout during environment resolution"
            command = (
                (resolved_lean_executable, *lean_args)
                if direct_environment_required and resolved_lean_executable
                else ("lake", "env", "lean", *lean_args)
            )
            proc = await asyncio.create_subprocess_exec(
                *command,
                cwd=str(self.project_dir),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                start_new_session=True,
                env=process_env,
            )
            if dispatch_observer is not None:
                try:
                    dispatch_observer()
                except Exception:
                    pass
        except FileNotFoundError:
            return (
                1,
                "lake binary not found on PATH — install Lean/Lake or check PATH",
            )
        except asyncio.TimeoutError:
            return (1, "Lean timeout during environment resolution")
        except OSError as exc:
            return (1, f"failed to spawn lake process: {exc}")

        # Read output incrementally while enforcing only the hard timeout.
        stdout_chunks: list[bytes] = []
        stderr_chunks: list[bytes] = []
        got_any_output = False
        start_time = asyncio.get_running_loop().time()

        async def read_stream(
            stream: asyncio.StreamReader, chunks: list[bytes]
        ) -> None:
            nonlocal got_any_output
            while True:
                try:
                    chunk = await asyncio.wait_for(stream.read(4096), timeout=1.0)
                    if not chunk:
                        break
                    chunks.append(chunk)
                    got_any_output = True
                except asyncio.TimeoutError:
                    # Check if we should continue waiting
                    elapsed = asyncio.get_running_loop().time() - start_time
                    if elapsed > total_timeout_s:
                        break

        read_tasks: list[asyncio.Task[None]] = []
        wait_task: Optional[asyncio.Task[int]] = None
        try:
            # Start reading both streams
            if proc.stdout is not None:
                read_tasks.append(
                    asyncio.create_task(read_stream(proc.stdout, stdout_chunks))
                )
            if proc.stderr is not None:
                read_tasks.append(
                    asyncio.create_task(read_stream(proc.stderr, stderr_chunks))
                )

            # Wait for process with timeout using proc.wait() task
            # (polling proc.returncode is unreliable without proc.wait())
            wait_task = asyncio.create_task(proc.wait())

            while not wait_task.done():
                elapsed = asyncio.get_running_loop().time() - start_time

                # Check total timeout
                if elapsed > total_timeout_s:
                    logger.debug("Lean total timeout after %.1fs", elapsed)
                    await self._kill_proc(
                        proc,
                        wait_task=wait_task,
                        auxiliary_tasks=read_tasks,
                    )
                    return (
                        1,
                        _status_with_captured_output(
                            "Lean timeout", stdout_chunks, stderr_chunks
                        ),
                    )

                # Wait for process exit or next check interval
                check_interval = min(0.5, total_timeout_s - elapsed)
                await asyncio.wait({wait_task}, timeout=max(0.1, check_interval))

            # ``done()`` only polls liveness; it does not join the task or
            # retrieve a failure.  This task is the structured process-exit
            # child for the check, so consume its result before the enclosing
            # MiniSession transaction reaches its child-task barrier.
            wait_task.result()

            # Wait for read tasks to complete
            for task in read_tasks:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass

            # Drain any remaining output. A closed Lean that never EOFs used
            # to park the controller forever on a raw ``StreamReader.read()``.
            if proc.stdout:
                try:
                    remaining = await asyncio.wait_for(proc.stdout.read(), timeout=2.0)
                except asyncio.TimeoutError:
                    remaining = b""
                if remaining:
                    stdout_chunks.append(remaining)
            if proc.stderr:
                try:
                    remaining = await asyncio.wait_for(proc.stderr.read(), timeout=2.0)
                except asyncio.TimeoutError:
                    remaining = b""
                if remaining:
                    stderr_chunks.append(remaining)

            # Ensure process is fully cleaned up
            try:
                await asyncio.wait_for(proc.wait(), timeout=2.0)
            except asyncio.TimeoutError:
                pass

        except asyncio.CancelledError:
            async def _cleanup_cancelled_lake_process() -> None:
                await self._kill_proc(
                    proc,
                    wait_task=wait_task,
                    auxiliary_tasks=read_tasks,
                )

            await self._finish_cleanup_despite_cancellation(
                _cleanup_cancelled_lake_process()
            )
            raise
        except Exception as exc:
            await self._kill_proc(
                proc,
                wait_task=wait_task,
                auxiliary_tasks=read_tasks,
            )
            return (
                1,
                _status_with_captured_output(
                    f"Lean subprocess error: {exc}",
                    stdout_chunks,
                    stderr_chunks,
                ),
            )

        out = _captured_output_text(stdout_chunks, stderr_chunks)
        returncode = proc.returncode
        if returncode is None:
            logger.warning("Lean process returncode missing; treating as failure.")
            returncode = 1
        return (returncode, out)

    async def _execute_generated_file(
        self,
        *,
        mode: str = "raw",
        goal_name: str,
        content: str,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        warning_as_error: Optional[bool] = None,
        semaphore: Optional[asyncio.Semaphore] = None,
        retry_repl_termination: bool = True,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> tuple[Optional[Path], Optional[_BackendExecutionResult], Optional[str]]:
        """Write generated Lean content, run it, and clean up consistently."""
        result, file_path_str, backend_key = await self._execute_content(
            mode=mode,
            goal_name=goal_name,
            content=content,
            timeout_s=timeout_s,
            fast_fail_timeout_s=fast_fail_timeout_s,
            warning_as_error=warning_as_error,
            use_oracle_sem=(semaphore is self.suggest_sem),
            retry_repl_termination=retry_repl_termination,
            dispatch_observer=dispatch_observer,
        )
        returncode, out = result
        if backend_key == "disk_error":
            return None, None, out
        file_path = Path(file_path_str) if file_path_str else None
        return (
            file_path,
            _BackendExecutionResult(
                returncode=int(returncode),
                output=str(out),
                backend=str(backend_key or "lake"),
            ),
            None,
        )

    async def check(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        max_heartbeats: Optional[int] = None,
        check_kind: str = "full",
        warning_as_error: bool = False,
        dispatch_observer: Optional[Callable[[], None]] = None,
    ) -> LeanResult:
        # Phase A fix (2026-05-09): default ``warning_as_error`` flipped
        # to False. Lean's stylistic warnings — `try simp instead of
        # simpa`, `unused variable`, `unused simp argument`,
        # deprecation notes — escalated to errors and rejected
        # mathematically-valid proofs. PutnamBench grading does NOT
        # fail on warnings (only on `sorry`/`admit`/errors), so a
        # warning-passing proof IS a correct submission. Rejecting it
        # for style burned LLM turns AND Lean checks for zero
        # correctness gain.
        #
        # Callers that genuinely need strict mode (e.g., a final
        # publishable Lean file) can opt in via ``warning_as_error=True``.
        # The lower-level ``check_with_sorry()``,
        # ``check_term_type()``, and apply_decl_to_goal paths kept
        # their pre-existing False default unchanged.
        #
        # Warnings are still surfaced in the output, so the
        # post-failure cascade (and the LLM's next-turn feedback)
        # still see them — this just stops them from being a hard
        # rejection signal.
        await self.ensure_project_imports_built()
        await self._ensure_extra_imports_built(
            self._required_extra_imports_for_proof(proof_code)
        )
        # 2026-05-22: when the caller does not specify max_heartbeats,
        # fall back to an opt-in instance attribute set by callers like
        # mini_prover (`--lean-max-heartbeats`). This lifts the heartbeats
        # budget for every check call (try_lean tool + primary proof
        # verification + answer-safe recheck) without touching the ~30
        # individual ``lean.check(...)`` call sites or LeanConfig.
        if max_heartbeats is None:
            instance_default = getattr(self, "default_max_heartbeats", None)
            if isinstance(instance_default, int) and instance_default > 0:
                max_heartbeats = instance_default
        goal_name = f"goal_{short_id(statement + proof_code)}"
        lemma_block = "\n".join(lemmas) if lemmas else ""
        helper_audit_names = tuple(
            dict.fromkeys(
                name
                for name in (helper_decl_name(block) for block in lemmas or ())
                if name
            )
        )
        built = self._build_file(
            statement,
            proof_code,
            lemma_block,
            goal_name,
            preamble_override=preamble_override,
            warning_as_error=warning_as_error,
            max_heartbeats=max_heartbeats,
            axiom_audit_names=helper_audit_names,
        )
        lemma_line_spans: Tuple[Tuple[int, int], ...] = ()
        if built.lemma_block_start_line > 0:
            next_line = built.lemma_block_start_line
            spans: List[Tuple[int, int]] = []
            for lemma in lemmas:
                end_line = next_line + str(lemma).count("\n")
                spans.append((next_line, end_line))
                # ``"\n".join(lemmas)`` contributes one separator after
                # every non-final block; advancing one line is correct for
                # both the separator and any trailing newline in the block.
                next_line = end_line + 1
            lemma_line_spans = tuple(spans)
        content = built.content
        file_path, execution, write_error = await self._execute_generated_file(
            mode=check_kind,
            goal_name=goal_name,
            content=content,
            timeout_s=timeout_s,
            fast_fail_timeout_s=fast_fail_timeout_s,
            warning_as_error=warning_as_error,
            dispatch_observer=dispatch_observer,
        )
        if execution is None:
            # Parse the disk-write-failed / write-error string so the
            # resulting LeanResult.parsed exposes infra_failure=True to
            # callers. Previously this returned parsed=None, leaving
            # downstream classification to treat the disk-I/O failure as
            # a real Lean rejection.
            output = str(write_error or "disk write failed")
            return LeanResult(
                ok=False,
                output=output,
                file_path=str(file_path or ""),
                returncode=1,
                parsed=parse_lean_output(
                    output, 1, goal_start_line=built.goal_start_line
                ),
                generated_declaration_name=goal_name,
                generated_goal_start_line=built.goal_start_line,
                generated_lemma_line_spans=lemma_line_spans,
            )
        returncode, out = execution.returncode, execution.output
        parsed = parse_lean_output(
            out, returncode, goal_start_line=built.goal_start_line
        )
        axiom_audit: Dict[str, Tuple[str, ...]] = {}
        axiom_audit_ok: Optional[bool] = None
        unexpected_axioms: Tuple[str, ...] = ()
        axiom_audit_error = ""
        if returncode == 0:
            axiom_audit, axiom_audit_error = _parse_complete_axiom_audit(
                out,
                built.axiom_audit_names,
            )
            all_axioms = tuple(
                sorted(
                    {
                        axiom
                        for axioms in axiom_audit.values()
                        for axiom in axioms
                    }
                )
            )
            unexpected_axioms = tuple(
                axiom
                for axiom in all_axioms
                if axiom not in _ALLOWED_CHECK_AXIOMS
            )
            parsed.axioms = list(all_axioms)
            parsed.unexpected_axioms = list(unexpected_axioms)
            parsed.axiom_audit_error = axiom_audit_error
            if axiom_audit_error:
                axiom_audit_ok = False
                parsed.axiom_audit_ok = False
                parsed.infra_failure = True
                parsed.ok = False
                audit_message = (
                    "Lean axiom-audit infrastructure failed: "
                    f"{axiom_audit_error}"
                )
                parsed.diagnostics.append(
                    LeanDiagnostic(
                        file=str(file_path or ""),
                        line=0,
                        col=0,
                        severity="error",
                        message=audit_message,
                    )
                )
                parsed.raw = f"{parsed.raw}\n{audit_message}".strip()
                out = f"{out}\n{audit_message}".strip()
            elif unexpected_axioms:
                axiom_audit_ok = False
                parsed.axiom_audit_ok = False
                parsed.ok = False
                audit_message = (
                    "Lean proof rejected by axiom policy; unexpected axioms: "
                    + ", ".join(unexpected_axioms)
                )
                parsed.diagnostics.append(
                    LeanDiagnostic(
                        file=str(file_path or ""),
                        line=0,
                        col=0,
                        severity="error",
                        message=audit_message,
                    )
                )
                parsed.raw = f"{parsed.raw}\n{audit_message}".strip()
                out = f"{out}\n{audit_message}".strip()
            else:
                axiom_audit_ok = True
                parsed.axiom_audit_ok = True
        # Track off-block "Try this:" drops from the full check path too —
        # protects against a future caller that reads parsed.suggestions
        # from a non-oracle path. See RCA 2026-04-24.
        dropped = int(getattr(parsed.suggestions, "rejected_off_block", 0))
        if dropped:
            self._oracle_suggestions_off_block_dropped += dropped
        # Lean returns 0 for sorry (warning, not error) — reject these.
        ok = (
            returncode == 0
            and parsed.sorry_count == 0
            and axiom_audit_ok is True
        )
        check_kind_norm = str(check_kind or "full").strip().lower()
        self._check_count += 1
        if ok:
            self._check_ok_count += 1
        else:
            self._check_fail_count += 1
        if check_kind_norm == "precheck":
            self._precheck_check_count += 1
            if ok:
                self._precheck_ok_count += 1
            else:
                self._precheck_fail_count += 1
        else:
            self._full_check_count += 1
            if ok:
                self._full_check_ok_count += 1
            else:
                self._full_check_fail_count += 1
        return LeanResult(
            ok=ok,
            output=out,
            file_path=str(file_path or ""),
            returncode=int(returncode),
            parsed=parsed,
            axiom_audit_ok=axiom_audit_ok,
            axiom_audit=axiom_audit,
            unexpected_axioms=unexpected_axioms,
            axiom_audit_error=axiom_audit_error,
            generated_declaration_name=goal_name,
            generated_goal_start_line=built.goal_start_line,
            generated_lemma_line_spans=lemma_line_spans,
        )

    async def run_observation_commands(
        self,
        commands: Sequence[str],
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        max_heartbeats: Optional[int] = None,
        check_kind: str = "compute_examples",
        allow_solution_refs: bool = False,
    ) -> LeanResult:
        """Run answer-safe observational commands such as ``#eval``.

        Callers must sanitize commands before reaching this low-level method.
        The generated file is not evidence for proof closure; it exists only to
        expose Lean-computed observations back to the planner/model.
        """

        preamble = self._resolve_preamble(
            preamble_override,
            proof_code="\n".join(str(command or "") for command in commands or []),
        )
        safe_commands, validation_error = _validate_observation_commands(
            commands,
            preamble=preamble,
            allow_solution_refs=allow_solution_refs,
        )
        if validation_error:
            return LeanResult(
                ok=False,
                output=f"observation command rejected: {validation_error}",
                file_path="",
                returncode=1,
                parsed=parse_lean_output(validation_error, 1, goal_start_line=1),
            )
        heartbeat_lines: list[str] = []
        if max_heartbeats is None:
            instance_default = getattr(self, "default_max_heartbeats", None)
            if isinstance(instance_default, int) and instance_default > 0:
                max_heartbeats = instance_default
        try:
            normalized_heartbeats = int(
                max_heartbeats or _OBSERVATION_DEFAULT_MAX_HEARTBEATS
            )
        except Exception:
            normalized_heartbeats = _OBSERVATION_DEFAULT_MAX_HEARTBEATS
        normalized_heartbeats = max(
            1000,
            min(normalized_heartbeats, _OBSERVATION_MAX_HEARTBEATS),
        )
        heartbeat_lines.append(f"set_option maxHeartbeats {int(normalized_heartbeats)}")
        try:
            normalized_timeout_s = float(
                timeout_s
                if timeout_s is not None
                else _OBSERVATION_DEFAULT_TIMEOUT_S
            )
        except Exception:
            normalized_timeout_s = _OBSERVATION_DEFAULT_TIMEOUT_S
        normalized_timeout_s = max(
            1.0,
            min(normalized_timeout_s, _OBSERVATION_MAX_TIMEOUT_S),
        )
        content = "\n".join(
            part
            for part in (
                preamble,
                "\n".join(heartbeat_lines),
                "\n".join(safe_commands),
                "",
            )
            if part is not None
        )
        goal_name = f"compute_{short_id(content)}"
        file_path, execution, write_error = await self._execute_generated_file(
            mode=check_kind,
            goal_name=goal_name,
            content=content,
            timeout_s=normalized_timeout_s,
            fast_fail_timeout_s=None,
            warning_as_error=False,
        )
        if execution is None:
            output = str(write_error or "disk write failed")
            return LeanResult(
                ok=False,
                output=output,
                file_path=str(file_path or ""),
                returncode=1,
                parsed=parse_lean_output(output, 1, goal_start_line=1),
            )
        parsed = parse_lean_output(
            execution.output,
            int(execution.returncode),
            goal_start_line=1,
        )
        ok = int(execution.returncode) == 0 and not bool(
            getattr(parsed, "infra_failure", False)
        )
        return LeanResult(
            ok=ok,
            output=execution.output,
            file_path=str(file_path or ""),
            returncode=int(execution.returncode),
            parsed=parsed,
        )

    async def check_with_sorry(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
    ) -> LeanParseResult:
        """Run Lean with sorry warnings suppressed so we can extract goals.

        Returns a ``LeanParseResult`` with remaining goals after sorry
        holes are filled.  The result's ``ok`` indicates whether the
        proof would be accepted *if* all sorry holes were filled.
        """
        parsed, _, _ = await self.check_with_sorry_raw(
            statement,
            proof_code,
            lemmas,
            preamble_override=preamble_override,
        )
        return parsed

    async def check_with_sorry_raw(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        fast_fail_timeout_s: Optional[float] = None,
        max_heartbeats: Optional[int] = None,
    ) -> tuple[LeanParseResult, str, int]:
        """Like ``check_with_sorry`` but also returns raw output and returncode.

        This is useful for persistent caching: callers can store ``(output, rc)``
        and re-parse the goal state without re-running Lean.
        """
        await self.ensure_project_imports_built()
        await self._ensure_extra_imports_built(
            self._required_extra_imports_for_proof(proof_code)
        )
        # Fix follow-up (2026-05-22): mirror the maxHeartbeats fallback from
        # ``check`` so the sorry-probe path (helper_salvage, mini_recursive
        # preamble validation) also inherits the bumped budget. Previously
        # this method emitted no ``set_option maxHeartbeats`` and ran at
        # Lean's built-in 200k ceiling — sufficient for trivial probes but
        # too tight for genuine proof-body sorry checks.
        if max_heartbeats is None:
            instance_default = getattr(self, "default_max_heartbeats", None)
            if isinstance(instance_default, int) and instance_default > 0:
                max_heartbeats = instance_default
        goal_name = f"sorry_{short_id(statement + proof_code)}"
        lemma_block = "\n".join(lemmas) if lemmas else ""
        built = self._build_file(
            statement,
            proof_code,
            lemma_block,
            goal_name,
            preamble_override=preamble_override,
            warning_as_error=False,
            max_heartbeats=max_heartbeats,
        )
        content = built.content
        file_path, execution, write_error = await self._execute_generated_file(
            mode="sorry",
            goal_name=goal_name,
            content=content,
            timeout_s=timeout_s,
            fast_fail_timeout_s=fast_fail_timeout_s,
            warning_as_error=False,
        )
        if execution is None:
            out = str(write_error or "disk write failed")
            return (
                parse_lean_output(out, 1, goal_start_line=built.goal_start_line),
                out,
                1,
            )
        returncode, out = execution.returncode, execution.output
        self._check_count += 1
        self._sorry_check_count += 1
        if returncode == 0:
            self._sorry_check_ok_count += 1
        else:
            self._check_fail_count += 1
            self._sorry_check_fail_count += 1
        parsed_sorry = parse_lean_output(
            out, returncode, goal_start_line=built.goal_start_line
        )
        dropped = int(getattr(parsed_sorry.suggestions, "rejected_off_block", 0))
        if dropped:
            self._oracle_suggestions_off_block_dropped += dropped
        return (parsed_sorry, out, int(returncode))

    async def _run_lean_for_oracle(
        self,
        statement: str,
        proof_code: str,
        lemmas: List[str],
        preamble_override: str | None,
        timeout_s: float,
        max_heartbeats: int,
    ) -> LeanParseResult:
        """Run a single oracle tactic attempt and return the parsed result.

        Builds a Lean file with ``set_option maxHeartbeats`` and
        ``set_option warningAsError false``, then runs via REPL or lake
        using the oracle-specific semaphore (``suggest_sem``).
        """
        await self.ensure_project_imports_built()
        await self._ensure_extra_imports_built(
            self._required_extra_imports_for_proof(proof_code)
        )
        lemma_block = "\n".join(lemmas) if lemmas else ""
        goal_name = f"suggest_{short_id(statement + proof_code)}"
        built = self._build_file(
            statement,
            proof_code,
            lemma_block,
            goal_name,
            preamble_override=preamble_override,
            warning_as_error=False,
            max_heartbeats=max_heartbeats,
        )
        content = built.content
        _file_path, execution, write_error = await self._execute_generated_file(
            mode="oracle",
            goal_name=goal_name,
            content=content,
            timeout_s=timeout_s,
            fast_fail_timeout_s=timeout_s,
            warning_as_error=False,
            semaphore=self.suggest_sem,
        )
        if execution is None:
            logger.warning("oracle: failed to write temp file: %s", write_error)
            # Route through parse_lean_output so infra_failure=True gets
            # set — otherwise downstream oracle-outcome classifiers
            # treat the failure as authoritative "oracle rejected".
            return parse_lean_output(
                str(write_error or "disk write failed"),
                1,
                goal_start_line=built.goal_start_line,
            )
        returncode, out = execution.returncode, execution.output
        self._oracle_check_count += 1
        parsed = parse_lean_output(
            out, returncode, goal_start_line=built.goal_start_line
        )
        # Surface off-block "Try this:" drops via runner stats so the
        # orchestrator can include the count in its live-trace snapshot.
        # The suggestion list carries the count as a side-channel attribute
        # only when at least one suggestion was filtered.
        dropped = int(getattr(parsed.suggestions, "rejected_off_block", 0))
        if dropped:
            self._oracle_suggestions_off_block_dropped += dropped
        return parsed

    async def _identify_tier1_winner(
        self,
        statement: str,
        proof_with_sorry: str,
        lemmas: List[str],
        preamble_override: str | None,
        *,
        base_timeout_s: float = 1.0,
        max_heartbeats: int = 20000,
        run_oracle: Optional[
            Callable[
                [str, str, List[str], str | None, float, int],
                Awaitable[LeanParseResult],
            ]
        ] = None,
        remaining_wall_fn: Optional[Callable[[], float]] = None,
    ) -> Optional[str]:
        """After a combined Tier-1 call succeeds, identify which tactic won.

        Replays each Tier-1 tactic individually using the configured Tier-1
        budget, clamped to the remaining wall-clock budget when
        *remaining_wall_fn* is provided.  Returns the first concrete tactic
        that silently succeeds, or ``None`` if the exact winner cannot be
        distinguished and the caller should reuse the combined Tier-1 bundle.
        """
        for tactic in _TIER1_INDIVIDUAL:
            replaced, n = _SORRY_PATTERN.subn(tactic, proof_with_sorry, count=1)
            if n == 0:
                return None
            timeout_s = max(0.0, float(base_timeout_s))
            if remaining_wall_fn is not None:
                wall_left = remaining_wall_fn()
                if wall_left <= 0.0:
                    return None
                timeout_s = min(timeout_s, wall_left)
            if timeout_s <= 0.0:
                return None
            runner = run_oracle or self._run_lean_for_oracle
            parsed = await runner(
                statement,
                replaced,
                lemmas,
                preamble_override,
                timeout_s,
                int(max_heartbeats),
            )
            if is_oracle_silent_success(parsed):
                return tactic
        return None

    async def suggest_tactics(
        self,
        statement: str,
        proof_with_sorry: str,
        lemmas: List[str],
        *,
        preamble_override: str | None = None,
        commands: List[str] | Tuple[str, ...] = (),
        timeout_s: float = 60.0,
        max_heartbeats: int = 800000,
        oracle_cfg: TacticOracleConfig | None = None,
        metrics_out: dict | None = None,
        max_wall_s: float = 0.0,
        goal_text: str | None = None,
        goal_hypotheses: Sequence[str] = (),
        retrieved_lemma_names: Sequence[str] = (),
    ) -> List[str]:
        """Run Lean tactic suggestions on the first sorry hole.

        **Legacy mode** (``commands`` non-empty): runs each command
        sequentially with a single timeout, checking only for
        ``Try this:`` suggestions.  Backward-compatible with old configs
        that set ``commands: "exact?,apply?"``.

        **Tiered mode** (``commands`` empty, the new default): executes
        the full Lean 4 tactic vocabulary through a goal-aware family
        scheduler.  Per-tactic timeout/heartbeat budgets still come from
        the tactic's base tier (tier2/tier3/tier4/tier5).

        Args:
            oracle_cfg: ``TacticOracleConfig`` for per-tier timeouts
                and opt-in flags.  Only used in tiered mode.
            metrics_out: If provided, populated with ``winning_tier``
                and ``winning_tactic`` on success.
            max_wall_s: Total wall-clock budget for all tiers combined.
                0 = unlimited (default).  When exceeded, remaining tiers
                are skipped.  Useful for proactive goal-start calls.
            goal_text: Focused current-goal text used to bias tactic-family
                ordering without changing the proof being checked.
            goal_hypotheses: Current local hypotheses for the focused goal.
        """
        _wall_start = time.monotonic()
        _wall_limit = float(max_wall_s) if max_wall_s > 0 else 0.0

        def _wall_exceeded() -> bool:
            return _wall_limit > 0 and (time.monotonic() - _wall_start) > _wall_limit

        def _remaining_wall() -> float:
            if _wall_limit <= 0:
                return float("inf")
            return max(0.0, _wall_limit - (time.monotonic() - _wall_start))

        def _clamp_timeout(t: float) -> float:
            return min(t, _remaining_wall()) if _wall_limit > 0 else t

        oracle_checks_used = 0
        cfg = oracle_cfg
        focus = str(goal_text or statement or "").strip()
        sort_like_focus = is_standalone_sort_like_lean_expr(focus)
        prop_complete_enabled = (
            bool(getattr(cfg, "include_prop_complete", False)) if cfg else False
        )
        prop_complete_fragment_match = (
            prop_complete_enabled
            and not sort_like_focus
            and _prop_complete_applicable(
                statement,
                goal_text=goal_text,
                goal_hypotheses=goal_hypotheses,
            )
        )

        async def _run_oracle(
            stmt: str,
            proof: str,
            lemma_block: List[str],
            preamble: str | None,
            timeout_eff: float,
            hb: int,
        ) -> LeanParseResult:
            nonlocal oracle_checks_used
            oracle_checks_used += 1
            if metrics_out is not None:
                metrics_out["oracle_checks_used"] = int(oracle_checks_used)
            return await self._run_lean_for_oracle(
                stmt,
                proof,
                lemma_block,
                preamble,
                timeout_eff,
                hb,
            )

        if metrics_out is not None:
            metrics_out["prop_complete_enabled"] = int(prop_complete_enabled)
            metrics_out["prop_complete_fragment_match"] = int(
                prop_complete_fragment_match
            )
            metrics_out["prop_complete_attempted"] = 0
            metrics_out["prop_complete_skipped_non_fragment"] = int(
                prop_complete_enabled and not prop_complete_fragment_match
            )
            metrics_out["specs_tried"] = int(metrics_out.get("specs_tried", 0) or 0)

        specs_tried = int(metrics_out.get("specs_tried", 0) or 0) if metrics_out is not None else 0

        def _record_spec_attempt() -> None:
            nonlocal specs_tried
            specs_tried += 1
            if metrics_out is not None:
                metrics_out["specs_tried"] = int(specs_tried)
        if sort_like_focus:
            return []

        # -----------------------------------------------------------
        # LEGACY MODE: explicit commands list provided
        # -----------------------------------------------------------
        if commands:
            legacy_commands = [str(cmd).strip() for cmd in commands if str(cmd).strip()]
            if prop_complete_fragment_match and "prop_complete" not in legacy_commands:
                legacy_commands = ["prop_complete", *legacy_commands]
            for cmd in legacy_commands:
                if _wall_exceeded():
                    if metrics_out is not None:
                        metrics_out["wall_exceeded"] = 1
                        metrics_out["specs_tried"] = specs_tried
                    return []
                replaced, n_subs = _SORRY_PATTERN.subn(cmd, proof_with_sorry, count=1)
                if n_subs == 0:
                    return []
                timeout_eff = _clamp_timeout(timeout_s)
                if timeout_eff <= 0.0:
                    if metrics_out is not None:
                        metrics_out["wall_exceeded"] = 1
                        metrics_out["specs_tried"] = specs_tried
                    return []
                if metrics_out is not None and cmd == "prop_complete":
                    metrics_out["prop_complete_attempted"] = (
                        int(metrics_out.get("prop_complete_attempted", 0)) + 1
                    )
                _record_spec_attempt()
                parsed = await _run_oracle(
                    statement,
                    replaced,
                    lemmas,
                    preamble_override,
                    timeout_eff,
                    max_heartbeats,
                )
                if parsed.suggestions:
                    return parsed.suggestions
                if is_oracle_silent_success(parsed):
                    return [cmd]
            return []

        # -----------------------------------------------------------
        # TIERED MODE: full vocabulary
        # -----------------------------------------------------------
        # Per-tier timeout / heartbeat budgets (from config or defaults)
        t1_timeout = float(getattr(cfg, "tier1_timeout_s", 5)) if cfg else 5.0
        t1_hb = int(getattr(cfg, "tier1_max_heartbeats", 50000)) if cfg else 50000
        t2_timeout = float(getattr(cfg, "tier2_timeout_s", 8)) if cfg else 8.0
        t2_hb = int(getattr(cfg, "tier2_max_heartbeats", 200000)) if cfg else 200000
        t3_timeout = float(getattr(cfg, "tier3_timeout_s", 15)) if cfg else 15.0
        t3_hb = int(getattr(cfg, "tier3_max_heartbeats", 400000)) if cfg else 400000
        if not self._configured_use_repl():
            # Direct `lake env lean` has measurable process startup overhead.
            # Keep Tier-1 viable on the fallback backend without changing the
            # configured REPL fast path.
            t1_timeout = max(t1_timeout, 5.0)

        def _record(tier: str, tactic: str, family: str | None = None) -> None:
            if metrics_out is not None:
                metrics_out["winning_tier"] = tier
                metrics_out["winning_tactic"] = tactic
                if family:
                    metrics_out["winning_family"] = family

        async def _try_prop_complete_probe() -> bool:
            if not prop_complete_fragment_match:
                return False
            replaced, n = _SORRY_PATTERN.subn(
                "prop_complete", proof_with_sorry, count=1
            )
            if n == 0:
                return False
            timeout_eff = _clamp_timeout(
                float(getattr(cfg, "prop_complete_timeout_s", 8)) if cfg else 8.0
            )
            if timeout_eff <= 0.0:
                return False
            if metrics_out is not None:
                metrics_out["prop_complete_attempted"] = (
                    int(metrics_out.get("prop_complete_attempted", 0)) + 1
                )
            _record_spec_attempt()
            parsed = await _run_oracle(
                statement,
                replaced,
                lemmas,
                preamble_override,
                timeout_eff,
                (
                    int(getattr(cfg, "prop_complete_max_heartbeats", 200000))
                    if cfg
                    else 200000
                ),
            )
            if is_oracle_silent_success(parsed):
                _record("tier5", "prop_complete", "propositional")
                return True
            return False

        if await _try_prop_complete_probe():
            return ["prop_complete"]

        # -- Step A: Tier 1 combined call --
        replaced, n = _SORRY_PATTERN.subn(_TIER1_COMBINED, proof_with_sorry, count=1)
        if n == 0:
            return []  # No sorry in proof
        if _wall_exceeded():
            if metrics_out is not None:
                metrics_out["wall_exceeded"] = 1
                metrics_out["specs_tried"] = specs_tried
            return []
        t1_timeout_eff = _clamp_timeout(t1_timeout)
        if t1_timeout_eff <= 0.0:
            if metrics_out is not None:
                metrics_out["wall_exceeded"] = 1
                metrics_out["specs_tried"] = specs_tried
            return []
        _record_spec_attempt()
        parsed = await _run_oracle(
            statement,
            replaced,
            lemmas,
            preamble_override,
            t1_timeout_eff,
            t1_hb,
        )
        if is_oracle_silent_success(parsed):
            winner = await self._identify_tier1_winner(
                statement,
                proof_with_sorry,
                lemmas,
                preamble_override,
                base_timeout_s=t1_timeout,
                max_heartbeats=t1_hb,
                run_oracle=_run_oracle,
                remaining_wall_fn=_remaining_wall if _wall_limit > 0 else None,
            )
            concrete_tactic = winner or _TIER1_COMBINED
            _record("tier1", concrete_tactic)
            return [concrete_tactic]

        # -- Steps B-D: goal-aware tactic scan across base tiers + domain opt-ins --
        tier_budgets: Dict[str, Tuple[float, int]] = {
            "tier2": (t2_timeout, t2_hb),
            "tier3": (t3_timeout, t3_hb),
            "tier4": (float(timeout_s), int(max_heartbeats)),
            "tier5": (float(timeout_s), int(max_heartbeats)),
        }
        for spec in _goal_aware_oracle_specs(
            statement,
            goal_text=goal_text,
            goal_hypotheses=goal_hypotheses,
            tactic_oracle_cfg=cfg,
        ):
            if _wall_exceeded():
                if metrics_out is not None:
                    metrics_out["wall_exceeded"] = 1
                    metrics_out["specs_tried"] = specs_tried
                return []
            replaced, n = _SORRY_PATTERN.subn(spec.tactic, proof_with_sorry, count=1)
            if n == 0:
                return []
            base_timeout, base_heartbeats = tier_budgets.get(
                spec.tier, (float(timeout_s), int(max_heartbeats))
            )
            timeout_eff = _clamp_timeout(base_timeout)
            if timeout_eff <= 0.0:
                return []
            _record_spec_attempt()
            parsed = await _run_oracle(
                statement,
                replaced,
                lemmas,
                preamble_override,
                timeout_eff,
                base_heartbeats,
            )
            if spec.suggestion_tactic:
                if parsed.suggestions:
                    _record(spec.tier, parsed.suggestions[0], spec.family)
                    return parsed.suggestions
                continue
            if is_oracle_silent_success(parsed):
                _record(spec.tier, spec.tactic, spec.family)
                return [spec.tactic]
            # Some tactics (for example `simp`) may emit suggestions even when
            # they do not close the goal themselves.
            if parsed.suggestions:
                _record(spec.tier, parsed.suggestions[0], spec.family)
                return parsed.suggestions

        # -- Step D.5: Retrieval-informed tactics --
        # Try exact/apply/simp/rw with retrieved Mathlib lemma names.
        # These are targeted checks (specific lemma, tier-2 budget) vs
        # exhaustive search (exact?/simp?, tier-4, 30-60s).
        _ri_enabled = bool(
            getattr(cfg, "retrieval_informed_enabled", True) if cfg else True
        )
        if _ri_enabled and retrieved_lemma_names and not _wall_exceeded():
            _ri_max = int(
                getattr(cfg, "retrieval_informed_max_lemmas", 5) if cfg else 5
            )
            _ri_timeout = float(
                getattr(cfg, "retrieval_informed_timeout_s", 3.0) if cfg else 3.0
            )
            _ri_hb = int(
                getattr(cfg, "retrieval_informed_max_heartbeats", 50000)
                if cfg
                else 50000
            )
            _RI_PATTERNS = ("exact {}", "apply {}", "simp only [{}]", "rw [{}]")
            for _ri_lemma in retrieved_lemma_names[:_ri_max]:
                if _wall_exceeded():
                    break
                for _ri_pat in _RI_PATTERNS:
                    if _wall_exceeded():
                        break
                    _ri_tactic = _ri_pat.format(_ri_lemma)
                    # Use lambda to avoid regex interpretation of the replacement string
                    # (lemma names could contain backslash sequences that crash re.subn).
                    replaced = _SORRY_PATTERN.sub(
                        lambda _m: _ri_tactic, proof_with_sorry, count=1
                    )
                    n = 1 if replaced != proof_with_sorry else 0
                    if n > 0:
                        timeout_eff = _clamp_timeout(_ri_timeout)
                        if timeout_eff <= 0.0:
                            break
                        if metrics_out is not None:
                            metrics_out["oracle_retrieval_informed_attempts"] = (
                                int(
                                    metrics_out.get(
                                        "oracle_retrieval_informed_attempts", 0
                                    )
                                )
                                + 1
                            )
                        _record_spec_attempt()
                        parsed = await _run_oracle(
                            statement,
                            replaced,
                            lemmas,
                            preamble_override,
                            timeout_eff,
                            _ri_hb,
                        )
                        if is_oracle_silent_success(parsed):
                            _record("retrieval_informed", _ri_tactic)
                            if metrics_out is not None:
                                metrics_out["oracle_retrieval_informed_hits"] = (
                                    int(
                                        metrics_out.get(
                                            "oracle_retrieval_informed_hits", 0
                                        )
                                    )
                                    + 1
                                )
                            return [_ri_tactic]

        # -- Step E: Tier 5 — opt-in tactics --
        if _wall_exceeded():
            return []

        if getattr(cfg, "include_decide", True) if cfg else True:
            d_timeout = float(getattr(cfg, "decide_timeout_s", 10)) if cfg else 10.0
            d_hb = int(getattr(cfg, "decide_max_heartbeats", 150000)) if cfg else 150000
            replaced, n = _SORRY_PATTERN.subn("decide", proof_with_sorry, count=1)
            if n > 0:
                timeout_eff = _clamp_timeout(d_timeout)
                if timeout_eff <= 0.0:
                    return []
                _record_spec_attempt()
                parsed = await _run_oracle(
                    statement,
                    replaced,
                    lemmas,
                    preamble_override,
                    timeout_eff,
                    d_hb,
                )
                if is_oracle_silent_success(parsed):
                    _record("tier5", "decide")
                    return ["decide"]

        if getattr(cfg, "include_native_decide", False) if cfg else False:
            if _wall_exceeded():
                return []
            nd_timeout = float(getattr(cfg, "decide_timeout_s", 10)) if cfg else 10.0
            nd_hb = (
                int(getattr(cfg, "decide_max_heartbeats", 150000)) if cfg else 150000
            )
            replaced, n = _SORRY_PATTERN.subn(
                "native_decide", proof_with_sorry, count=1
            )
            if n > 0:
                timeout_eff = _clamp_timeout(nd_timeout)
                if timeout_eff > 0.0:
                    _record_spec_attempt()
                    parsed = await _run_oracle(
                        statement,
                        replaced,
                        lemmas,
                        preamble_override,
                        timeout_eff,
                        nd_hb,
                    )
                    if is_oracle_silent_success(parsed):
                        _record("tier5", "native_decide")
                        return ["native_decide"]

        if getattr(cfg, "include_grind", True) if cfg else True:
            if _wall_exceeded():
                return []
            g_timeout = float(getattr(cfg, "grind_timeout_s", 20)) if cfg else 20.0
            g_hb = int(getattr(cfg, "grind_max_heartbeats", 600000)) if cfg else 600000
            replaced, n = _SORRY_PATTERN.subn("grind", proof_with_sorry, count=1)
            if n > 0:
                timeout_eff = _clamp_timeout(g_timeout)
                if timeout_eff <= 0.0:
                    return []
                _record_spec_attempt()
                parsed = await _run_oracle(
                    statement,
                    replaced,
                    lemmas,
                    preamble_override,
                    timeout_eff,
                    g_hb,
                )
                if is_oracle_silent_success(parsed):
                    _record("tier5", "grind")
                    return ["grind"]

        return []

    def get_stats(self) -> Dict[str, Any]:
        """Return Lean runner throughput statistics."""
        total_work = max(1, self._check_count + self._oracle_check_count)
        wall = max(0.001, self._total_check_time_s)
        repl_cache_stats: Dict[str, int] = {}
        persistent_stats: Dict[str, Any] = {}
        if self._repl is not None and hasattr(self._repl, "global_cache_stats"):
            try:
                repl_cache_stats = self._repl.global_cache_stats()
            except Exception:
                repl_cache_stats = {}
        if self._persistent_pool is not None:
            try:
                persistent_stats = self._persistent_pool.stats()
            except Exception:
                persistent_stats = {}
        backend_caps = self._backend_capabilities(self._last_backend_key)
        persistent_fallbacks = int(
            persistent_stats.get("persistent_backend_fallbacks", 0)
        ) + int(self._persistent_fallback_count)
        return {
            "runner_invocation_count": self._check_count,
            "work_invocation_count": self._check_count + self._oracle_check_count,
            "runner_returncode_ok_count": self._check_ok_count
            + self._sorry_check_ok_count,
            "runner_returncode_fail_count": self._check_fail_count,
            "full_check_count": self._full_check_count,
            "full_check_ok_count": self._full_check_ok_count,
            "full_check_fail_count": self._full_check_fail_count,
            "precheck_check_count": self._precheck_check_count,
            "precheck_ok_count": self._precheck_ok_count,
            "precheck_fail_count": self._precheck_fail_count,
            "sorry_check_count": self._sorry_check_count,
            "sorry_check_returncode_ok_count": self._sorry_check_ok_count,
            "sorry_check_returncode_fail_count": self._sorry_check_fail_count,
            "oracle_check_count": self._oracle_check_count,
            "lean_oracle_suggestions_off_block_dropped": int(
                self._oracle_suggestions_off_block_dropped
            ),
            "persistent_check_count": self._persistent_check_count,
            "repl_check_count": self._repl_check_count,
            "lake_check_count": self._lake_check_count,
            "request_dedup_hits": self._request_dedup_hits,
            "request_dedup_hits_full": self._request_dedup_hits_full,
            "request_dedup_hits_sorry": self._request_dedup_hits_sorry,
            "request_dedup_hits_oracle": self._request_dedup_hits_oracle,
            "request_dedup_hits_raw": self._request_dedup_hits_raw,
            "repl_start_failures": self._repl_start_failures,
            "repl_runtime_failures": self._repl_runtime_failures,
            "repl_restart_count": self._repl_restart_count,
            "repl_fallback_count": self._repl_fallback_count,
            "persistent_fallback_count": self._persistent_fallback_count,
            "total_check_time_s": round(self._total_check_time_s, 2),
            "total_queue_wait_s": round(self._total_queue_wait_s, 2),
            "max_check_time_s": round(self._max_check_time_s, 2),
            "max_queue_wait_s": round(self._max_queue_wait_s, 2),
            "peak_active_checks": self._peak_active_checks,
            "max_parallel": self.cfg.max_parallel,
            "avg_check_time_s": round(self._total_check_time_s / total_work, 2),
            "avg_queue_wait_s": round(self._total_queue_wait_s / total_work, 2),
            "throughput_checks_per_min": round(total_work / (wall / 60.0), 1),
            "backend_kind_last": str(backend_caps.get("backend_kind", "")),
            "backend_supports_silence_fast_fail": bool(
                backend_caps.get("supports_silence_fast_fail", False)
            ),
            "backend_persistent_process": bool(
                backend_caps.get("persistent_process", False)
            ),
            "backend_caches_environment": bool(
                backend_caps.get("caches_environment", False)
            ),
            "supports_silent_fast_fail": False,
            "timeout_mode": "hard_timeout_only",
            "repl_startup_time_s": round(self._repl_startup_time_s, 3),
            "repl_global_cache_entries": int(repl_cache_stats.get("entries", 0)),
            "repl_global_cache_hits": int(repl_cache_stats.get("hits", 0)),
            "repl_global_cache_misses": int(repl_cache_stats.get("misses", 0)),
            **persistent_stats,
            "persistent_backend_fallbacks": int(persistent_fallbacks),
        }

    def reset_stats(self) -> None:
        """Reset throughput counters (e.g. between problems)."""
        self._check_count = 0
        self._check_ok_count = 0
        self._check_fail_count = 0
        self._full_check_count = 0
        self._full_check_ok_count = 0
        self._full_check_fail_count = 0
        self._precheck_check_count = 0
        self._precheck_ok_count = 0
        self._precheck_fail_count = 0
        self._sorry_check_count = 0
        self._sorry_check_ok_count = 0
        self._sorry_check_fail_count = 0
        self._oracle_check_count = 0
        self._oracle_suggestions_off_block_dropped = 0
        self._persistent_check_count = 0
        self._repl_check_count = 0
        self._lake_check_count = 0
        self._repl_start_failures = 0
        self._repl_runtime_failures = 0
        self._repl_restart_count = 0
        self._repl_fallback_count = 0
        self._persistent_fallback_count = 0
        self._repl_startup_time_s = 0.0
        self._request_dedup_hits = 0
        self._request_dedup_hits_full = 0
        self._request_dedup_hits_sorry = 0
        self._request_dedup_hits_oracle = 0
        self._request_dedup_hits_raw = 0
        self._total_check_time_s = 0.0
        self._total_queue_wait_s = 0.0
        self._max_check_time_s = 0.0
        self._max_queue_wait_s = 0.0
        self._peak_active_checks = 0
        if self._persistent_pool is not None and hasattr(self._persistent_pool, "reset_stats"):
            try:
                self._persistent_pool.reset_stats()
            except Exception:
                logger.debug("Failed to reset persistent verifier pool stats", exc_info=True)

    @staticmethod
    def _normalize_check_term_name(term: str) -> tuple[str, str]:
        """Return a single-command Lean expression for ``#check``.

        ``#check`` accepts terms, not only declaration names.  Restricting this
        boundary to dotted identifiers silently changed useful probes such as
        ``Finset.strongInductionOn (motive := ...)`` into a check of the bare
        declaration.  This layer rejects obvious multiline/comment/delimiter
        hazards; ``check_term_type`` separately requires a non-bare candidate
        to parse as exactly one complete term before interpolation. Bare names
        retain the historical ``@name`` rendering so implicit arguments remain
        visible.
        """
        raw = str(term or "").strip()
        sanitized = " ".join(raw.replace("\r", "\n").splitlines()).strip()
        if not sanitized:
            return "", "Error: empty term"
        if len(sanitized) > 2000:
            return "", "Error: unsupported check_type term: expression is too long"
        if any(token in raw for token in ("\n", "\r", "#", "--", "/-", "-/")):
            return "", f"Error: unsupported check_type term: {sanitized[:80]}"
        # ``#check`` is a type inspector, not a scratch proof verifier.
        # Admitted proof blocks can acquire an apparent proposition type
        # without providing evidence for it. Ordinary ``?_`` probes remain
        # useful for inspecting application obligations; they are safe here
        # because a nonzero Lean result never returns an info signature.
        if re.search(
            r"(?<![\w'])(?:by|sorry|admit)(?![\w'])",
            sanitized,
        ):
            return "", f"Error: unsupported check_type term: {sanitized[:80]}"
        if not lean_expression_delimiters_balanced(sanitized):
            return "", f"Error: unsupported check_type term: {sanitized[:80]}"
        return sanitized, ""

    @staticmethod
    def _complete_check_signature_from_output(output: str) -> str:
        """Recover one complete, possibly wrapped, ``#check`` info payload.

        Subprocess and LSP transports do not always agree on whether wrapped
        pretty-printer lines belong to the diagnostic message.  The old raw
        fallback returned the first line containing `` : `` and discarded all
        continuation binders.  Collect the diagnostic block (or indented plain
        continuation lines) and let the caller compare it with parsed info.
        """
        lines = str(output or "").splitlines()
        header_re = re.compile(
            r"^[^\n]+?:\d+:\d+:\s*(?:error|warning|info)(?:\([^)]+\))?:\s*(.*)$"
        )
        candidates: list[str] = []
        for index, line in enumerate(lines):
            header = header_re.match(line)
            payload = header.group(1).strip() if header else line.strip()
            if " : " not in payload or payload.startswith("--"):
                continue
            block = [payload]
            for continuation in lines[index + 1 :]:
                if header_re.match(continuation):
                    break
                if not continuation.strip():
                    break
                # Pretty-printer continuations are indented.  Do not absorb
                # unrelated runner prose that happens to follow the result.
                if continuation == continuation.lstrip():
                    break
                block.append(continuation.rstrip())
            candidates.append("\n".join(block).strip())
        return max(candidates, key=len, default="")

    async def check_term_type(
        self,
        term: str,
        *,
        preamble_override: str | None = None,
        lemmas: Optional[List[str]] = None,
        timeout_s: float = 10.0,
    ) -> str:
        """Run ``#check <term>`` and return the type string.

        Uses the oracle semaphore and the same REPL/lake fallback as
        ``suggest_tactics``.  Returns a string like
        ``"Real.sqrt_pos : 0 < √x ↔ 0 < x"`` on success, or an error
        description on failure.
        """
        preamble = self._resolve_preamble(preamble_override)
        sanitized, error = self._normalize_check_term_name(term)
        if error:
            return error
        goal_name = f"check_{short_id(sanitized)}"
        lemma_block = "\n".join(list(lemmas or []))
        # Same free-universe declaration as _build_file: under LSP-strict
        # autoImplicit=false, lemma_block content like
        # `lemma helper_x : ∀ (S : Type u), ...` requires a top-level
        # `universe u` declaration BEFORE the lemma. Without it the
        # whole `#check` wrapper rejects with `unknown universe level u`
        # at the lemma definition, then `[Error pretty printing
        # signature: incorrect number of universe levels ...]` for the
        # `#check` itself. Live trace 2001_a1_16apr_11.jsonl: every
        # `check_type` call on a solved synthetic lemma hit this path.
        universe_scan_text = "\n".join(part for part in (lemma_block,) if part)
        universe_decl = _free_universe_decl(universe_scan_text)
        head_universe_decl = f"{universe_decl}\n\n" if universe_decl else ""
        rendered_term = (
            f"@{sanitized}"
            if _SAFE_CHECK_NAME_RE.fullmatch(sanitized)
            else f"({sanitized})"
        )
        if not _SAFE_CHECK_NAME_RE.fullmatch(sanitized):
            # Lean's command parser performs error recovery: wrapping an
            # untrusted string in parentheses is not enough, because input
            # like ``Nat run_cmd ...`` can recover at ``run_cmd`` and execute
            # it as a second command. Parse the JSON-escaped string as the
            # *term category with end-of-input required* in a separate file.
            # The candidate is data in this phase and therefore cannot run.
            parse_literal = json.dumps(sanitized, ensure_ascii=False)
            parse_content = (
                f"{preamble}\n\n"
                f"{head_universe_decl}"
                f"{lemma_block}\n\n"
                "open Lean Elab Command\n"
                "run_cmd\n"
                "  match Lean.Parser.runParserCategory (← getEnv) `term "
                f"{parse_literal} with\n"
                "  | .ok _ => pure ()\n"
                "  | .error e => throwError e\n"
            )
            (
                _parse_file_path,
                parse_execution,
                _parse_write_error,
            ) = await self._execute_generated_file(
                goal_name=f"{goal_name}_parse",
                content=parse_content,
                timeout_s=timeout_s,
                fast_fail_timeout_s=timeout_s,
                semaphore=self.suggest_sem,
            )
            if parse_execution is None:
                return "Note: type information unavailable (verifier busy)"
            if int(parse_execution.returncode or 0) != 0:
                return (
                    "Error: unsupported check_type term: expression must be "
                    "exactly one complete Lean term"
                )
        content = (
            f"{preamble}\n\n"
            f"{head_universe_decl}"
            f"{lemma_block}\n\n"
            f"set_option maxHeartbeats 200000 in\n"
            f"#check {rendered_term}\n"
        )
        _file_path, execution, write_error = await self._execute_generated_file(
            goal_name=goal_name,
            content=content,
            timeout_s=timeout_s,
            fast_fail_timeout_s=timeout_s,
            semaphore=self.suggest_sem,
        )
        if execution is None:
            return "Note: type information unavailable (verifier busy)"

        returncode, out = execution.returncode, execution.output
        # #check output appears as an info diagnostic: "<file>:N:M: info: <name> : <type>"
        parsed = parse_lean_output(out, returncode)
        # Infrastructure failure (LSP timeout / worker crash / transport
        # error) is NOT a Lean error — surfacing it to the tool-loop LLM
        # as ``Error: persistent verifier timed out ...`` caused the
        # model to try to "fix" a phantom Lean error, wasting budget.
        # Return a distinct sentinel the tool-loop handler can treat as
        # "skip, infra problem" rather than "fix this Lean error".
        if bool(getattr(parsed, "infra_failure", False)):
            # Don't surface the raw infra error to the tool-loop LLM —
            # it would treat "persistent verifier timed out" as a Lean
            # error and attempt to fix it. Return a neutral sentinel so
            # the LLM moves on (the declaration was not verified, but
            # that is not a signal to the LLM's proof search).
            return "Note: type information unavailable (verifier busy)"
        signature_candidates: List[str] = []
        for diag in getattr(parsed, "diagnostics", []):
            if getattr(diag, "severity", "") == "info":
                msg = str(getattr(diag, "message", "") or "").strip()
                if msg and " : " in msg:
                    signature_candidates.append(msg)
        raw_signature = self._complete_check_signature_from_output(out)
        if raw_signature:
            signature_candidates.append(raw_signature)
        if returncode == 0 and signature_candidates:
            return max(signature_candidates, key=len)
        if returncode != 0:
            error_type = canonical_error_type(parsed) or "lean_error"
            parts = [f"Error: #check failed ({error_type}) for `{sanitized}`."]
            if error_type == "unknown_identifier":
                parts.append(
                    "That declaration is not available in this environment."
                )
            elif error_type == "unknown_universe":
                parts.append("The check refers to an unavailable universe level.")
            elif error_type == "parse_error":
                parts.append("The check term is not valid Lean declaration syntax.")
            error_diagnostics = [
                diag
                for diag in list(getattr(parsed, "diagnostics", []) or [])
                if str(getattr(diag, "severity", "") or "").lower() == "error"
            ]
            for diag in error_diagnostics[:2]:
                message = str(getattr(diag, "message", "") or "")
                summary = diagnostic_preview(message, canonical_error=error_type)
                if summary:
                    parts.append(summary[:240])
            return " ".join(parts)
        return out.strip()[:500] if out.strip() else "Error: no output"

    async def check_source_declaration_type(
        self,
        source: str,
        theorem_name: str,
        *,
        timeout_s: float = 60.0,
        pp_explicit: bool = False,
        pp_universes: bool = False,
    ) -> tuple[bool, str, str]:
        """Compile an exact input module and return its elaborated root type.

        Lean's default pretty printer is intentionally compact and its output
        is not always self-contained source. For example, an expected ``Rat``
        type can disambiguate ``(d - 1)⁻¹`` in the original declaration while
        disappearing from the rendered expression. ``pp_explicit`` is the
        fail-safe serialization used only after the compact rendering fails an
        independent elaboration check.
        """

        sanitized, error = self._normalize_check_term_name(theorem_name)
        if error:
            return False, "", error
        # ``#check`` is a display command, not a source serializer. Its
        # default delaborator omits dependent Pi/Exists binder types whenever
        # the surrounding expression supplies enough expected-type context
        # (for example ``∃ n t, ... t i ...``). Once copied into a standalone
        # axiom that context is gone and the rendered type no longer
        # elaborates. Force binder annotations at the source boundary while
        # retaining readable notation and names.
        printer_prefix = (
            f"set_option pp.universes {str(bool(pp_universes)).lower()} in\n"
            "set_option pp.piBinderTypes true in\n"
            "set_option pp.funBinderTypes true in\n"
        )
        if pp_explicit:
            printer_prefix += "set_option pp.explicit true in\n"
        content = (
            str(source or "").rstrip()
            + "\n\n"
            + printer_prefix
            + f"#check @_root_.{sanitized}\n"
            + "#check Prop\n"
        )
        _path, execution, write_error = await self._execute_generated_file(
            goal_name=f"source_type_{short_id(sanitized + content)}",
            content=content,
            timeout_s=max(1.0, float(timeout_s)),
            fast_fail_timeout_s=None,
            semaphore=self.sem,
        )
        if execution is None:
            return False, "", str(write_error or "source type probe unavailable")
        output = str(execution.output or "")
        if int(execution.returncode) != 0:
            return False, "", output
        rendered_types = self._checked_declaration_types_from_output(
            output,
            (sanitized,),
            returncode=execution.returncode,
        )
        complete_type = rendered_types.get(sanitized, "")
        if complete_type:
            return True, complete_type, output
        return False, "", output + "\nmissing exact #check type report"

    async def check_source_declaration_type_equivalence(
        self,
        source: str,
        theorem_name: str,
        rendered_type: str,
        *,
        timeout_s: float = 60.0,
        preamble_override: str | None = None,
    ) -> tuple[LeanParseResult, str, int]:
        """Prove that a rendered type is still the source declaration's type.

        A successful standalone elaboration only proves that pretty-printed
        text has *some* meaning. Overloaded notation can silently acquire a
        different meaning after expected-type annotations disappear. Compile
        the exact source again and compare the candidate with the declaration's
        kernel type using ``Meta.isDefEq``. Universe schemas are alpha-renamed
        to a shared rigid parameter list first, preventing both coercion-based
        conversions and silent specialization of polymorphic declarations.
        """

        sanitized, error = self._normalize_check_term_name(theorem_name)
        candidate = str(rendered_type or "").strip()
        if error or not candidate:
            output = str(error or "rendered source type is empty")
            return parse_lean_output(output, 1), output, 1
        operation_timeout = max(1.0, float(timeout_s))
        operation_deadline = time.monotonic() + operation_timeout
        universe_decl = _free_universe_decl(candidate, declared_in=source)
        candidate_literal = json.dumps(candidate, ensure_ascii=False)
        source_term_literal = json.dumps(
            f"@_root_.{sanitized}",
            ensure_ascii=False,
        )
        probe = "\n".join(
            (
                "run_cmd Lean.Elab.Command.liftTermElabM do",
                "  let candidateStx ←",
                "    match Lean.Parser.runParserCategory (← Lean.getEnv) `term",
                f"        {candidate_literal} with",
                "    | .ok stx => pure stx",
                "    | .error error => Lean.throwError error",
                "  let candidateType ← Lean.Elab.Term.withoutErrToSorry do",
                "    Lean.Elab.Term.elabType candidateStx",
                "  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing",
                "  let candidateType ← Lean.instantiateMVars candidateType",
                "  let candidateLevelParams :=",
                "    (Lean.collectLevelParams {} candidateType).params.toList",
                "  let sourceStx ←",
                "    match Lean.Parser.runParserCategory (← Lean.getEnv) `term",
                f"        {source_term_literal} with",
                "    | .ok stx => pure stx",
                "    | .error error => Lean.throwError error",
                "  let sourceTerm ← Lean.Elab.Term.withoutErrToSorry do",
                "    Lean.Elab.Term.elabTerm sourceStx none",
                "  let some sourceName := sourceTerm.getAppFn.constName?",
                '    | Lean.throwError "source theorem did not elaborate to a constant"',
                "  let sourceInfo ← Lean.getConstInfo sourceName",
                "  let sourceLevelParams :=",
                "    (Lean.collectLevelParams {} sourceInfo.type).params.toList",
                "  unless sourceLevelParams.length ==",
                "      candidateLevelParams.length do",
                '    Lean.throwError "rendered type changed the source universe arity"',
                "  let commonLevels := sourceLevelParams.map Lean.Level.param",
                "  let sourceType := sourceInfo.type.instantiateLevelParams",
                "    sourceLevelParams commonLevels",
                "  let candidateType := candidateType.instantiateLevelParams",
                "    candidateLevelParams commonLevels",
                "  unless ← Lean.Meta.isDefEq sourceType candidateType do",
                '    Lean.throwError "rendered type is not definitionally equal to the source declaration type"',
            )
        )
        content = (
            str(source or "").rstrip()
            + "\n\n"
            + (universe_decl + "\n" if universe_decl else "")
            + probe
            + "\n"
        )
        _path, execution, write_error = await self._execute_generated_file(
            goal_name=f"source_type_equiv_{short_id(content)}",
            content=content,
            timeout_s=max(1.0, min(15.0, operation_timeout * 0.4)),
            fast_fail_timeout_s=None,
            semaphore=self.sem,
        )
        if execution is None:
            output = str(write_error or "source type equivalence probe unavailable")
            return parse_lean_output(output, 1), output, 1
        output = str(execution.output or "")
        returncode = int(execution.returncode)
        parsed = parse_lean_output(output, returncode)
        if returncode == 0 and parsed.ok:
            return parsed, output, returncode

        # Core-only projects need not import Lean's command meta API. Compile
        # the exact source and an independently elaborated candidate axiom into
        # one temporary module *before* importing Meta, then compare the two
        # stored ConstantInfo types from a second module. This preserves the
        # original elaboration environment and gives neither side an expected
        # type or coercion path from the other.
        resolved_preamble = self._resolve_preamble(preamble_override)
        _clean_preamble, target_scoped_prefix, target_omit_variables = (
            decode_theorem_target_context(resolved_preamble)
        )
        candidate_name = f"miniSourceCandidate_{uuid.uuid4().hex}"
        candidate_command = f"axiom _root_.{candidate_name} : {candidate}"
        if target_omit_variables:
            candidate_command = (
                f"omit {' '.join(target_omit_variables)} in\n{candidate_command}"
            )
        if target_scoped_prefix:
            candidate_command = f"{target_scoped_prefix}\n{candidate_command}"
        candidate_universe_decl = _free_universe_decl(
            candidate,
            declared_in=source,
        )
        candidate_block = "\n".join(
            part for part in (candidate_universe_decl, candidate_command) if part
        )
        source_text = str(source or "").rstrip()
        trailing_closers = re.search(
            r"(?ms)(?P<closers>(?:^\s*end(?:\s+[^\s]+)?\s*$\n?)+)\s*\Z",
            source_text,
        )
        insertion = (
            trailing_closers.start("closers")
            if trailing_closers
            else len(source_text)
        )
        module_content = (
            source_text[:insertion].rstrip()
            + "\n\n"
            + candidate_block
            + "\n"
            + source_text[insertion:]
            + "\n"
        )
        module_name = f"MiniSourceEquiv{uuid.uuid4().hex}"
        module_path = self.temp_dir / f"{module_name}.lean"
        olean_path = self.temp_dir / f"{module_name}.olean"
        ilean_path = self.temp_dir / f"{module_name}.ilean"
        probe_path = self.temp_dir / f"{module_name}Probe.lean"
        source_literal = json.dumps(f"@_root_.{sanitized}", ensure_ascii=False)
        candidate_literal = json.dumps(
            f"@_root_.{candidate_name}",
            ensure_ascii=False,
        )
        module_probe = f"""import Lean.Elab.Command
import {module_name}

run_cmd Lean.Elab.Command.liftTermElabM do
  let sourceStx ←
    match Lean.Parser.runParserCategory (← Lean.getEnv) `term {source_literal} with
    | .ok stx => pure stx
    | .error error => Lean.throwError error
  let sourceTerm ← Lean.Elab.Term.withoutErrToSorry do
    Lean.Elab.Term.elabTerm sourceStx none
  let some sourceName := sourceTerm.getAppFn.constName?
    | Lean.throwError "source theorem did not elaborate to a constant"
  let candidateStx ←
    match Lean.Parser.runParserCategory (← Lean.getEnv) `term {candidate_literal} with
    | .ok stx => pure stx
    | .error error => Lean.throwError error
  let candidateTerm ← Lean.Elab.Term.withoutErrToSorry do
    Lean.Elab.Term.elabTerm candidateStx none
  let some candidateName := candidateTerm.getAppFn.constName?
    | Lean.throwError "candidate witness did not elaborate to a constant"
  let sourceInfo ← Lean.getConstInfo sourceName
  let candidateInfo ← Lean.getConstInfo candidateName
  let sourceParams := (Lean.collectLevelParams {{}} sourceInfo.type).params.toList
  let candidateParams :=
    (Lean.collectLevelParams {{}} candidateInfo.type).params.toList
  unless sourceParams.length == candidateParams.length do
    Lean.throwError "rendered type changed the source universe arity"
  let commonLevels := sourceParams.map Lean.Level.param
  let sourceType := sourceInfo.type.instantiateLevelParams sourceParams commonLevels
  let candidateType :=
    candidateInfo.type.instantiateLevelParams candidateParams commonLevels
  unless ← Lean.Meta.isDefEq sourceType candidateType do
    Lean.throwError "rendered type is not definitionally equal to the source declaration type"
"""
        lifecycle_task: Optional[asyncio.Task[Any]] = None
        sem_acquired = False
        remaining = operation_deadline - time.monotonic()
        if remaining <= 0:
            timeout_output = "Lean timeout during source type equivalence"
            return parse_lean_output(timeout_output, 1), timeout_output, 1
        try:
            admission_task = asyncio.ensure_future(
                self._admit_uncached_execution(asyncio.current_task())
            )
            try:
                lifecycle_task = await asyncio.wait_for(
                    admission_task,
                    timeout=remaining,
                )
            except asyncio.TimeoutError:
                cleanup_cancellation = None
                if not admission_task.done():
                    admission_task.cancel()
                    cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                        asyncio.gather(admission_task, return_exceptions=True)
                    )
                if not admission_task.cancelled():
                    try:
                        lifecycle_task = admission_task.result()
                    except BaseException:
                        lifecycle_task = None
                if cleanup_cancellation is not None:
                    raise cleanup_cancellation
                timeout_output = "Lean timeout during source type equivalence"
                return parse_lean_output(timeout_output, 1), timeout_output, 1
            except RuntimeError as exc:
                fallback_output = str(exc)
                return parse_lean_output(fallback_output, 1), fallback_output, 1
            except BaseException:
                cleanup_cancellation = None
                if not admission_task.done():
                    admission_task.cancel()
                    cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                        asyncio.gather(admission_task, return_exceptions=True)
                    )
                if not admission_task.cancelled():
                    try:
                        lifecycle_task = admission_task.result()
                    except BaseException:
                        lifecycle_task = None
                if cleanup_cancellation is not None:
                    raise cleanup_cancellation
                raise

            write_module_error = self._write_temp_lean_file(
                module_path,
                module_content,
            )
            if write_module_error is not None:
                fallback_output = f"disk write failed: {write_module_error}"
                return parse_lean_output(fallback_output, 1), fallback_output, 1
            self._owned_temp_files.add(module_path)
            write_probe_error = self._write_temp_lean_file(
                probe_path,
                module_probe,
            )
            if write_probe_error is not None:
                fallback_output = f"disk write failed: {write_probe_error}"
                return parse_lean_output(fallback_output, 1), fallback_output, 1
            self._owned_temp_files.add(probe_path)

            remaining = operation_deadline - time.monotonic()
            if remaining <= 0:
                timeout_output = "Lean timeout during source type equivalence"
                return parse_lean_output(timeout_output, 1), timeout_output, 1
            acquire_task = asyncio.ensure_future(self.sem.acquire())
            try:
                await asyncio.wait_for(acquire_task, timeout=remaining)
                sem_acquired = True
            except asyncio.TimeoutError:
                cleanup_cancellation = None
                if not acquire_task.done():
                    acquire_task.cancel()
                    cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                        asyncio.gather(acquire_task, return_exceptions=True)
                    )
                if not acquire_task.cancelled():
                    try:
                        sem_acquired = bool(acquire_task.result())
                    except BaseException:
                        sem_acquired = False
                if cleanup_cancellation is not None:
                    raise cleanup_cancellation
                timeout_output = "Lean timeout during source type equivalence"
                return parse_lean_output(timeout_output, 1), timeout_output, 1
            except BaseException:
                cleanup_cancellation = None
                if not acquire_task.done():
                    acquire_task.cancel()
                    cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                        asyncio.gather(acquire_task, return_exceptions=True)
                    )
                if not acquire_task.cancelled():
                    try:
                        sem_acquired = bool(acquire_task.result())
                    except BaseException:
                        sem_acquired = False
                if cleanup_cancellation is not None:
                    raise cleanup_cancellation
                raise

            remaining = operation_deadline - time.monotonic()
            if remaining <= 0:
                timeout_output = "Lean timeout during source type equivalence"
                return parse_lean_output(timeout_output, 1), timeout_output, 1
            compile_remaining = remaining * 0.65
            compile_returncode, compile_output = await self._run_via_lake(
                module_path,
                timeout_s=compile_remaining,
                output_path=olean_path,
                extra_module_paths=(self.temp_dir,),
            )
            if int(compile_returncode) != 0:
                return (
                    parse_lean_output(compile_output, int(compile_returncode)),
                    compile_output,
                    int(compile_returncode),
                )
            probe_remaining = operation_deadline - time.monotonic()
            if probe_remaining <= 0:
                timeout_output = "Lean timeout during source type equivalence"
                return parse_lean_output(timeout_output, 1), timeout_output, 1
            probe_returncode, probe_output = await self._run_via_lake(
                probe_path,
                timeout_s=probe_remaining,
                extra_module_paths=(self.temp_dir,),
            )
            return (
                parse_lean_output(probe_output, int(probe_returncode)),
                probe_output,
                int(probe_returncode),
            )
        finally:
            if sem_acquired:
                self.sem.release()
            for path in (module_path, olean_path, ilean_path, probe_path):
                try:
                    path.unlink(missing_ok=True)
                except OSError:
                    pass
                self._owned_temp_files.discard(path)
            if lifecycle_task is not None:
                cleanup_cancellation = await self._finish_cleanup_despite_cancellation(
                    self._release_uncached_execution(lifecycle_task)
                )
                if cleanup_cancellation is not None:
                    raise cleanup_cancellation

    @staticmethod
    def _checked_declaration_types_from_output(
        output: str,
        declaration_names: Sequence[str],
        *,
        returncode: int = 0,
    ) -> dict[str, str]:
        """Recover complete ``#check`` types for an exact declaration set.

        Lean emits one info diagnostic per ``#check`` and may wrap a long Pi
        type over continuation lines.  Parsing by requested declaration name
        prevents an unrelated diagnostic from being mistaken for a contract
        identity.  Partial results are intentional: one malformed planner
        claim must not erase canonical types for the root and valid siblings.
        """

        requested = tuple(
            str(name or "").strip() for name in declaration_names if str(name or "").strip()
        )
        if not requested:
            return {}
        alias_to_name: dict[str, str] = {}
        for name in requested:
            for alias in (name, f"_root_.{name}", f"@{name}", f"@_root_.{name}"):
                alias_to_name[alias] = name

        def checked_name(value: str) -> str:
            return re.sub(r"\.\{[^{}]*\}$", "", str(value or "").strip())

        recovered: dict[str, str] = {}
        raw_output = str(output or "")
        output_lines = raw_output.splitlines()
        for index, line in enumerate(output_lines):
            rendered = line.strip()
            if "info:" in rendered:
                rendered = rendered.rsplit("info:", 1)[-1].strip()
            if " : " not in rendered:
                continue
            rendered_name, rendered_type = rendered.split(" : ", 1)
            canonical_name = alias_to_name.get(checked_name(rendered_name))
            if canonical_name is None:
                continue
            parts = [rendered_type.strip()]
            for continuation in output_lines[index + 1 :]:
                continuation_rendered = continuation.strip()
                if "info:" in continuation_rendered:
                    continuation_rendered = continuation_rendered.rsplit(
                        "info:", 1
                    )[-1].strip()
                if " : " in continuation_rendered and (
                    checked_name(continuation_rendered.split(" : ", 1)[0])
                    in alias_to_name
                ):
                    break
                if re.search(
                    r"(?:^|\s)(?:info|warning|error)(?:\([^\r\n)]*\))?:",
                    continuation,
                ) or re.search(
                    r"(?:^|\s)(?:Prop\s*:\s*Type|"
                    r"MINI_CONTRACT_ANALYSIS_[0-9a-f]+_\d+:)",
                    continuation,
                ):
                    break
                if continuation.strip():
                    parts.append(continuation.strip())
            complete_type = re.sub(r"\s+", " ", " ".join(parts)).strip()
            if complete_type:
                recovered[canonical_name] = complete_type
        if len(recovered) == len(requested):
            return recovered
        # Structural-analysis JSON markers can be megabytes long and are not
        # Lean diagnostics.  Feeding them to the generic parser when one
        # sibling declaration is missing made partial contract batches spend
        # minutes tokenizing irrelevant serialized Expr data.  The direct
        # name parser above consumes the display reports; the fallback needs
        # only ordinary diagnostic lines.
        diagnostic_output = "\n".join(
            line
            for line in output_lines
            if not line.lstrip().startswith("MINI_CONTRACT_ANALYSIS_")
        )
        parsed = parse_lean_output(diagnostic_output, int(returncode or 0))
        for diagnostic in list(getattr(parsed, "diagnostics", ()) or ()):
            if str(getattr(diagnostic, "severity", "") or "") != "info":
                continue
            message = str(getattr(diagnostic, "message", "") or "").strip()
            if " : " not in message:
                continue
            rendered_name, rendered_type = message.split(" : ", 1)
            rendered_name = rendered_name.strip()
            if "info:" in rendered_name:
                rendered_name = rendered_name.rsplit("info:", 1)[-1].strip()
            canonical_name = alias_to_name.get(checked_name(rendered_name))
            complete_type = re.sub(r"\s+", " ", rendered_type).strip()
            if canonical_name is not None and complete_type:
                recovered.setdefault(canonical_name, complete_type)
        return recovered

    async def extract_typed_residual_batch(
        self,
        statement: str,
        proof_code: str,
        lemmas: Sequence[str] = (),
        *,
        preamble_override: str | None = None,
        timeout_s: Optional[float] = None,
        max_heartbeats: Optional[int] = None,
        check_kind: str = "proof_state_residual_receipt",
    ) -> LeanResidualBatchResult:
        """Run a partial proof and return an atomic typed residual receipt.

        The residual goals come directly from ``Lean.Elab.runTactic``. Each
        goal is closed over the tactic-created local context, fully explicitly
        delaborated, reparsed as a standalone type in this same Lean command,
        and required to be definitionally equal to the original closed
        ``Expr`` before the nonce-bound batch marker is emitted.

        Human diagnostic goal text is deliberately absent from this API. A
        non-``by`` partial proof is interpreted as exactly one
        ``refine (<term>)`` tactic so its term holes remain residual mvars.
        """

        raw_statement = str(statement or "").strip()
        raw_proof = str(proof_code or "").strip()
        exact_lemmas = tuple(str(lemma or "") for lemma in lemmas)

        def failed(
            error: str,
            *,
            phase: str,
            kind: str = "",
            output: str = "",
            returncode: int = 1,
            file_path: str = "",
            attempted: bool = False,
        ) -> LeanResidualBatchResult:
            exact_kind = str(kind or error)
            fingerprint, preview = _residual_failure_evidence(
                phase,
                exact_kind,
                output,
            )
            return LeanResidualBatchResult(
                ok=False,
                receipt=None,
                output=str(output or ""),
                returncode=int(returncode or 0),
                file_path=str(file_path or ""),
                error=str(error or ""),
                failure_phase=str(phase or ""),
                failure_kind=exact_kind,
                failure_fingerprint=fingerprint,
                diagnostic_preview=preview,
                attempted=bool(attempted),
            )

        if not raw_statement:
            return failed(
                "residual_parent_statement_missing",
                phase="input",
            )
        if not raw_proof:
            return failed(
                "residual_proof_stub_missing",
                phase="input",
            )
        if has_sorry_or_admit(raw_statement):
            return failed(
                "residual_parent_statement_contains_admission",
                phase="input",
            )
        if has_sorry_or_admit(raw_proof):
            return failed(
                "residual_proof_stub_contains_admission",
                phase="input",
            )

        try:
            await self.ensure_project_imports_built()
            await self._ensure_extra_imports_built(
                self._required_extra_imports_for_proof(raw_proof)
            )
        except Exception as exc:
            return failed(
                "residual_environment_unavailable",
                phase="environment",
                kind=type(exc).__name__,
                output=str(exc),
                attempted=True,
            )

        resolved_preamble = self._resolve_preamble(
            preamble_override,
            proof_code=raw_proof,
        )
        preamble, target_scoped_prefix, target_omit_variables = (
            decode_theorem_target_context(resolved_preamble)
        )
        elaboration_context_hash = lean_residual_elaboration_context_hash(
            self,
            preamble_override=preamble_override,
            ordered_lemmas=exact_lemmas,
            proof_code=raw_proof,
        )
        parent_statement_sha256 = hash_text(raw_statement)
        proof_stub_sha256 = hash_text(raw_proof)
        nonce = uuid.uuid4().hex
        serializer_prefix = f"miniResidual_{nonce}"
        proof_rejection_marker = f"MINI_RESIDUAL_PROOF_REJECTION_{nonce}"
        postprocess_marker = f"MINI_RESIDUAL_POSTPROCESS_FAILURE_{nonce}"
        statement_literal = json.dumps(raw_statement, ensure_ascii=False)
        proof_literal = json.dumps(raw_proof, ensure_ascii=False)
        serializer = f"""
private def {serializer_prefix}_binderInfo :
    Lean.BinderInfo → Lean.Json
  | .default => Lean.Json.str "default"
  | .implicit => Lean.Json.str "implicit"
  | .strictImplicit => Lean.Json.str "strictImplicit"
  | .instImplicit => Lean.Json.str "instImplicit"

private partial def {serializer_prefix}_level :
    Lean.Level → Lean.Json
  | .zero => Lean.Json.arr #[Lean.Json.str "zero"]
  | .succ level =>
      Lean.Json.arr #[Lean.Json.str "succ", {serializer_prefix}_level level]
  | .max left right =>
      Lean.Json.arr #[Lean.Json.str "max", {serializer_prefix}_level left,
        {serializer_prefix}_level right]
  | .imax left right =>
      Lean.Json.arr #[Lean.Json.str "imax", {serializer_prefix}_level left,
        {serializer_prefix}_level right]
  | .param name =>
      Lean.Json.arr #[Lean.Json.str "param", Lean.Json.str name.toString]
  | .mvar id =>
      Lean.Json.arr #[Lean.Json.str "mvar", Lean.Json.str id.name.toString]

private def {serializer_prefix}_literal : Lean.Literal → Lean.Json
  | .natVal value =>
      Lean.Json.arr #[Lean.Json.str "nat", Lean.ToJson.toJson value]
  | .strVal value =>
      Lean.Json.arr #[Lean.Json.str "str", Lean.Json.str value]

private partial def {serializer_prefix}_expr :
    Lean.Expr → Lean.Json
  | .bvar index =>
      Lean.Json.arr #[Lean.Json.str "bvar", Lean.ToJson.toJson index]
  | .fvar id =>
      Lean.Json.arr #[Lean.Json.str "fvar", Lean.Json.str id.name.toString]
  | .mvar id =>
      Lean.Json.arr #[Lean.Json.str "mvar", Lean.Json.str id.name.toString]
  | .sort level =>
      Lean.Json.arr #[Lean.Json.str "sort", {serializer_prefix}_level level]
  | .const name levels =>
      Lean.Json.arr #[Lean.Json.str "const", Lean.Json.str name.toString,
        Lean.Json.arr (levels.toArray.map {serializer_prefix}_level)]
  | .app fn arg =>
      Lean.Json.arr #[Lean.Json.str "app", {serializer_prefix}_expr fn,
        {serializer_prefix}_expr arg]
  | .lam _ domain body info =>
      Lean.Json.arr #[Lean.Json.str "lam", {serializer_prefix}_binderInfo info,
        {serializer_prefix}_expr domain, {serializer_prefix}_expr body]
  | .forallE _ domain body info =>
      Lean.Json.arr #[Lean.Json.str "forall", {serializer_prefix}_binderInfo info,
        {serializer_prefix}_expr domain, {serializer_prefix}_expr body]
  | .letE _ type value body nonDependent =>
      Lean.Json.arr #[Lean.Json.str "let", Lean.ToJson.toJson nonDependent,
        {serializer_prefix}_expr type, {serializer_prefix}_expr value,
        {serializer_prefix}_expr body]
  | .lit literal =>
      Lean.Json.arr #[Lean.Json.str "lit", {serializer_prefix}_literal literal]
  | .mdata _ body => {serializer_prefix}_expr body
  | .proj typeName index projected =>
      Lean.Json.arr #[Lean.Json.str "proj", Lean.Json.str typeName.toString,
        Lean.ToJson.toJson index, {serializer_prefix}_expr projected]

private def {serializer_prefix}_parse
    (category : Lean.Name) (source : String) : Lean.CoreM Lean.Syntax := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) category source with
  | .ok stx => pure stx
  | .error error => Lean.throwError error

private def {serializer_prefix}_elabType
    (source : String) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let stx ← {serializer_prefix}_parse `term source
  let type ← Lean.Elab.Term.withoutErrToSorry do
    Lean.Elab.Term.elabType stx
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let type ← Lean.instantiateMVars type
  if type.hasMVar || type.hasFVar || type.hasLooseBVars then
    Lean.throwError "elaborated type is not closed"
  pure type
"""
        probe = "\n".join(
            (
                "run_cmd Lean.Elab.Command.liftTermElabM do",
                f"  let statementType ← {serializer_prefix}_elabType {statement_literal}",
                "  let proofMessageCount :=",
                "    (\u2190 Lean.Core.getMessageLog).reportedPlusUnreported.size",
                "  let proofStx ← try",
                f"    {serializer_prefix}_parse `term {proof_literal}",
                "  catch",
                "  | .error ref message =>",
                "      Lean.logErrorAt ref message",
                f'      Lean.throwError "{proof_rejection_marker}"',
                "  | exception => throw exception",
                "  let tacticStx ← try",
                "    match proofStx with",
                "    | `(term| by $tactics:tacticSeq) => pure tactics.raw",
                "    | _ =>",
                f"      {serializer_prefix}_parse `tactic "
                f"(\"refine (\" ++ {proof_literal} ++ \")\")",
                "  catch",
                "  | .error ref message =>",
                "      Lean.logErrorAt ref message",
                f'      Lean.throwError "{proof_rejection_marker}"',
                "  | exception => throw exception",
                "  let rootGoal ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar statementType",
                "  let tacticResult ← try",
                "    Lean.Elab.runTactic rootGoal.mvarId! tacticStx",
                "  catch",
                "  | .error ref message =>",
                "      Lean.logErrorAt ref message",
                f'      Lean.throwError "{proof_rejection_marker}"',
                "  | exception => throw exception",
                "  let (goals, _) := tacticResult",
                "  let proofMessages :=",
                "    (\u2190 Lean.Core.getMessageLog).reportedPlusUnreported.toArray",
                "  let proofLoggedError :=",
                "    (proofMessages.extract proofMessageCount proofMessages.size).any",
                "      fun message => message.severity matches .error",
                "  if proofLoggedError then",
                f'    Lean.throwError "{proof_rejection_marker}"',
                "  try",
                "    let rootProof ← Lean.instantiateMVars rootGoal",
                "    Lean.Meta.check rootProof",
                "    let rootProofType ← Lean.Meta.inferType rootProof",
                "    unless ← Lean.Meta.withNewMCtxDepth <|",
                "        Lean.Meta.isDefEq rootProofType statementType do",
                '      Lean.throwError "residual root proof has the wrong type"',
                "    let rootProof ← Lean.instantiateMVars rootGoal",
                "    if rootProof.hasSorry then",
                '      Lean.throwError "residual proof contains sorry"',
                "    let reachableGoals ← Lean.Meta.getMVarsNoDelayed rootProof",
                "    let returnedGoals := goals.toArray",
                "    let goalsMatch :=",
                "      reachableGoals.size == returnedGoals.size &&",
                "      reachableGoals.all (fun goalId => returnedGoals.contains goalId) &&",
                "      returnedGoals.all (fun goalId => reachableGoals.contains goalId)",
                "    unless goalsMatch do",
                '      Lean.throwError "residual proof goal accounting mismatch"',
                "    for goalId in goals do",
                "      if ← goalId.isAssigned then",
                '        Lean.throwError "residual proof returned an assigned goal"',
                "      goalId.withContext do",
                "        let target ← Lean.instantiateMVars (← goalId.getType)",
                "        let fvars := (← Lean.getLCtx).getFVarIds.map Lean.mkFVar",
                "        let closed ← Lean.Meta.mkForallFVars fvars target",
                "        let closed ← Lean.instantiateMVars closed",
                "        if closed.hasSorry then",
                '          Lean.throwError "residual proof goal contains sorry"',
                "  catch",
                "  | .error ref message =>",
                "      Lean.logErrorAt ref message",
                f'      Lean.throwError "{proof_rejection_marker}"',
                "  | exception => throw exception",
                "  let goalPayloads ← try",
                "    let mut goalPayloads : Array Lean.Json := #[]",
                "    for slot in [:goals.length] do",
                "      let goalId := goals[slot]!",
                "      let goalPayload ← goalId.withContext do",
                "        let target ← Lean.instantiateMVars (← goalId.getType)",
                "        let fvars := (← Lean.getLCtx).getFVarIds.map Lean.mkFVar",
                "        let closed ← Lean.Meta.mkForallFVars fvars target",
                "        let closed ← Lean.instantiateMVars closed",
                "        if closed.hasMVar || closed.hasFVar || closed.hasLooseBVars then",
                '          Lean.throwError "residual goal did not close"',
                "        if closed.hasSorry then",
                '          Lean.throwError "residual goal contains sorry"',
                "        let rendered ← Lean.withOptions (fun options =>",
                "          options",
                "            |>.setBool `pp.fullNames true",
                "            |>.setBool `pp.explicit true",
                "            |>.setBool `pp.universes true",
                "            |>.setBool `pp.piBinderTypes true",
                "            |>.setBool `pp.funBinderTypes true",
                "            |>.setBool `pp.deepTerms true",
                "            |>.setBool `pp.proofs true",
                "            |>.set `pp.maxSteps (1000000 : Nat)) do",
                "          Lean.Meta.ppExpr closed",
                f"        if rendered.pretty.length > {_LEAN_RESIDUAL_SOURCE_MAX_CHARS} then",
                '          Lean.throwError "residual source exceeded size limit"',
                f"        let replayed ← {serializer_prefix}_elabType rendered.pretty",
                "        if replayed.hasSorry then",
                '          Lean.throwError "replayed residual contains sorry"',
                "        unless ← Lean.Meta.withNewMCtxDepth <|",
                "            Lean.Meta.isDefEq closed replayed do",
                '          Lean.throwError "residual source round-trip changed its type"',
                "        pure <| Lean.Json.mkObj [",
                '          ("slot", Lean.ToJson.toJson slot),',
                '          ("source", Lean.Json.str rendered.pretty),',
                f'          ("expr", {serializer_prefix}_expr closed)',
                "        ]",
                "      goalPayloads := goalPayloads.push goalPayload",
                "    pure goalPayloads",
                "  catch",
                "  | .error ref message =>",
                "      Lean.logErrorAt ref message",
                f'      Lean.throwError "{postprocess_marker}"',
                "  | exception => throw exception",
                "  let payload := Lean.Json.mkObj [",
                f'    ("version", Lean.ToJson.toJson {_LEAN_RESIDUAL_BATCH_FORMAT_VERSION}),',
                f'    ("parentExpr", {serializer_prefix}_expr statementType),',
                '    ("goals", Lean.Json.arr goalPayloads)',
                "  ]",
                f'  Lean.logInfo m!"MINI_RESIDUAL_BATCH_{nonce}:{{payload.compress}}"',
            )
        )
        # Hard-math goals can contain hundreds of nested applications. Keep
        # the elevated recursion allowance scoped to this generated receipt
        # command: it prevents Lean's serializer/elaborator from rejecting a
        # valid deep goal without altering the user's theorem environment or
        # placing an artificial depth cap on ordinary proof search.
        probe = "set_option maxRecDepth 1000000 in\n" + probe
        if isinstance(max_heartbeats, int) and max_heartbeats > 0:
            probe = f"set_option maxHeartbeats {int(max_heartbeats)} in\n{probe}"
        if target_omit_variables:
            probe = f"omit {' '.join(target_omit_variables)} in\n{probe}"
        if target_scoped_prefix:
            probe = f"{target_scoped_prefix}\n{probe}"

        lemma_block = "\n".join(exact_lemmas)
        universe_decl = _free_universe_decl(
            "\n".join((raw_statement, raw_proof, lemma_block))
        )
        content = "\n\n".join(
            part
            for part in (
                preamble.strip(),
                universe_decl,
                lemma_block.strip(),
                "open Lean Elab Command Meta",
                serializer.strip(),
                probe,
                "#check Prop",
            )
            if part
        ) + "\n"
        try:
            file_path, execution, write_error = await self._execute_generated_file(
                mode=check_kind,
                goal_name=f"residual_receipt_{short_id(content)}",
                content=content,
                timeout_s=timeout_s,
                fast_fail_timeout_s=None,
                warning_as_error=True,
                semaphore=self.sem,
            )
        except Exception as exc:
            return failed(
                "residual_execution_unavailable",
                phase="execution",
                kind=type(exc).__name__,
                output=str(exc),
                attempted=True,
            )
        if execution is None:
            return failed(
                "residual_execution_unavailable",
                phase="execution",
                kind="execution_unavailable",
                output=str(write_error or "residual receipt execution unavailable"),
                file_path=str(file_path or ""),
                attempted=True,
            )
        output = str(execution.output or "")
        returncode = int(execution.returncode or 0)
        marker_family_re = re.compile(
            r"MINI_RESIDUAL_(?:PROOF_REJECTION|POSTPROCESS_FAILURE)_"
            r"[0-9a-f]+"
        )
        diagnostic_marker_re = re.compile(
            r"(?m)^[^\r\n]*:\d+:\d+:\s+error:\s+"
            r"(MINI_RESIDUAL_(?:PROOF_REJECTION|POSTPROCESS_FAILURE)_"
            r"[0-9a-f]+)\s*$"
        )
        batch_marker_token_re = re.compile(
            r"MINI_RESIDUAL_BATCH_([0-9a-f]+):"
        )
        all_marker_tokens = marker_family_re.findall(output)
        diagnostic_marker_tokens = diagnostic_marker_re.findall(output)
        batch_marker_nonces = batch_marker_token_re.findall(output)
        marker_transport_integrity = bool(
            all_marker_tokens == diagnostic_marker_tokens
        )
        if returncode != 0:
            parsed_failure = parse_lean_output(output, returncode)
            timeout_error = bool(getattr(parsed_failure, "timeout", False))
            proof_command_rejected = bool(
                marker_transport_integrity
                and not batch_marker_nonces
                and diagnostic_marker_tokens == [proof_rejection_marker]
            )
            postprocess_failure = bool(
                marker_transport_integrity
                and not batch_marker_nonces
                and diagnostic_marker_tokens == [postprocess_marker]
            )
            error = (
                "residual_lean_rejected"
                if proof_command_rejected
                else (
                    "residual_postprocess_failure"
                    if postprocess_failure
                    else (
                        "residual_execution_timeout"
                        if timeout_error
                        else "residual_execution_unavailable"
                    )
                )
            )
            phase = (
                "proof"
                if proof_command_rejected
                else (
                    "postprocess"
                    if postprocess_failure
                    else ("timeout" if timeout_error else "execution")
                )
            )
            return failed(
                error,
                phase=phase,
                kind=error,
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        if all_marker_tokens or diagnostic_marker_tokens:
            return failed(
                "residual_control_marker_on_success",
                phase="protocol",
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        if batch_marker_nonces != [nonce]:
            return failed(
                "residual_marker_count_mismatch",
                phase="protocol",
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        marker_re = re.compile(
            rf"(?m)^MINI_RESIDUAL_BATCH_{re.escape(nonce)}:"
            r"(\{[^\r\n]*\})\s*$"
        )
        marker_matches = list(marker_re.finditer(output))
        if len(marker_matches) != 1:
            return failed(
                "residual_marker_count_mismatch",
                phase="protocol",
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        try:
            payload = _decode_json_iterative(marker_matches[0].group(1))
        except (TypeError, ValueError, json.JSONDecodeError, RecursionError):
            return failed(
                "residual_marker_invalid_json",
                phase="protocol",
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        receipt, validation_error = _residual_batch_receipt_from_payload(
            payload,
            marker_nonce=nonce,
            parent_statement_sha256=parent_statement_sha256,
            proof_stub_sha256=proof_stub_sha256,
            elaboration_context_hash=elaboration_context_hash,
        )
        if receipt is None:
            validation_kind = validation_error or "residual_marker_invalid"
            return failed(
                validation_kind,
                phase="validation",
                output=output,
                returncode=returncode,
                file_path=str(file_path or ""),
                attempted=True,
            )
        return LeanResidualBatchResult(
            ok=True,
            receipt=receipt,
            output=output,
            returncode=returncode,
            file_path=str(file_path or ""),
            attempted=True,
        )

    async def analyze_statement_contracts(
        self,
        statements: Sequence[str],
        *,
        preamble_override: str | None = None,
        timeout_s: float = 60.0,
        defeq_anchor_indices: Sequence[int] = (),
        defeq_candidate_indices: Sequence[int] = (),
        _operation_deadline: float | None = None,
    ) -> tuple[tuple[LeanStatementContractAnalysis, ...], str, int]:
        """Elaborate propositions and return structural contract evidence.

        The trusted Lean metaprogram serializes the elaborated ``Expr`` before
        delaboration and separately reports the complete reduced Pi telescope.
        Pretty-printer output remains available for diagnostics and conservative
        surface matching, but is never used as structural identity.
        """

        operation_started = time.monotonic()
        operation_deadline = (
            float(_operation_deadline)
            if _operation_deadline is not None
            else operation_started + max(1.0, float(timeout_s))
        )
        raw_statements = tuple(str(statement or "").strip() for statement in statements)
        if not raw_statements:
            return (), "", 0
        requested_anchor_indices = tuple(
            dict.fromkeys(
                int(index)
                for index in defeq_anchor_indices
                if 0 <= int(index) < len(raw_statements)
                and raw_statements[int(index)]
            )
        )
        requested_candidate_indices = frozenset(
            int(index)
            for index in defeq_candidate_indices
            if 0 <= int(index) < len(raw_statements)
            and raw_statements[int(index)]
        )
        preamble = self._resolve_preamble(preamble_override)
        nonce = short_id("\n".join(raw_statements) + str(time.monotonic_ns()))
        names = tuple(
            f"mini_contract_identity_{nonce}_{index}"
            for index in range(len(raw_statements))
        )
        serializer_prefix = f"miniContract_{nonce}"
        serializer = f"""
private def {serializer_prefix}_binderInfo :
    Lean.BinderInfo → Lean.Json
  | .default => Lean.Json.str "default"
  | .implicit => Lean.Json.str "implicit"
  | .strictImplicit => Lean.Json.str "strictImplicit"
  | .instImplicit => Lean.Json.str "instImplicit"

private partial def {serializer_prefix}_level :
    Lean.Level → Lean.Json
  | .zero => Lean.Json.arr #[Lean.Json.str "zero"]
  | .succ level =>
      Lean.Json.arr #[Lean.Json.str "succ", {serializer_prefix}_level level]
  | .max left right =>
      Lean.Json.arr #[Lean.Json.str "max", {serializer_prefix}_level left,
        {serializer_prefix}_level right]
  | .imax left right =>
      Lean.Json.arr #[Lean.Json.str "imax", {serializer_prefix}_level left,
        {serializer_prefix}_level right]
  | .param name =>
      Lean.Json.arr #[Lean.Json.str "param", Lean.Json.str name.toString]
  | .mvar id =>
      Lean.Json.arr #[Lean.Json.str "mvar", Lean.Json.str id.name.toString]

private def {serializer_prefix}_literal : Lean.Literal → Lean.Json
  | .natVal value =>
      Lean.Json.arr #[Lean.Json.str "nat", Lean.ToJson.toJson value]
  | .strVal value =>
      Lean.Json.arr #[Lean.Json.str "str", Lean.Json.str value]

private def {serializer_prefix}_printerOptions
    (options : Lean.Options) : Lean.Options :=
  options
    |>.setBool `pp.universes false
    |>.setBool `pp.piBinderTypes true
    |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.fullNames true

private partial def {serializer_prefix}_expr :
    Lean.Expr → Lean.Json
  | .bvar index =>
      Lean.Json.arr #[Lean.Json.str "bvar", Lean.ToJson.toJson index]
  | .fvar id =>
      Lean.Json.arr #[Lean.Json.str "fvar", Lean.Json.str id.name.toString]
  | .mvar id =>
      Lean.Json.arr #[Lean.Json.str "mvar", Lean.Json.str id.name.toString]
  | .sort level =>
      Lean.Json.arr #[Lean.Json.str "sort",
        {serializer_prefix}_level level]
  | .const name levels =>
      Lean.Json.arr #[Lean.Json.str "const", Lean.Json.str name.toString,
        Lean.Json.arr (levels.toArray.map {serializer_prefix}_level)]
  | .app fn arg =>
      Lean.Json.arr #[Lean.Json.str "app", {serializer_prefix}_expr fn,
        {serializer_prefix}_expr arg]
  | .lam _ domain body info =>
      Lean.Json.arr #[Lean.Json.str "lam",
        {serializer_prefix}_binderInfo info,
        {serializer_prefix}_expr domain, {serializer_prefix}_expr body]
  | .forallE _ domain body info =>
      Lean.Json.arr #[Lean.Json.str "forall",
        {serializer_prefix}_binderInfo info,
        {serializer_prefix}_expr domain, {serializer_prefix}_expr body]
  | .letE _ type value body nonDependent =>
      Lean.Json.arr #[Lean.Json.str "let",
        Lean.ToJson.toJson nonDependent,
        {serializer_prefix}_expr type, {serializer_prefix}_expr value,
        {serializer_prefix}_expr body]
  | .lit literal =>
      Lean.Json.arr #[Lean.Json.str "lit",
        {serializer_prefix}_literal literal]
  | .mdata _ body => {serializer_prefix}_expr body
  | .proj typeName index projected =>
      Lean.Json.arr #[Lean.Json.str "proj",
        Lean.Json.str typeName.toString, Lean.ToJson.toJson index,
        {serializer_prefix}_expr projected]

private def {serializer_prefix}_binders (type : Lean.Expr) :
    Lean.MetaM (Array Lean.Json) :=
  Lean.Meta.forallTelescope type fun fvars _body => do
    let mut binders : Array Lean.Json := #[]
    for fvar in fvars do
      let localDecl ← fvar.fvarId!.getDecl
      let domain := localDecl.type
      let proof ← Lean.Meta.isProp domain
      let rendered ← Lean.withOptions {serializer_prefix}_printerOptions do
        Lean.Meta.ppExpr domain
      let normalizedDomain ← Lean.Meta.whnf domain
      let normalizedRendered ←
        Lean.withOptions {serializer_prefix}_printerOptions do
          Lean.Meta.ppExpr normalizedDomain
      binders := binders.push <| Lean.Json.mkObj [
          ("sort", Lean.Json.str (if proof then "proof" else "data")),
          ("type", Lean.Json.str rendered.pretty),
          ("normalizedType", Lean.Json.str normalizedRendered.pretty),
          ("expr", {serializer_prefix}_expr normalizedDomain)
        ]
    pure binders

private def {serializer_prefix}_elabType (source : String) :
    Lean.Elab.Term.TermElabM Lean.Expr := do
  let stx ←
    match Lean.Parser.runParserCategory (← Lean.getEnv) `term source with
    | .ok stx => pure stx
    | .error error => Lean.throwError error
  let type ← Lean.Elab.Term.withoutErrToSorry do
    Lean.Elab.Term.elabType stx
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let type ← Lean.instantiateMVars type
  if type.hasMVar then
    Lean.throwError "statement type contains unresolved metavariables"
  unless ← Lean.Meta.isProp type do
    Lean.throwError "statement is not a proposition"
  pure type

private partial def {serializer_prefix}_contractTypeCore (type : Lean.Expr) :
    Lean.MetaM (Option Lean.Expr) := do
  match type with
  | .forallE name domain body info =>
      let proof ← Lean.Meta.isProp domain
      Lean.Meta.withLocalDecl name info domain fun localExpr => do
        let some rest ←
          {serializer_prefix}_contractTypeCore (body.instantiate1 localExpr)
          | pure none
        if proof then
          if rest.containsFVar localExpr.fvarId! then
            pure none
          else
            pure (some rest)
        else
          pure (some (← Lean.Meta.mkForallFVars #[localExpr] rest))
  | _ => pure (some type)

private def {serializer_prefix}_contractType (type : Lean.Expr) :
    Lean.MetaM (Option Lean.Expr) := do
  {serializer_prefix}_contractTypeCore (← Lean.Meta.whnf type)

private def {serializer_prefix}_defeq
    (type : Lean.Expr) (source : String) :
    Lean.Elab.Term.TermElabM (Option Bool) := do
  try
    let other ← {serializer_prefix}_elabType source
    pure (some (← Lean.Meta.withNewMCtxDepth <| Lean.Meta.isDefEq type other))
  catch _ => pure none

private def {serializer_prefix}_contractDefeq
    (type : Lean.Expr) (source : String) :
    Lean.Elab.Term.TermElabM (Option Bool) := do
  try
    let other ← {serializer_prefix}_elabType source
    let some left ← {serializer_prefix}_contractType type | pure none
    let some right ← {serializer_prefix}_contractType other | pure none
    pure (some (← Lean.Meta.withNewMCtxDepth <| Lean.Meta.isDefEq left right))
  catch _ => pure none
"""
        probes = [
            "\n".join(
                (
                    "run_cmd Lean.Elab.Command.liftTermElabM do",
                    "  try",
                    "    let stx ←",
                    "      match Lean.Parser.runParserCategory (← Lean.getEnv) `term",
                    f"          {json.dumps(statement, ensure_ascii=False)} with",
                    "      | .ok stx => pure stx",
                    "      | .error error => Lean.throwError error",
                    "    let type ← Lean.Elab.Term.withoutErrToSorry do",
                    "      Lean.Elab.Term.elabType stx",
                    "    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing",
                    "    let type ← Lean.instantiateMVars type",
                    "    if type.hasMVar then",
                    '      Lean.throwError "statement type contains unresolved metavariables"',
                    "    unless ← Lean.Meta.isProp type do",
                    '      Lean.throwError "statement is not a proposition"',
                    "    let displayType ← Lean.withOptions",
                    f"      {serializer_prefix}_printerOptions do",
                    "      Lean.Meta.ppExpr type",
                    "    let mut defeq : Array Lean.Json := #[]",
                    "    let mut contractDefeq : Array Lean.Json := #[]",
                    "    let mut defeqChecked : Array Lean.Json := #[]",
                    "    let mut contractDefeqChecked : Array Lean.Json := #[]",
                    *tuple(
                        "\n".join(
                            (
                                f"    match ← {serializer_prefix}_defeq type "
                                f"{json.dumps(other, ensure_ascii=False)} with",
                                "    | some equal =>",
                                "      defeqChecked := defeqChecked.push "
                                f"(Lean.ToJson.toJson {other_index})",
                                "      if equal then defeq := defeq.push "
                                f"(Lean.ToJson.toJson {other_index})",
                                "    | none => pure ()",
                                f"    match ← {serializer_prefix}_contractDefeq type "
                                f"{json.dumps(other, ensure_ascii=False)} with",
                                "    | some equal =>",
                                "      contractDefeqChecked := "
                                "contractDefeqChecked.push "
                                f"(Lean.ToJson.toJson {other_index})",
                                "      if equal then contractDefeq := "
                                "contractDefeq.push "
                                f"(Lean.ToJson.toJson {other_index})",
                                "    | none => pure ()",
                            )
                        )
                        for other_index in (
                            requested_anchor_indices
                            if index in requested_candidate_indices
                            else ()
                        )
                        for other in (raw_statements[other_index],)
                    ),
                    "    let normalizedType ← Lean.Meta.whnf type",
                    f"    let binders ← {serializer_prefix}_binders normalizedType",
                    "    let contractConclusionExpr ←",
                    f"      match ← {serializer_prefix}_contractType type with",
                    "      | some contractType =>",
                    "        pure <| "
                    f"{serializer_prefix}_expr (← Lean.Meta.whnf contractType)",
                    "      | none => pure Lean.Json.null",
                    "    let payload := Lean.Json.mkObj [",
                    f'      ("format", Lean.ToJson.toJson {_CONTRACT_ANALYSIS_FORMAT_VERSION}),',
                    f'      ("expr", {serializer_prefix}_expr normalizedType),',
                    '      ("binders", Lean.Json.arr binders),',
                    '      ("contractConclusionExpr", contractConclusionExpr),',
                    '      ("defeq", Lean.Json.arr defeq),',
                    '      ("contractDefeq", Lean.Json.arr contractDefeq),',
                    '      ("defeqChecked", Lean.Json.arr defeqChecked),',
                    '      ("contractDefeqChecked", Lean.Json.arr contractDefeqChecked)',
                    "    ]",
                    f'    Lean.logInfo m!"MINI_CONTRACT_ANALYSIS_{nonce}_{index}:'
                    '{payload.compress}"',
                    f'    Lean.logInfo m!"{name} : {{displayType}}"',
                    "  catch error =>",
                    f'    Lean.throwError m!"{name}: {{error.toMessageData}}"',
                )
            )
            for index, (name, statement) in enumerate(zip(names, raw_statements))
            if statement
        ]
        probe_statement_indices = [
            index
            for index, statement in enumerate(raw_statements)
            if statement
        ]
        content_parts = [
            part
            for part in (
                preamble.strip(),
                "open Lean Elab Command Meta",
                serializer,
                *probes,
                "#check Prop",
            )
            if part
        ]
        # Retain generated source spans as a fallback. Ordinary exceptions are
        # explicitly probe-prefixed above, but parser/runtime diagnostics that
        # bypass that catch may still be attributable from their source line.
        probe_line_ranges: list[tuple[int, int, int]] = []
        next_line = 1
        probe_index_by_text = {
            probe: probe_statement_indices[index]
            for index, probe in enumerate(probes)
        }
        for part in content_parts:
            line_count = max(1, part.count("\n") + 1)
            probe_index = probe_index_by_text.get(part)
            if probe_index is not None:
                probe_line_ranges.append(
                    (next_line, next_line + line_count - 1, probe_index)
                )
            next_line += line_count + 1  # ``\n\n`` separator
        content = "\n\n".join(content_parts)
        content_built_at = time.monotonic()
        execution_started = content_built_at
        remaining_operation_s = operation_deadline - time.monotonic()
        if remaining_operation_s <= 0.0:
            return (
                tuple(
                    LeanStatementContractAnalysis() for _ in raw_statements
                ),
                "Lean timeout: contract analysis deadline exhausted",
                1,
            )
        _path, execution, write_error = await self._execute_generated_file(
            goal_name=f"contract_identity_{short_id(content)}",
            content=content,
            timeout_s=max(0.01, remaining_operation_s),
            fast_fail_timeout_s=None,
            semaphore=self.sem,
            retry_repl_termination=False,
        )
        execution_finished = time.monotonic()

        def operation_receipt(*, postprocess_finished: float) -> dict[str, Any]:
            return {
                "runner_backend_key": str(
                    getattr(execution, "backend", "") or ""
                ),
                "runner_content_build_wall_s": round(
                    max(0.0, content_built_at - operation_started),
                    6,
                ),
                "runner_execution_wall_s": round(
                    max(0.0, execution_finished - execution_started),
                    6,
                ),
                "runner_postprocess_wall_s": round(
                    max(0.0, postprocess_finished - execution_finished),
                    6,
                ),
                "runner_operation_wall_s": round(
                    max(0.0, postprocess_finished - operation_started),
                    6,
                ),
            }

        def attach_operation_receipt(
            items: Sequence[LeanStatementContractAnalysis],
        ) -> tuple[LeanStatementContractAnalysis, ...]:
            receipt = operation_receipt(postprocess_finished=time.monotonic())
            return tuple(
                dataclass_replace(item, operation_telemetry=receipt)
                for item in items
            )

        if execution is None:
            error = str(write_error or "contract identity probe unavailable")
            return (
                attach_operation_receipt(
                    tuple(LeanStatementContractAnalysis() for _ in raw_statements)
                ),
                error,
                1,
            )
        output = str(execution.output or "")
        if termination_signal_from_returncode(execution.returncode):
            active_indices = tuple(
                index for index, statement in enumerate(raw_statements) if statement
            )
            if len(active_indices) > 1:
                active_anchor_indices = tuple(
                    index
                    for index in requested_anchor_indices
                    if index in active_indices
                )
                active_candidate_indices = tuple(
                    index
                    for index in requested_candidate_indices
                    if index in active_indices
                )
                index_groups: list[tuple[int, ...]] = []
                if active_anchor_indices and active_candidate_indices:
                    anchor_set = set(active_anchor_indices)
                    candidate_set = set(active_candidate_indices)
                    relation_groups: list[tuple[int, ...]]
                    if anchor_set.isdisjoint(candidate_set):
                        # Preserve the complete anchor/candidate relation
                        # matrix without expanding it into one verifier call
                        # per pair. Partition the larger side and repeat the
                        # smaller side; recursive negative-exit recovery then
                        # keeps logarithmically shrinking the generated files
                        # under the caller's one absolute deadline.
                        if (
                            len(active_anchor_indices) == 1
                            and len(active_candidate_indices) == 1
                            and len(active_indices) == 2
                        ):
                            relation_groups = []
                            index_groups = [
                                (index,) for index in active_indices
                            ]
                        elif len(active_anchor_indices) >= len(
                            active_candidate_indices
                        ) and len(active_anchor_indices) > 1:
                            midpoint = max(
                                1, len(active_anchor_indices) // 2
                            )
                            relation_groups = [
                                tuple(
                                    dict.fromkeys(
                                        (*anchor_group, *active_candidate_indices)
                                    )
                                )
                                for anchor_group in (
                                    active_anchor_indices[:midpoint],
                                    active_anchor_indices[midpoint:],
                                )
                                if anchor_group
                            ]
                        elif len(active_candidate_indices) > 1:
                            midpoint = max(
                                1, len(active_candidate_indices) // 2
                            )
                            relation_groups = [
                                tuple(
                                    dict.fromkeys(
                                        (*active_anchor_indices, *candidate_group)
                                    )
                                )
                                for candidate_group in (
                                    active_candidate_indices[:midpoint],
                                    active_candidate_indices[midpoint:],
                                )
                                if candidate_group
                            ]
                        else:
                            relation_groups = [
                                (
                                    active_anchor_indices[0],
                                    active_candidate_indices[0],
                                )
                            ]
                    else:
                        # Overlapping role sets (including self-relations) do
                        # not admit the disjoint-side partition above: adding
                        # an index through its other role would silently widen
                        # the local anchor set. Keep exact pair checks for this
                        # uncommon shape, with the prior singleton escape for
                        # an irreducible batch.
                        relation_groups = list(
                            dict.fromkeys(
                                (anchor_index, candidate_index)
                                for candidate_index in active_candidate_indices
                                for anchor_index in active_anchor_indices
                                if anchor_index != candidate_index
                            )
                        )
                        if any(
                            len(group) >= len(active_indices)
                            for group in relation_groups
                        ):
                            relation_groups = []
                            index_groups = [
                                (index,) for index in active_indices
                            ]
                    if relation_groups:
                        index_groups.extend(relation_groups)
                        covered_relation_indices = {
                            index for group in relation_groups for index in group
                        }
                        remaining_indices = tuple(
                            index
                            for index in active_indices
                            if index not in covered_relation_indices
                        )
                        if remaining_indices:
                            remaining_midpoint = max(
                                1, len(remaining_indices) // 2
                            )
                            index_groups.extend(
                                group
                                for group in (
                                    remaining_indices[:remaining_midpoint],
                                    remaining_indices[remaining_midpoint:],
                                )
                                if group
                            )
                    elif not index_groups and len(active_indices) > 1:
                        midpoint = max(1, len(active_indices) // 2)
                        index_groups = [
                            group
                            for group in (
                                active_indices[:midpoint],
                                active_indices[midpoint:],
                            )
                            if group
                        ]
                else:
                    midpoint = max(1, len(active_indices) // 2)
                    index_groups = [
                        group
                        for group in (
                            active_indices[:midpoint],
                            active_indices[midpoint:],
                        )
                        if group
                    ]
                if not index_groups:
                    return (
                        attach_operation_receipt(
                            tuple(
                                LeanStatementContractAnalysis()
                                for _ in raw_statements
                            )
                        ),
                        output,
                        int(execution.returncode or 0),
                    )
                combined = [
                    LeanStatementContractAnalysis() for _ in raw_statements
                ]
                combined_output = [output] if output else []
                combined_returncode = 0
                split_finished = True
                for group in index_groups:
                    remaining_timeout_s = operation_deadline - time.monotonic()
                    if remaining_timeout_s <= 0.0:
                        split_finished = False
                        break
                    local_by_global = {
                        global_index: local_index
                        for local_index, global_index in enumerate(group)
                    }
                    local_anchors = tuple(
                        local_by_global[index]
                        for index in requested_anchor_indices
                        if index in local_by_global
                    )
                    local_candidates = tuple(
                        local_by_global[index]
                        for index in requested_candidate_indices
                        if index in local_by_global
                    )
                    try:
                        (
                            local_analyses,
                            local_output,
                            local_returncode,
                        ) = await asyncio.wait_for(
                            self.analyze_statement_contracts(
                                tuple(raw_statements[index] for index in group),
                                preamble_override=preamble,
                                timeout_s=remaining_timeout_s,
                                defeq_anchor_indices=local_anchors,
                                defeq_candidate_indices=local_candidates,
                                _operation_deadline=operation_deadline,
                            ),
                            timeout=remaining_timeout_s,
                        )
                    except asyncio.TimeoutError:
                        split_finished = False
                        break
                    if local_output:
                        combined_output.append(str(local_output))
                    if int(local_returncode or 0) != 0:
                        combined_returncode = int(local_returncode or 0)
                    global_by_local = dict(enumerate(group))
                    for local_index, analysis in enumerate(local_analyses):
                        if local_index not in global_by_local:
                            continue

                        def remap(indices: Sequence[int]) -> tuple[int, ...]:
                            return tuple(
                                global_by_local[index]
                                for index in indices
                                if index in global_by_local
                            )

                        remapped_analysis = dataclass_replace(
                            analysis,
                            definitionally_equal_indices=remap(
                                analysis.definitionally_equal_indices
                            ),
                            contract_definitionally_equal_indices=remap(
                                analysis.contract_definitionally_equal_indices
                            ),
                            definitionally_checked_indices=remap(
                                analysis.definitionally_checked_indices
                            ),
                            contract_definitionally_checked_indices=remap(
                                analysis.contract_definitionally_checked_indices
                            ),
                        )
                        global_index = global_by_local[local_index]
                        prior_analysis = combined[global_index]
                        base_analysis = (
                            remapped_analysis
                            if remapped_analysis.structural_identity
                            or not prior_analysis.structural_identity
                            else prior_analysis
                        )

                        def merged_indices(
                            prior: Sequence[int], current: Sequence[int]
                        ) -> tuple[int, ...]:
                            return tuple(sorted(set(prior).union(current)))

                        combined[global_index] = dataclass_replace(
                            base_analysis,
                            definitionally_equal_indices=merged_indices(
                                prior_analysis.definitionally_equal_indices,
                                remapped_analysis.definitionally_equal_indices,
                            ),
                            contract_definitionally_equal_indices=merged_indices(
                                prior_analysis.contract_definitionally_equal_indices,
                                remapped_analysis.contract_definitionally_equal_indices,
                            ),
                            definitionally_checked_indices=merged_indices(
                                prior_analysis.definitionally_checked_indices,
                                remapped_analysis.definitionally_checked_indices,
                            ),
                            contract_definitionally_checked_indices=merged_indices(
                                prior_analysis.contract_definitionally_checked_indices,
                                remapped_analysis.contract_definitionally_checked_indices,
                            ),
                        )
                if split_finished:
                    return (
                        tuple(combined),
                        "\n".join(combined_output),
                        combined_returncode,
                    )
        if _execution_ended_without_complete_contract_output(execution):
            # Timeout/infra output has no structural proof authority. It can
            # contain a very large partial marker stream; parsing that stream
            # synchronously would extend a completed backend timeout while
            # blocking the event loop that owns the caller's wall deadline.
            return (
                attach_operation_receipt(
                    tuple(LeanStatementContractAnalysis() for _ in raw_statements)
                ),
                output,
                int(execution.returncode or 0),
            )
        # Parse diagnostics one line at a time.  The previous multiline regex
        # began with ``.*?`` and was attempted at every output line.  Structural
        # contract markers are very large one-line JSON values containing many
        # colons; when even one later claim failed, backtracking across those
        # marker lines made a 32-statement batch consume ~46 minutes of CPU in
        # production despite a 60-second backend timeout.  Bound the diagnostic
        # header prefix and never run it against marker lines.
        diagnostic_header_re = re.compile(
            r"^.{0,4096}?:(?P<line>\d+):\d+:\s+"
            r"(?:error|warning)(?:\([^\r\n)]*\))?:"
        )
        attributed: list[str] = []
        output_lines = output.splitlines()
        line_index = 0
        while line_index < len(output_lines):
            line = output_lines[line_index]
            if ": error" not in line and ": warning" not in line:
                line_index += 1
                continue
            match = diagnostic_header_re.match(line)
            if match is None:
                line_index += 1
                continue
            source_line = int(match.group("line"))
            block_lines = [line]
            continuation_index = line_index + 1
            while continuation_index < len(output_lines):
                continuation = output_lines[continuation_index]
                if (
                    ((": error" in continuation or ": warning" in continuation)
                     and diagnostic_header_re.match(continuation) is not None)
                    or re.match(
                        r"^(?:MINI_CONTRACT_ANALYSIS_[0-9a-f]+_\d+:|"
                        r"mini_contract_identity_[0-9a-f]+_\d+\s*:|"
                        r"Prop\s*:)",
                        continuation.strip(),
                    )
                ):
                    break
                block_lines.append(continuation)
                continuation_index += 1
            block = "\n".join(block_lines).strip()
            named_probe = re.search(
                r"mini_contract_identity_[0-9a-f]+_(\d+):",
                block,
            )
            probe_index = (
                int(named_probe.group(1))
                if named_probe is not None
                else next(
                    (
                        index
                        for start, end, index in probe_line_ranges
                        if start <= source_line <= end
                    ),
                    None,
                )
            )
            if probe_index is None:
                line_index = continuation_index
                continue
            attributed.append(
                f"MINI_CONTRACT_DIAGNOSTIC_{probe_index}: {block}"
            )
            line_index = continuation_index
        if attributed:
            output = "\n".join((output, *attributed))
        recovered = self._checked_declaration_types_from_output(
            output,
            names,
            returncode=execution.returncode,
        )
        payloads: dict[int, Any] = {}
        marker_re = re.compile(
            rf"(?m)^MINI_CONTRACT_ANALYSIS_{re.escape(nonce)}_"
            r"(\d+):(\{[^\r\n]*\})\s*$"
        )
        for marker in marker_re.finditer(output):
            try:
                payloads[int(marker.group(1))] = json.loads(marker.group(2))
            except (TypeError, ValueError, json.JSONDecodeError):
                continue
        analyses = tuple(
            (
                _contract_analysis_from_payload(
                    payloads.get(index),
                    display_type=recovered.get(name, ""),
                )
                if statement
                else LeanStatementContractAnalysis()
            )
            for index, (name, statement) in enumerate(
                zip(names, raw_statements)
            )
        )
        allowed_anchors = frozenset(requested_anchor_indices)
        analyses = tuple(
            dataclass_replace(
                item,
                definitionally_equal_indices=tuple(
                    index
                    for index in item.definitionally_equal_indices
                    if statement_index in requested_candidate_indices
                    and index in allowed_anchors
                ),
                contract_definitionally_equal_indices=tuple(
                    index
                    for index in item.contract_definitionally_equal_indices
                    if statement_index in requested_candidate_indices
                    and index in allowed_anchors
                ),
                definitionally_checked_indices=tuple(
                    index
                    for index in item.definitionally_checked_indices
                    if statement_index in requested_candidate_indices
                    and index in allowed_anchors
                ),
                contract_definitionally_checked_indices=tuple(
                    index
                    for index in item.contract_definitionally_checked_indices
                    if statement_index in requested_candidate_indices
                    and index in allowed_anchors
                ),
            )
            for statement_index, item in enumerate(analyses)
        )
        return (
            attach_operation_receipt(analyses),
            output,
            int(execution.returncode),
        )

    async def canonicalize_statement_types(
        self,
        statements: Sequence[str],
        *,
        preamble_override: str | None = None,
        timeout_s: float = 60.0,
    ) -> tuple[tuple[str, ...], str, int]:
        """Compatibility wrapper returning diagnostic display types only."""

        analyses, output, returncode = await self.analyze_statement_contracts(
            statements,
            preamble_override=preamble_override,
            timeout_s=timeout_s,
        )
        return (
            tuple(
                analysis.display_type
                for analysis in analyses
            ),
            output,
            returncode,
        )

    async def check_statement_type_raw(
        self,
        statement: str,
        *,
        preamble_override: str | None = None,
        timeout_s: float = 60.0,
    ) -> tuple[LeanParseResult, str, int]:
        """Elaborate a theorem type without relying on tactics or ``sorry``."""

        preamble = self._resolve_preamble(preamble_override)
        preamble, target_scoped_prefix, target_omit_variables = (
            decode_theorem_target_context(preamble)
        )
        universe_decl = _free_universe_decl(statement, declared_in=preamble)
        witness = f"theoremProjectPreflightWitness_{short_id(statement)}"
        witness_command = f"axiom {witness} : {str(statement).strip()}"
        if target_omit_variables:
            witness_command = (
                f"omit {' '.join(target_omit_variables)} in\n{witness_command}"
            )
        if target_scoped_prefix:
            witness_command = f"{target_scoped_prefix}\n{witness_command}"
        content = "\n\n".join(
            part
            for part in (
                preamble.strip(),
                universe_decl,
                witness_command,
            )
            if part
        ) + "\n"
        _path, execution, write_error = await self._execute_generated_file(
            mode="theorem_project_type",
            goal_name=f"project_type_{short_id(content)}",
            content=content,
            timeout_s=max(1.0, float(timeout_s)),
            fast_fail_timeout_s=None,
            semaphore=self.sem,
        )
        if execution is None:
            output = str(write_error or "statement type probe unavailable")
            return parse_lean_output(output, 1), output, 1
        output = str(execution.output or "")
        return (
            parse_lean_output(output, int(execution.returncode)),
            output,
            int(execution.returncode),
        )

    @staticmethod
    def _render_goal_state(goal: LeanGoalState) -> str:
        """Render one remaining goal compactly for JSON tool responses."""
        lines = [
            str(h).strip() for h in getattr(goal, "hypotheses", []) if str(h).strip()
        ]
        target = str(getattr(goal, "target", "") or "").strip()
        if target:
            lines.append(f"⊢ {target}")
        return "\n".join(lines).strip()

    @staticmethod
    def _decl_application_probe_stubs(decl_name: str) -> List[str]:
        """Return proof-stub candidates for goal-aware declaration probing.

        Each bare variant is paired with an ``intros``-prefixed variant so
        goals with leading ``∀``/hypothesis binders (e.g. ``∀ {α β : ℝ}, H → G``)
        can be probed.  ``intros`` is a no-op when no leading Pi exists, so
        the prefixed form is strictly more robust; we still try the bare
        form as a fallback for goals where ``intros`` would over-reduce.
        """
        name = str(decl_name or "").strip()
        if not name:
            return []
        base_stubs: List[str] = []
        base_stubs.extend(
            [
                f"apply {name}",
                f"exact {name}",
                f"refine {name}",
            ]
        )
        for placeholder_count in (1, 2, 3):
            placeholders = " ".join("?_" for _ in range(placeholder_count))
            base_stubs.append(f"refine {name} {placeholders}".rstrip())
        stubs: List[str] = []
        seen: set[str] = set()
        # Try ``intros``-prefixed variants first so goals with leading
        # binders are handled quickly without burning probes on the bare
        # form that is structurally guaranteed to fail.
        for prefix in ("intros\n  ", ""):
            for base in base_stubs:
                stub = f"{prefix}{base}"
                if stub not in seen:
                    seen.add(stub)
                    stubs.append(stub)
        return stubs

    async def apply_decl_to_goal(
        self,
        statement: str,
        decl_name: str,
        *,
        preamble_override: str | None = None,
        lemmas: Optional[List[str]] = None,
        timeout_s: float = 10.0,
        ping_only: bool = False,
        ping_timeout_s: float = 8.0,
        probe_observer: Optional[Callable[[Dict[str, Any]], None]] = None,
    ) -> Dict[str, Any]:
        """Probe whether a declaration can be applied to the current goal.

        ``ping_only`` runs only the baseline plus the first, most robust probe
        stub under a short deadline.  A negative ping is explicitly deferred
        to the full portfolio: it is latency evidence, not a proof that later
        ``exact``/``refine`` variants are impossible.
        """
        goal_statement = str(statement or "").strip()
        sanitized_decl, error = self._normalize_check_term_name(decl_name)
        base_result: Dict[str, Any] = {
            "decl_name": sanitized_decl or str(decl_name or "").strip(),
            "statement": goal_statement,
            "applicable": False,
            "proof_stub": "",
            "remaining_goals": [],
            "instantiated_target": "",
            "error_kind": "",
            "requires_full_probe": False,
            "ping_error_kind": "",
        }
        if not goal_statement:
            base_result["error_kind"] = "empty_statement"
            return base_result
        if error:
            base_result["error_kind"] = "invalid_decl_name"
            return base_result
        operation_timeout_s = max(0.0, float(timeout_s or 0.0))
        if ping_only:
            operation_timeout_s = min(
                operation_timeout_s,
                max(0.0, float(ping_timeout_s or 0.0)),
            )
        # One absolute deadline bounds the baseline, the complete stub
        # portfolio, and failure enrichment together. In particular, a
        # cancellation-resistant backend tail may finish its current check,
        # but it cannot start another full-timeout check afterward.
        portfolio_deadline_monotonic = time.monotonic() + operation_timeout_s

        def portfolio_time_remaining() -> float:
            return max(0.0, portfolio_deadline_monotonic - time.monotonic())

        def probe_timeouts() -> Tuple[float, float]:
            hard_timeout_s = portfolio_time_remaining()
            fast_fail_timeout_s = (
                hard_timeout_s if ping_only else min(8.0, hard_timeout_s)
            )
            return hard_timeout_s, fast_fail_timeout_s

        def observe_probe(event: Dict[str, Any]) -> None:
            if probe_observer is None:
                return
            try:
                probe_observer(dict(event))
            except Exception:
                # Observability is not proof authority and must never change
                # whether a declaration application is tried or accepted.
                logger.debug("Declaration probe observer failed", exc_info=True)

        def probe_event(
            *,
            event: str,
            probe_stage: str,
            stub_index: int,
            proof_stub: str,
            elapsed_s: Optional[float] = None,
            hard_timeout_s: Optional[float] = None,
            fast_fail_timeout_s: Optional[float] = None,
            **extra: Any,
        ) -> None:
            allocated_hard_timeout_s = max(
                0.0,
                float(
                    portfolio_time_remaining()
                    if hard_timeout_s is None
                    else hard_timeout_s
                ),
            )
            allocated_fast_fail_timeout_s = max(
                0.0,
                float(
                    (
                        allocated_hard_timeout_s
                        if ping_only
                        else min(8.0, allocated_hard_timeout_s)
                    )
                    if fast_fail_timeout_s is None
                    else fast_fail_timeout_s
                ),
            )
            payload: Dict[str, Any] = {
                "event": event,
                "probe_stage": probe_stage,
                "stub_index": stub_index,
                "proof_stub": proof_stub,
                "hard_timeout_s": allocated_hard_timeout_s,
                "fast_fail_timeout_s": allocated_fast_fail_timeout_s,
            }
            if elapsed_s is not None:
                payload["elapsed_s"] = max(0.0, float(elapsed_s))
            payload.update(extra)
            observe_probe(payload)

        def finish_ping_failure(
            error_kind: str,
            error_text: str = "",
        ) -> Dict[str, Any]:
            normalized = str(error_kind or "unknown_error").strip().lower()
            diagnostic = str(error_text or "").strip().lower()
            context_sensitive = normalized == "unknown_identifier" or any(
                token in normalized or token in diagnostic
                for token in (
                    "instance",
                    "synthes",
                    "typeclass",
                    "unification",
                    "metavariable",
                )
            )
            definitive = normalized in {
                "invalid_decl_name",
                "type_mismatch",
                "no_applicable_probe",
                "no_residual_goals",
                "no_residuals",
            }
            # Only ambiguous infrastructure/timeout/parser results receive a
            # later full-portfolio quantum. A semantic first-apply miss is
            # either permanently structural or retriable after a real Lean
            # context change; neither should burn the 120-second portfolio in
            # this unchanged context.
            requires_full = not definitive and not context_sensitive
            base_result["requires_full_probe"] = requires_full
            base_result["ping_error_kind"] = normalized
            base_result["error_kind"] = (
                "decl_application_ping_deferred"
                if requires_full
                else normalized
            )
            if error_text:
                base_result["error"] = str(error_text)
            return base_result

        def finish_portfolio_deadline() -> Dict[str, Any]:
            message = "declaration application portfolio deadline exhausted"
            if ping_only:
                return finish_ping_failure("timeout", message)
            base_result["error_kind"] = "timeout"
            base_result["error"] = message
            return base_result

        lemma_blocks = list(lemmas or [])
        baseline_stub = "refine ?_"
        baseline_timeout_s, baseline_fast_fail_timeout_s = probe_timeouts()
        if baseline_timeout_s <= 0.0:
            return finish_portfolio_deadline()
        baseline_started = time.monotonic()
        probe_event(
            event="started",
            probe_stage="baseline",
            stub_index=0,
            proof_stub=baseline_stub,
            hard_timeout_s=baseline_timeout_s,
            fast_fail_timeout_s=baseline_fast_fail_timeout_s,
        )
        try:
            baseline_parsed, _baseline_out, _baseline_rc = await self.check_with_sorry_raw(
                goal_statement,
                "by\n  refine ?_\n",
                lemma_blocks,
                preamble_override=preamble_override,
                timeout_s=baseline_timeout_s,
                fast_fail_timeout_s=baseline_fast_fail_timeout_s,
            )
        except Exception as exc:
            deadline_expired = portfolio_time_remaining() <= 0.0
            probe_event(
                event="finished",
                probe_stage="baseline",
                stub_index=0,
                proof_stub=baseline_stub,
                elapsed_s=time.monotonic() - baseline_started,
                hard_timeout_s=baseline_timeout_s,
                fast_fail_timeout_s=baseline_fast_fail_timeout_s,
                applicable=False,
                error_kind="timeout" if deadline_expired else "runner_exception",
            )
            if deadline_expired:
                return finish_portfolio_deadline()
            if ping_only:
                return finish_ping_failure("runner_exception", str(exc))
            base_result["error_kind"] = "runner_exception"
            base_result["error"] = str(exc)
            return base_result
        if portfolio_time_remaining() <= 0.0:
            probe_event(
                event="finished",
                probe_stage="baseline",
                stub_index=0,
                proof_stub=baseline_stub,
                elapsed_s=time.monotonic() - baseline_started,
                hard_timeout_s=baseline_timeout_s,
                fast_fail_timeout_s=baseline_fast_fail_timeout_s,
                applicable=False,
                error_kind="timeout",
            )
            return finish_portfolio_deadline()
        try:
            baseline_error_kind = canonical_error_type(baseline_parsed)
        except (AttributeError, TypeError, ValueError):
            # Lightweight adapters may return only a remaining-goals view.
            # Telemetry must not strengthen the result interface they need to
            # implement or interrupt declaration search.
            baseline_error_kind = ""
        baseline_remaining_goals = list(
            getattr(baseline_parsed, "remaining_goals", []) or []
        )
        baseline_applicable = bool(baseline_remaining_goals) and (
            baseline_error_kind in ("", "unsolved_goals")
        )
        probe_event(
            event="finished",
            probe_stage="baseline",
            stub_index=0,
            proof_stub=baseline_stub,
            elapsed_s=time.monotonic() - baseline_started,
            hard_timeout_s=baseline_timeout_s,
            fast_fail_timeout_s=baseline_fast_fail_timeout_s,
            applicable=baseline_applicable,
            error_kind=baseline_error_kind,
            remaining_goal_count=len(baseline_remaining_goals),
        )
        if getattr(baseline_parsed, "remaining_goals", None):
            first_goal = list(getattr(baseline_parsed, "remaining_goals", []) or [])[0]
            base_result["instantiated_target"] = str(
                getattr(first_goal, "target", "") or ""
            ).strip()
        if not base_result["instantiated_target"]:
            base_result["instantiated_target"] = goal_statement

        last_error_kind = ""
        last_error_text = ""
        proof_stubs = self._decl_application_probe_stubs(sanitized_decl)
        if ping_only:
            proof_stubs = proof_stubs[:1]
        for stub_index, proof_stub in enumerate(proof_stubs, 1):
            stub_timeout_s, stub_fast_fail_timeout_s = probe_timeouts()
            if stub_timeout_s <= 0.0:
                return finish_portfolio_deadline()
            proof_code = f"by\n  {proof_stub}\n"
            stub_started = time.monotonic()
            probe_event(
                event="started",
                probe_stage="stub",
                stub_index=stub_index,
                proof_stub=proof_stub,
                hard_timeout_s=stub_timeout_s,
                fast_fail_timeout_s=stub_fast_fail_timeout_s,
            )
            try:
                parsed, out, returncode = await self.check_with_sorry_raw(
                    goal_statement,
                    proof_code,
                    lemma_blocks,
                    preamble_override=preamble_override,
                    timeout_s=stub_timeout_s,
                    fast_fail_timeout_s=stub_fast_fail_timeout_s,
                )
            except Exception as exc:
                deadline_expired = portfolio_time_remaining() <= 0.0
                probe_event(
                    event="finished",
                    probe_stage="stub",
                    stub_index=stub_index,
                    proof_stub=proof_stub,
                    elapsed_s=time.monotonic() - stub_started,
                    hard_timeout_s=stub_timeout_s,
                    fast_fail_timeout_s=stub_fast_fail_timeout_s,
                    applicable=False,
                    error_kind="timeout" if deadline_expired else "runner_exception",
                )
                if deadline_expired:
                    return finish_portfolio_deadline()
                if ping_only:
                    return finish_ping_failure("runner_exception", str(exc))
                base_result["error_kind"] = "runner_exception"
                base_result["error"] = str(exc)
                return base_result
            if portfolio_time_remaining() <= 0.0:
                probe_event(
                    event="finished",
                    probe_stage="stub",
                    stub_index=stub_index,
                    proof_stub=proof_stub,
                    elapsed_s=time.monotonic() - stub_started,
                    hard_timeout_s=stub_timeout_s,
                    fast_fail_timeout_s=stub_fast_fail_timeout_s,
                    applicable=False,
                    error_kind="timeout",
                )
                return finish_portfolio_deadline()

            remaining_goals = [
                rendered
                for rendered in (
                    self._render_goal_state(goal)
                    for goal in (getattr(parsed, "remaining_goals", []) or [])
                )
                if rendered
            ]
            parsed_error_kind = canonical_error_type(parsed)
            if remaining_goals and parsed_error_kind in ("", "unsolved_goals"):
                probe_event(
                    event="finished",
                    probe_stage="stub",
                    stub_index=stub_index,
                    proof_stub=proof_stub,
                    elapsed_s=time.monotonic() - stub_started,
                    hard_timeout_s=stub_timeout_s,
                    fast_fail_timeout_s=stub_fast_fail_timeout_s,
                    applicable=True,
                    error_kind="",
                    remaining_goal_count=len(remaining_goals),
                )
                base_result["applicable"] = True
                base_result["proof_stub"] = proof_stub
                base_result["remaining_goals"] = remaining_goals
                return base_result

            if returncode == 0 and not getattr(parsed, "diagnostics", None):
                probe_event(
                    event="finished",
                    probe_stage="stub",
                    stub_index=stub_index,
                    proof_stub=proof_stub,
                    elapsed_s=time.monotonic() - stub_started,
                    hard_timeout_s=stub_timeout_s,
                    fast_fail_timeout_s=stub_fast_fail_timeout_s,
                    applicable=True,
                    error_kind="",
                    remaining_goal_count=0,
                )
                base_result["applicable"] = True
                base_result["proof_stub"] = proof_stub
                return base_result

            current_error_kind = parsed_error_kind or "unknown_error"
            current_error_text = ""
            for diag in getattr(parsed, "diagnostics", []) or []:
                if str(getattr(diag, "severity", "") or "") == "error":
                    current_error_text = diagnostic_preview(
                        str(getattr(diag, "message", "") or "")
                    )
                    break
            if not current_error_text:
                current_error_text = " ".join(str(out or "").split())[:240]
            probe_event(
                event="finished",
                probe_stage="stub",
                stub_index=stub_index,
                proof_stub=proof_stub,
                elapsed_s=time.monotonic() - stub_started,
                hard_timeout_s=stub_timeout_s,
                fast_fail_timeout_s=stub_fast_fail_timeout_s,
                applicable=False,
                error_kind=current_error_kind,
                remaining_goal_count=0,
            )
            # Keep the earliest semantic failure so later over-applied probe
            # variants do not overwrite the real incompatibility signal.
            if not last_error_kind:
                last_error_kind = current_error_kind
            if not last_error_text:
                last_error_text = current_error_text

        if ping_only:
            return finish_ping_failure(
                last_error_kind or "unknown_error",
                last_error_text,
            )
        base_result["error_kind"] = last_error_kind or "unknown_error"
        if last_error_text:
            base_result["error"] = last_error_text
        # Enrich failure responses with the decl's actual type signature
        # so the tool-loop LLM can see what the lemma really requires
        # instead of repeatedly guessing a wrong statement. Without this
        # enrichment, a type_mismatch is opaque: the LLM only knows its
        # guess was wrong, not WHAT the correct signature is, so it keeps
        # hallucinating applications (live trace 2012_a2_19apr_15.jsonl,
        # composition rounds 2–4: 9/13 candidate failures were
        # type_mismatch applying bridge lemmas with fabricated signatures).
        # Only emitted on failure so the success path adds no extra probe.
        decl_type = ""
        type_lookup_timeout_s, _unused_fast_fail_timeout_s = probe_timeouts()
        if type_lookup_timeout_s > 0.0:
            type_lookup_stub = f"#check {sanitized_decl}"
            type_lookup_started = time.monotonic()
            # check_term_type has no silence-based fast-fail contract, so its
            # hard remaining lease is reported in both timeout fields.
            probe_event(
                event="started",
                probe_stage="type_lookup",
                stub_index=0,
                proof_stub=type_lookup_stub,
                hard_timeout_s=type_lookup_timeout_s,
                fast_fail_timeout_s=type_lookup_timeout_s,
            )
            try:
                decl_type = await self.check_term_type(
                    sanitized_decl,
                    preamble_override=preamble_override,
                    lemmas=lemma_blocks,
                    timeout_s=type_lookup_timeout_s,
                )
            except Exception:
                type_lookup_expired = portfolio_time_remaining() <= 0.0
                probe_event(
                    event="finished",
                    probe_stage="type_lookup",
                    stub_index=0,
                    proof_stub=type_lookup_stub,
                    elapsed_s=time.monotonic() - type_lookup_started,
                    hard_timeout_s=type_lookup_timeout_s,
                    fast_fail_timeout_s=type_lookup_timeout_s,
                    applicable=False,
                    error_kind=(
                        "timeout" if type_lookup_expired else "runner_exception"
                    ),
                )
                decl_type = ""
            else:
                type_lookup_expired = portfolio_time_remaining() <= 0.0
                probe_event(
                    event="finished",
                    probe_stage="type_lookup",
                    stub_index=0,
                    proof_stub=type_lookup_stub,
                    elapsed_s=time.monotonic() - type_lookup_started,
                    hard_timeout_s=type_lookup_timeout_s,
                    fast_fail_timeout_s=type_lookup_timeout_s,
                    applicable=bool(decl_type) and not type_lookup_expired,
                    error_kind="timeout" if type_lookup_expired else "",
                )
                if type_lookup_expired:
                    decl_type = ""
        decl_type_clean = str(decl_type or "").strip()
        if (
            decl_type_clean
            and not decl_type_clean.startswith("Error:")
            and not decl_type_clean.startswith("Note:")
        ):
            base_result["decl_type"] = decl_type_clean
        return base_result

    def quiesce(self) -> None:
        """Refuse new Lean work while leaving cleanup facilities alive.

        First step of the manual-cancellation child-work barrier
        (MP-FU-009): after this call no new scratch ``.lean`` file can be
        written and no new check can start, but in-flight cleanup, kills,
        and ``aclose()`` still function. Idempotent.

        A retired generation must not quiesce its live successor. Captured
        callers reach the live runner through ``current_generation()`` /
        forwarded theorem operations, not through this teardown path.
        """

        self._quiesced = True
        self._detach_replacement_chain()

    def _finalize_close_state(self) -> list[asyncio.Task[Any]]:
        self._repl_init = False
        self._repl_disabled_until_s = 0.0
        # Cancel any pending coalescing Futures before clearing the
        # _inflight_exec dict. Without this, any waiter currently
        # inside asyncio.shield(future) would hang forever on a
        # Future that will never be resolved — the shield isolates
        # the waiter from cancellation of its own task, so the only
        # thing that can unblock it is the Future itself transitioning
        # to a done state. Iterate a snapshot because dict.clear()
        # will run after.
        for future in list(self._inflight_exec.values()):
            if not future.done():
                future.cancel()
        self._inflight_exec.clear()
        try:
            current_task = asyncio.current_task()
        except RuntimeError:
            current_task = None
        cancelled_tasks = [
            task
            for task in tuple(self._inflight_exec_tasks)
            if task is not current_task and not task.done()
        ]
        for task in cancelled_tasks:
            task.cancel()
        self._inflight_exec_tasks.difference_update(cancelled_tasks)
        # Bulk cleanup of any remaining temp files.
        for file_path in tuple(self._owned_temp_files):
            try:
                file_path.unlink(missing_ok=True)
            except OSError:
                continue
            self._owned_temp_files.discard(file_path)
        return cancelled_tasks

    async def aclose(self) -> None:
        """Asynchronously clean up this generation's verifier resources."""

        await self.aclose_generation_only()

    async def aclose_generation_only(self) -> None:
        """Close this retired generation without closing its replacement.

        Live callers reach the published generation through
        ``_generation_ref``. This path reclaims only the retired
        subprocess/pool resources for *this* object.
        """

        self._detach_replacement_chain()
        self._closed = True
        self._close_generation += 1
        pool = self._persistent_pool
        self._persistent_pool = None
        if self._repl:
            self._repl.close()
            self._repl = None
        cancelled_tasks = self._finalize_close_state()
        if cancelled_tasks:
            await asyncio.gather(*cancelled_tasks, return_exceptions=True)
        if pool is not None:
            await pool.close()

    def close(self) -> None:
        """Clean up this generation's verifier resources and temp files."""

        try:
            asyncio.get_running_loop()
        except RuntimeError:
            asyncio.run(self.aclose())
            return
        self.close_generation_only()

    def close_generation_only(self) -> None:
        """Synchronously reclaim this retired generation only."""

        self._detach_replacement_chain()
        self._closed = True
        self._close_generation += 1
        if self._repl:
            self._repl.close()
            self._repl = None
        if self._persistent_pool is not None:
            self._persistent_pool.close_nowait()
            self._persistent_pool = None
        self._finalize_close_state()
