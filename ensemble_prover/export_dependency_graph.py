"""Build browsable dependency artifacts for exported Lean proofs.

The exporter parses each solved ``.lean`` file into local declarations and
source-level dependency edges, then writes JSON, source maps, source HTML, and
an interactive graph. Batch mode also writes a local index. External Lean names
are heuristic source references, not claims about the elaborated environment,
and are marked accordingly in the output.

Usage::

    python -m ensemble_prover.export_dependency_graph
    python -m ensemble_prover.export_dependency_graph --problem putnam_1962_a6
    python -m ensemble_prover.export_dependency_graph --file path/to/proof.lean
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import quote

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SOLVED_DIR = PROJECT_ROOT / "runs" / "mini_prover" / "solved"

try:  # Import lazily-friendly: tests can still exercise the fallback parser.
    from ensemble_prover.lean_decl_parser import find_decl_header_end
except Exception:  # pragma: no cover - fallback is covered through behavior.
    find_decl_header_end = None  # type: ignore[assignment]

_LEAN_IDENT_RE = r"[A-Za-z_][A-Za-z0-9_']*"
_LEAN_NAME_RE = rf"{_LEAN_IDENT_RE}(?:\.{_LEAN_IDENT_RE})*"

_DECL_RE = re.compile(
    r"^(?:\s*@\[[^\]]*\]\s*)*"
    rf"(?:\s*open\s+(?P<inline_open>[^\n]+?)\s+in\s+)?"
    r"(?:\s*@\[[^\]]*\]\s*)*"
    r"(?P<kind>(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|axiom))\s+"
    rf"(?P<name>{_LEAN_NAME_RE})(?![A-Za-z0-9_'.])",
    re.MULTILINE,
)

# Dotted capitalized identifiers are, in practice, external Mathlib/core
# references in exported proof files (local decls are flat mini_*/putnam_*
# names). Purely syntactic — see module docstring.
_EXTERNAL_REF_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_']+)+)\b")

_COMMENT_LINE_RE = re.compile(r"--.*?$", re.MULTILINE)
_COMMENT_BLOCK_RE = re.compile(r"/-.*?-/", re.DOTALL)
_VERSION_SUFFIX_RE = re.compile(r"_v[1-9][0-9]*$")
_PUTNAM_STEM_RE = re.compile(r"^putnam_(\d{4})_([ab])([1-6])$")
_STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
_SCOPE_CMD_RE = re.compile(
    rf"(?m)^\s*(?:namespace[ \t]+(?P<namespace>{_LEAN_NAME_RE})|"
    rf"section(?:[ \t]+(?P<section>{_LEAN_NAME_RE}))?|"
    rf"end(?:[ \t]+(?P<end>{_LEAN_NAME_RE}))?|"
    rf"open[ \t]+(?P<open>[^\n]+))\b"
)


@dataclass
class Declaration:
    name: str
    kind: str
    line: int
    line_end: int
    col_start: int
    col_end: int
    char_start: int
    char_end: int
    byte_start: int
    byte_end: int
    source_span: Dict[str, int]
    proof_line: int
    proof_line_end: int
    proof_char_start: int
    proof_char_end: int
    proof_span: Dict[str, int]
    body: str
    statement: str
    proof_length: int
    source_hash: str
    source_name: str = ""
    namespace: str = ""
    open_namespaces: List[str] = field(default_factory=list)
    open_hiding: Dict[str, List[str]] = field(default_factory=dict)
    open_aliases: List[Dict[str, str]] = field(default_factory=list)
    href: str = ""
    proof_href: str = ""
    graph_node_id: str = ""
    runtime_source_hash_match: Optional[bool] = None
    is_root: bool = False
    deps: List[str] = field(default_factory=list)
    external_refs: List[str] = field(default_factory=list)


def _strip_comments(text: str) -> str:
    return _COMMENT_LINE_RE.sub("", _COMMENT_BLOCK_RE.sub("", text))


# Trailing lines that belong to the NEXT declaration (its docstring or
# attributes) or are pure noise: block/doc comments, line comments,
# attribute lines, blanks. Stripped from a declaration's body slice so
# proof_length/statement describe THIS declaration only.
_TRAILING_NONCODE_RE = re.compile(
    r"(?:\s*(?:/--?(?:[^-]|-(?!/))*-/|--[^\n]*|@\[[^\]]*\]))*\s*$"
)


def _trim_trailing_noncode(segment: str) -> str:
    return _TRAILING_NONCODE_RE.sub("", segment)


def _text_hash(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8")).hexdigest()[:16]


def _byte_len(text: str) -> int:
    return len(str(text or "").encode("utf-8"))


def _line_col_for_index(source: str, index: int) -> Tuple[int, int]:
    safe_index = max(0, min(len(source), int(index or 0)))
    line_start = source.rfind("\n", 0, safe_index) + 1
    return source.count("\n", 0, safe_index) + 1, safe_index - line_start + 1


def _line_for_inclusive_end(source: str, start: int, end: int) -> int:
    if end <= start:
        return _line_col_for_index(source, start)[0]
    return _line_col_for_index(source, end - 1)[0]


def _decl_header_end(source: str, start: int, end: int) -> int:
    if find_decl_header_end is not None:
        parsed = find_decl_header_end(
            source,
            start,
            max_scan=max(1, end - start),
            allow_where=True,
        )
        if parsed is not None and start < parsed <= end:
            return int(parsed)
    fallback = source.find(":=", start, end)
    return (fallback + 2) if fallback >= 0 else start


def _href_for_line(source_html_name: str, line: int, line_end: int) -> str:
    if not source_html_name:
        return ""
    start = max(1, int(line or 1))
    return f"./{quote(source_html_name)}#L{start}"


def root_name_for_export_stem(stem: str) -> str:
    root = _VERSION_SUFFIX_RE.sub("", str(stem or "").strip())
    if root.endswith("_visible"):
        root = root[: -len("_visible")]
    return root


def _parse_open_directives(
    rest: str,
    *,
    allow_scoped: bool = False,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, str]]]:
    raw = str(rest or "").strip()
    if not raw or raw.startswith("scoped"):
        return [], []
    if not allow_scoped and re.search(r"\bin\b(?:\s|$)", raw):
        return [], []
    raw = raw.split(" in ", 1)[0]
    skip = {"open", "only", "hiding", "renaming", "from", "in"}
    specs: List[Dict[str, Any]] = []
    aliases: List[Dict[str, str]] = []
    idx = 0
    while idx < len(raw):
        while idx < len(raw) and raw[idx] in " \t,":
            idx += 1
        match = re.match(_LEAN_NAME_RE, raw[idx:])
        if match is None:
            idx += 1
            continue
        namespace = match.group(0)
        idx += match.end()
        if namespace in skip:
            continue
        while idx < len(raw) and raw[idx].isspace():
            idx += 1
        if idx < len(raw) and raw[idx] == "(":
            group_end = _balanced_close_after(raw, idx, "(", ")")
            exposed = raw[idx + 1 : max(idx + 1, group_end - 1)]
            for item in re.finditer(_LEAN_NAME_RE, exposed):
                original = item.group(0)
                if original not in skip:
                    aliases.append(
                        {
                            "namespace": namespace,
                            "original": original,
                            "alias": original.rsplit(".", 1)[-1],
                        }
                    )
            idx = group_end
            continue
        suffix = raw[idx:].lstrip()
        if suffix.startswith("hiding"):
            hidden = [
                item.group(0)
                for item in re.finditer(_LEAN_IDENT_RE, suffix[len("hiding") :])
                if item.group(0) not in skip
            ]
            specs.append({"namespace": namespace, "hidden": hidden})
            break
        if suffix.startswith("renaming"):
            hidden: List[str] = []
            renames = suffix[len("renaming") :]
            for rename in re.finditer(
                rf"({_LEAN_NAME_RE})\s*(?:->|=>)\s*({_LEAN_IDENT_RE})",
                renames,
            ):
                original = rename.group(1)
                alias = rename.group(2)
                hidden.append(original.rsplit(".", 1)[-1])
                aliases.append(
                    {
                        "namespace": namespace,
                        "original": original,
                        "alias": alias,
                    }
                )
            specs.append({"namespace": namespace, "hidden": hidden})
            break
        specs.append({"namespace": namespace, "hidden": []})
    return specs, aliases


def _parse_open_namespaces(rest: str, *, allow_scoped: bool = False) -> List[str]:
    specs, _aliases = _parse_open_directives(rest, allow_scoped=allow_scoped)
    names: List[str] = []
    for spec in specs:
        namespace = str(spec.get("namespace") or "")
        if namespace and namespace not in names:
            names.append(namespace)
    return names


def _balanced_close_after(raw: str, start: int, opener: str, closer: str) -> int:
    depth = 0
    for idx in range(start, len(raw)):
        char = raw[idx]
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return idx + 1
    return len(raw)


def _scope_context_at(
    clean_source: str,
    index: int,
) -> Tuple[str, List[str], List[Dict[str, str]], Dict[str, List[str]]]:
    namespace_stack: List[str] = []
    open_specs: List[Dict[str, Any]] = []
    open_aliases: List[Dict[str, str]] = []
    blocks: List[Dict[str, Any]] = []

    def pop_block() -> None:
        if not blocks:
            return
        block = blocks.pop()
        for opened in reversed(list(block.get("opens") or [])):
            try:
                open_specs.remove(opened)
            except ValueError:
                pass
        for alias in reversed(list(block.get("aliases") or [])):
            try:
                open_aliases.remove(alias)
            except ValueError:
                pass
        if block.get("kind") == "namespace":
            parts = list(block.get("parts") or [])
            if parts and namespace_stack[-len(parts) :] == parts:
                del namespace_stack[-len(parts) :]
            elif parts:
                for _ in parts:
                    if namespace_stack:
                        namespace_stack.pop()

    for match in _SCOPE_CMD_RE.finditer(clean_source, 0, max(0, index)):
        namespace = str(match.group("namespace") or "").strip()
        if namespace:
            parts = [part for part in namespace.split(".") if part]
            namespace_stack.extend(parts)
            blocks.append(
                {
                    "kind": "namespace",
                    "name": namespace,
                    "parts": parts,
                    "opens": [],
                    "aliases": [],
                }
            )
            continue
        if match.group(0).lstrip().startswith("section"):
            blocks.append(
                {
                    "kind": "section",
                    "name": str(match.group("section") or "").strip(),
                    "parts": [],
                    "opens": [],
                    "aliases": [],
                }
            )
            continue
        opened, aliases = _parse_open_directives(str(match.group("open") or ""))
        if opened or aliases:
            open_specs.extend(opened)
            open_aliases.extend(aliases)
            if blocks:
                blocks[-1].setdefault("opens", []).extend(opened)
                blocks[-1].setdefault("aliases", []).extend(aliases)
            continue
        if match.group("open") is not None:
            continue
        end_name = str(match.group("end") or "").strip()
        if not blocks:
            continue
        if not end_name:
            pop_block()
            continue
        parts = [part for part in end_name.split(".") if part]
        top = blocks[-1]
        if top.get("kind") == "section" and top.get("name") == end_name:
            pop_block()
        elif (
            top.get("kind") == "namespace"
            and parts
            and namespace_stack[-len(parts) :] == parts
        ):
            pop_block()
        else:
            pop_block()
    open_namespaces: List[str] = []
    open_hiding: Dict[str, List[str]] = {}
    for spec in open_specs:
        namespace = str(spec.get("namespace") or "").strip()
        if namespace and namespace not in open_namespaces:
            open_namespaces.append(namespace)
        hidden = [str(item) for item in list(spec.get("hidden") or []) if str(item)]
        if namespace and hidden:
            current = open_hiding.setdefault(namespace, [])
            for item in hidden:
                if item not in current:
                    current.append(item)
    return (
        ".".join(namespace_stack),
        open_namespaces,
        [dict(alias) for alias in open_aliases],
        open_hiding,
    )


def _namespace_prefix_at(clean_source: str, index: int) -> str:
    namespace, _opens, _aliases, _hiding = _scope_context_at(clean_source, index)
    return namespace


def _open_namespaces_at(clean_source: str, index: int) -> List[str]:
    _namespace, opens, _aliases, _hiding = _scope_context_at(clean_source, index)
    return opens


def _open_context_at(
    clean_source: str,
    index: int,
) -> Tuple[List[str], List[Dict[str, str]], Dict[str, List[str]]]:
    _namespace, opens, aliases, hiding = _scope_context_at(clean_source, index)
    return opens, aliases, hiding


def _qualified_decl_name(source_name: str, namespace: str) -> str:
    raw = str(source_name or "").strip()
    if raw.startswith("_root_."):
        return raw[len("_root_.") :]
    ns = str(namespace or "").strip(".")
    return f"{ns}.{raw}" if ns else raw


def _strip_root_prefix(name: str) -> str:
    raw = str(name or "").strip(".")
    if raw.startswith("_root_."):
        return raw[len("_root_.") :]
    return raw


def _open_namespace_prefixes(opened_raw: str, current_namespace: str) -> List[str]:
    opened = _strip_root_prefix(opened_raw)
    if not opened:
        return []
    prefixes = [opened]
    if str(opened_raw or "").strip(".").startswith("_root_."):
        return prefixes
    namespace = str(current_namespace or "").strip(".")
    if namespace:
        namespace_parts = [part for part in namespace.split(".") if part]
        for size in range(len(namespace_parts), 0, -1):
            prefixes.append(".".join([*namespace_parts[:size], opened]))
    ordered: List[str] = []
    for prefix in prefixes:
        if prefix and prefix not in ordered:
            ordered.append(prefix)
    return ordered


def _open_hidden_names(
    open_hiding: Optional[Dict[str, List[str]]],
    opened_raw: str,
) -> Set[str]:
    raw = str(opened_raw or "").strip(".")
    stripped = _strip_root_prefix(raw)
    hidden: Set[str] = set()
    for key in (raw, stripped):
        for item in list((open_hiding or {}).get(key) or []):
            hidden.add(str(item).rsplit(".", 1)[-1])
    return hidden


def _reference_aliases(
    target_name: str,
    current_namespace: str,
    open_namespaces: Optional[List[str]] = None,
    open_aliases: Optional[List[Dict[str, str]]] = None,
    open_hiding: Optional[Dict[str, List[str]]] = None,
) -> Set[str]:
    target = str(target_name or "").strip()
    aliases = {target} if target else set()
    if target and not target.startswith("_root_."):
        aliases.add(f"_root_.{target}")
    namespace = str(current_namespace or "").strip(".")
    if namespace and target.startswith(namespace + "."):
        aliases.add(target[len(namespace) + 1 :])
    if namespace:
        parts = [part for part in namespace.split(".") if part]
        for size in range(len(parts) - 1, 0, -1):
            parent = ".".join(parts[:size])
            if target.startswith(parent + "."):
                aliases.add(target[len(parent) + 1 :])
    for opened in list(open_namespaces or []):
        opened_raw = str(opened or "").strip(".")
        hidden = _open_hidden_names(open_hiding, opened_raw)
        for opened_prefix in _open_namespace_prefixes(opened_raw, namespace):
            if target.startswith(opened_prefix + "."):
                alias = target[len(opened_prefix) + 1 :]
                if (
                    alias.rsplit(".", 1)[0] in hidden
                    or alias.split(".", 1)[0] in hidden
                ):
                    continue
                aliases.add(alias)
    for alias_spec in list(open_aliases or []):
        opened_raw = str(alias_spec.get("namespace") or "").strip(".")
        original = _strip_root_prefix(alias_spec.get("original") or "")
        alias = str(alias_spec.get("alias") or "").strip()
        if not opened_raw or not original or not alias:
            continue
        for opened_prefix in _open_namespace_prefixes(opened_raw, namespace):
            if target == f"{opened_prefix}.{original}":
                aliases.add(alias)
    return aliases


def _root_name_candidates_for_stem(stem: str) -> List[str]:
    raw = str(stem or "").strip()
    candidates = [raw]
    without_version = _VERSION_SUFFIX_RE.sub("", raw)
    candidates.append(without_version)
    if without_version.endswith("_visible"):
        candidates.append(without_version[: -len("_visible")])
    if raw.endswith("_visible"):
        candidates.append(raw[: -len("_visible")])
    candidates.append(root_name_for_export_stem(raw))
    ordered: List[str] = []
    for candidate in candidates:
        if candidate and candidate not in ordered:
            ordered.append(candidate)
    return ordered


def _infer_root_name_for_decls(stem: str, decls: List[Declaration]) -> str:
    names = {decl.name for decl in decls}
    for candidate in _root_name_candidates_for_stem(stem):
        if candidate in names:
            return candidate
    return root_name_for_export_stem(stem)


def _next_decl_boundary(clean_source: str, start: int, default_end: int) -> int:
    end = int(default_end)
    current_line_start = clean_source.rfind("\n", 0, start) + 1
    cursor = max(0, start)
    while cursor < len(clean_source) and clean_source[cursor].isspace():
        if clean_source[cursor] == "\n":
            current_line_start = cursor + 1
        cursor += 1
    for match in _SCOPE_CMD_RE.finditer(clean_source, max(0, start + 1), end):
        if match.start() <= start:
            continue
        if clean_source.rfind("\n", 0, match.start()) + 1 == current_line_start:
            continue
        stripped = match.group(0).lstrip()
        if (
            match.group("end") is not None
            or stripped.startswith("end")
            or stripped.startswith("open")
            or stripped.startswith("namespace")
            or stripped.startswith("section")
        ):
            return match.start()
    return end


def _strip_comments_and_strings(text: str) -> str:
    """Blank comments and literals before syntactic name-reference scans."""

    raw = str(text or "")
    out = list(raw)
    i = 0
    n = len(raw)
    while i < n:
        if raw.startswith("--", i):
            j = raw.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if raw.startswith("/-", i):
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if raw.startswith("/-", j):
                    depth += 1
                    j += 2
                    continue
                if raw.startswith("-/", j):
                    depth -= 1
                    j += 2
                    continue
                j += 1
            for k in range(i, min(j, n)):
                out[k] = " "
            i = j
            continue
        if raw[i] == "r":
            hash_start = i + 1
            quote_idx = hash_start
            while quote_idx < n and raw[quote_idx] == "#":
                quote_idx += 1
            if quote_idx < n and raw[quote_idx] == '"':
                hashes = raw[hash_start:quote_idx]
                close = '"' + hashes
                j = raw.find(close, quote_idx + 1)
                j = n if j < 0 else j + len(close)
                for k in range(i, min(j, n)):
                    out[k] = " "
                i = j
                continue
        if raw[i] == '"':
            j = i + 1
            while j < n:
                if raw[j] == "\\":
                    j += 2
                    continue
                if raw[j] == '"':
                    j += 1
                    break
                j += 1
            for k in range(i, min(j, n)):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def _mask_local_lambda_bodies(clean: str) -> str:
    out = list(str(clean or ""))
    fun_re = re.compile(r"\bfun\b(?P<params>.*?)=>", re.DOTALL)
    for match in fun_re.finditer(clean):
        params = str(match.group("params") or "")
        names = _lambda_bound_names(params)
        if not names:
            continue
        body_end = _lambda_body_end(clean, match.start(), match.end())
        for rel_start, rel_end in _lambda_bound_name_spans(params):
            start = match.start("params") + rel_start
            end = match.start("params") + rel_end
            for idx in range(start, end):
                out[idx] = " "
        segment_start = match.end()
        for name in names:
            _mask_name_occurrences(out, clean, name, segment_start, body_end)
    return "".join(out)


def _mask_name_occurrences(
    out: List[str],
    clean: str,
    name: str,
    start: int,
    end: int,
) -> None:
    name_re = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])")
    segment_start = max(0, int(start))
    segment_end = max(segment_start, min(len(clean), int(end)))
    segment = clean[segment_start:segment_end]
    for name_match in name_re.finditer(segment):
        abs_start = segment_start + name_match.start()
        abs_end = segment_start + name_match.end()
        if clean[max(0, abs_start - len("_root_.")) : abs_start] == "_root_.":
            continue
        if abs_start > 0 and clean[abs_start - 1] == ".":
            continue
        for idx in range(abs_start, abs_end):
            out[idx] = " "


def _lambda_bound_name_spans(params: str) -> List[Tuple[int, int]]:
    raw = str(params or "")
    spans, consumed_spans = _typed_binder_name_spans(raw)
    free_regions = _subtract_spans(len(raw), consumed_spans)
    for start, end in free_regions:
        prefix_end = raw.find(":", start, end)
        if prefix_end < 0:
            prefix_end = end
        for name_match in re.finditer(_LEAN_IDENT_RE, raw[start:prefix_end]):
            name = name_match.group(0)
            if name not in {"fun", "by", "_"}:
                spans.append((start + name_match.start(), start + name_match.end()))
    return spans


def _typed_binder_groups(
    raw: str,
) -> List[Tuple[List[Tuple[int, int]], Tuple[int, int]]]:
    groups: List[Tuple[List[Tuple[int, int]], Tuple[int, int]]] = []
    typed_group_re = re.compile(
        rf"[\(\{{\[]\s*((?:{_LEAN_IDENT_RE}\s+)*{_LEAN_IDENT_RE})\s*:"
    )
    for match in typed_group_re.finditer(str(raw or "")):
        spans: List[Tuple[int, int]] = []
        for name_match in re.finditer(_LEAN_IDENT_RE, match.group(1)):
            spans.append(
                (
                    match.start(1) + name_match.start(),
                    match.start(1) + name_match.end(),
                )
            )
        groups.append((spans, (match.start(), _binder_group_end(raw, match.start()))))
    return groups


def _typed_binder_name_spans(
    raw: str,
) -> Tuple[List[Tuple[int, int]], List[Tuple[int, int]]]:
    spans: List[Tuple[int, int]] = []
    consumed_spans: List[Tuple[int, int]] = []
    for group_spans, consumed_span in _typed_binder_groups(raw):
        spans.extend(group_spans)
        consumed_spans.append(consumed_span)
    return spans, consumed_spans


def _subtract_spans(length: int, spans: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    regions: List[Tuple[int, int]] = []
    cursor = 0
    for start, end in sorted(spans):
        start = max(0, min(length, start))
        end = max(start, min(length, end))
        if cursor < start:
            regions.append((cursor, start))
        cursor = max(cursor, end)
    if cursor < length:
        regions.append((cursor, length))
    return regions


def _lambda_bound_names(params: str) -> Set[str]:
    raw = str(params or "")
    return {raw[start:end] for start, end in _lambda_bound_name_spans(raw)}


def _mask_header_binder_scopes(clean: str, header_end: int) -> str:
    out = list(str(clean or ""))
    split = max(0, min(len(out), int(header_end or 0)))
    param_end = _decl_parameter_region_end(clean, split)
    header = clean[:param_end]
    for spans, (_group_start, group_end) in _typed_binder_groups(header):
        names = {header[start:end] for start, end in spans}
        for start, end in spans:
            for idx in range(start, end):
                out[idx] = " "
        for name in names:
            _mask_name_occurrences(out, clean, name, group_end, len(clean))
    _mask_quantifier_binders(out, clean, 0, split)
    return "".join(out)


def _mask_all_quantifier_binders(clean: str) -> str:
    out = list(str(clean or ""))
    _mask_quantifier_binders(out, clean, 0, len(clean))
    return "".join(out)


def _mask_quantifier_binders(
    out: List[str],
    clean: str,
    start: int,
    end: int,
) -> None:
    segment_start = max(0, min(len(clean), int(start or 0)))
    segment_end = max(segment_start, min(len(clean), int(end or 0)))
    quantifier_re = re.compile(r"(?:∀|∃|\bforall\b|\bexists\b)")
    for match in quantifier_re.finditer(clean, segment_start, segment_end):
        assign = _top_level_assign_after(clean, match.end(), segment_end)
        scope_end = segment_end if assign < 0 else assign
        cursor = match.end()
        while cursor < scope_end and clean[cursor].isspace():
            cursor += 1
        untyped_start = cursor
        if cursor < scope_end and clean[cursor] not in "({[":
            comma = clean.find(",", cursor, scope_end)
            colon = clean.find(":", cursor, scope_end)
            relation_positions = [
                pos
                for pos in (
                    clean.find(token, cursor, scope_end)
                    for token in ("∈", "∉", "<", "≤", ">", "≥", "≠")
                )
                if pos >= 0
            ]
            relation = min(relation_positions) if relation_positions else -1
            if comma >= 0 and colon >= 0 and colon < comma:
                names_text = clean[untyped_start:colon]
            elif comma >= 0 and relation >= 0 and relation < comma:
                names_text = clean[untyped_start:relation]
                colon = relation
            else:
                names_text = ""
            if names_text:
                spans: List[Tuple[int, int]] = []
                for name_match in re.finditer(_LEAN_IDENT_RE, names_text):
                    name = name_match.group(0)
                    if name not in {"forall", "exists", "_"}:
                        spans.append(
                            (
                                untyped_start + name_match.start(),
                                untyped_start + name_match.end(),
                            )
                        )
                names = {clean[span_start:span_end] for span_start, span_end in spans}
                for span_start, span_end in spans:
                    for idx in range(span_start, span_end):
                        out[idx] = " "
                for name in names:
                    _mask_name_occurrences(out, clean, name, comma + 1, scope_end)
                cursor = comma + 1
                while cursor < scope_end and clean[cursor].isspace():
                    cursor += 1
        while cursor < scope_end and clean[cursor] in "({[":
            group_end = _binder_group_end(clean, cursor)
            group_text = clean[cursor:group_end]
            spans, _ = _typed_binder_name_spans(group_text)
            if not spans:
                break
            names = {group_text[span_start:span_end] for span_start, span_end in spans}
            for span_start, span_end in spans:
                for idx in range(cursor + span_start, cursor + span_end):
                    out[idx] = " "
            body_start = group_end
            for name in names:
                _mask_name_occurrences(out, clean, name, body_start, scope_end)
            cursor = group_end
            while cursor < scope_end and clean[cursor].isspace():
                cursor += 1


def _top_level_assign_after(
    clean: str,
    start: int,
    end: int,
    *,
    skip_nested_let: bool = True,
) -> int:
    depth = 0
    idx = max(0, int(start))
    limit = max(idx, min(len(clean), int(end)))
    while idx < limit - 1:
        char = clean[idx]
        if char in "({[":
            depth += 1
            idx += 1
            continue
        if char in ")}]":
            depth = max(0, depth - 1)
            idx += 1
            continue
        if depth == 0 and clean.startswith(":=", idx):
            prefix = clean[max(0, idx - 120) : idx]
            if skip_nested_let and re.search(
                r"\blet\s+" + _LEAN_IDENT_RE + r"(?:\s*:\s*[^;\n]*?)?\s*$",
                prefix,
            ):
                idx += 2
                continue
            return idx
        idx += 1
    return -1


def _decl_parameter_region_end(clean: str, header_end: int) -> int:
    split = max(0, min(len(clean), int(header_end or 0)))
    match = _DECL_RE.search(clean[:split])
    if match is None:
        return split
    cursor = match.end("name")
    depth = 0
    closers = {")": "(", "}": "{", "]": "["}
    stack: List[str] = []
    while cursor < split:
        char = clean[cursor]
        if char in "({[":
            stack.append(char)
            depth += 1
        elif char in closers:
            if stack and stack[-1] == closers[char]:
                stack.pop()
                depth = max(0, depth - 1)
        elif char == ":" and depth == 0:
            if cursor + 1 >= len(clean) or clean[cursor + 1] != "=":
                return cursor
        cursor += 1
    return split


def _mask_local_value_shadows(
    clean: str,
    case_label_indexes: Optional[Dict[str, int]] = None,
) -> str:
    out = list(str(clean or ""))
    for match in re.finditer(rf"\b(?:let|have|set)\s+({_LEAN_IDENT_RE})\b", clean):
        name = match.group(1)
        scope_start = _local_value_scope_start(clean, match.start(), match.end())
        scope_end = _local_value_scope_end(clean, match.start(), match.end())
        for idx in range(match.start(1), match.end(1)):
            out[idx] = " "
        if scope_start < scope_end:
            _mask_name_occurrences(out, clean, name, scope_start, scope_end)
    pattern_value_re = re.compile(
        r"\b(?:let|have|obtain)\s+([^:\n;=]+?)\s*(?::|:=|:=\s*by)\s*"
    )
    for match in pattern_value_re.finditer(clean):
        pattern_text = str(match.group(1) or "")
        if re.fullmatch(rf"\s*{_LEAN_IDENT_RE}\s*", pattern_text):
            continue
        names = _pattern_bound_names(pattern_text)
        if not names:
            continue
        scope_start = _local_value_scope_start(clean, match.start(), match.end())
        scope_end = _local_value_scope_end(clean, match.start(), match.end())
        for name in names:
            _mask_name_occurrences(out, clean, name, match.start(1), match.end(1))
            if scope_start < scope_end:
                _mask_name_occurrences(out, clean, name, scope_start, scope_end)
    for match in re.finditer(r"\b(?:intro|intros)[ \t]+([^\n;:=]+)", clean):
        if match.start() > 0 and clean[match.start() - 1] == ".":
            continue
        scope_end = _local_value_scope_end(clean, match.start(), match.end())
        for name_match in re.finditer(_LEAN_IDENT_RE, match.group(1)):
            name = name_match.group(0)
            if name in {"with", "using", "by", "from"}:
                continue
            _mask_name_occurrences(out, clean, name, match.start(1), scope_end)
    for match in re.finditer(r"(?m)\brcases\b[^\n]*?\bwith\b([^\n;:=]+)", clean):
        pattern_text = str(match.group(1) or "")
        alternatives = [part for part in pattern_text.split("|")]
        case_scopes = _rcases_generated_case_scopes(clean, match.end())
        bullet_scopes = _rcases_generated_bullet_scopes(clean, match.end())
        for name in _pattern_bound_names(pattern_text):
            _mask_name_occurrences(out, clean, name, match.start(1), match.end(1))
        if case_scopes:
            label_indexes = case_label_indexes or {}
            for label, scope_start, scope_end in case_scopes:
                index = label_indexes.get(label)
                if index is None or index < 0 or index >= len(alternatives):
                    continue
                for name in _pattern_bound_names(alternatives[index]):
                    _mask_name_occurrences(out, clean, name, scope_start, scope_end)
            continue
        if bullet_scopes:
            for pattern, (scope_start, scope_end) in zip(alternatives, bullet_scopes):
                for name in _pattern_bound_names(pattern):
                    _mask_name_occurrences(out, clean, name, scope_start, scope_end)
            continue
        scope_end = _local_value_scope_end(clean, match.start(), match.end())
        for name in _pattern_bound_names(pattern_text):
            _mask_name_occurrences(out, clean, name, match.start(1), scope_end)
    for match in re.finditer(r"(?m)^\s*case\s+([^\n=]+)=>", clean):
        names = _case_branch_bound_names(match.group(1))
        if not names:
            continue
        scope_end = _case_branch_scope_end(clean, match.start(), match.end())
        for name in names:
            _mask_name_occurrences(out, clean, name, match.start(1), scope_end)
    for match in re.finditer(r"(?m)(?<!\|)\|\s*([^\n=]+)=>", clean):
        names = _pipe_branch_bound_names(match.group(1), case_label_indexes or {})
        if not names:
            continue
        scope_end = _pipe_branch_scope_end(clean, match.start(), match.end())
        for name in names:
            _mask_name_occurrences(out, clean, name, match.start(1), scope_end)
    return "".join(out)


def _case_branch_bound_names(pattern: str) -> List[str]:
    tokens = [
        match.group(0) for match in re.finditer(_LEAN_IDENT_RE, str(pattern or ""))
    ]
    return [token for token in tokens[1:] if token != "_"]


def _pipe_branch_bound_names(
    pattern: str,
    case_label_indexes: Dict[str, int],
) -> List[str]:
    tokens = [
        match.group(0)
        for match in re.finditer(_LEAN_IDENT_RE, str(pattern or ""))
        if match.group(0) != "_"
    ]
    if not tokens:
        return []
    if tokens[0] in case_label_indexes and len(tokens) > 1:
        tokens = tokens[1:]
    ordered: List[str] = []
    for token in tokens:
        if token not in ordered:
            ordered.append(token)
    return ordered


def _pipe_branch_scope_end(clean: str, start: int, fallback_end: int) -> int:
    line_start = clean.rfind("\n", 0, start) + 1
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        line_end = len(clean)
    same_line_next = re.search(r"(?<!\|)\|\s*[^|\n=]+?=>", clean[fallback_end:line_end])
    if same_line_next is not None:
        return fallback_end + same_line_next.start()
    base_line = clean[line_start:line_end]
    base_indent = len(base_line) - len(base_line.lstrip())
    scope_end = line_end
    scan_start = line_end + 1
    while scan_start < len(clean):
        scan_end = clean.find("\n", scan_start)
        scan_end = len(clean) if scan_end < 0 else scan_end
        line = clean[scan_start:scan_end]
        if line.strip():
            indent = len(line) - len(line.lstrip())
            if indent <= base_indent and line.lstrip().startswith("|"):
                break
            if indent < base_indent:
                break
        scope_end = scan_end
        if scan_end >= len(clean):
            break
        scan_start = scan_end + 1
    return scope_end


def _case_branch_scope_end(clean: str, start: int, fallback_end: int) -> int:
    line_start = clean.rfind("\n", 0, start) + 1
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        return len(clean)
    base_line = clean[line_start:line_end]
    base_indent = len(base_line) - len(base_line.lstrip())
    scan_start = line_end + 1
    scope_end = line_end
    while scan_start < len(clean):
        scan_end = clean.find("\n", scan_start)
        scan_end = len(clean) if scan_end < 0 else scan_end
        line = clean[scan_start:scan_end]
        if line.strip():
            indent = len(line) - len(line.lstrip())
            if indent <= base_indent and line.lstrip().startswith("case "):
                break
        scope_end = scan_end
        if scan_end >= len(clean):
            break
        scan_start = scan_end + 1
    return scope_end


def _case_label_indexes(decls: List[Declaration]) -> Dict[str, int]:
    raw_indexes: Dict[str, Optional[int]] = {
        "inl": 0,
        "left": 0,
        "inr": 1,
        "right": 1,
    }
    constructor_re = re.compile(rf"(?m)^\s*\|\s*({_LEAN_IDENT_RE})\b")
    for decl in decls:
        if "inductive" not in str(decl.kind or "").split():
            continue
        labels = [match.group(1) for match in constructor_re.finditer(decl.body)]
        for index, label in enumerate(labels):
            if label not in raw_indexes:
                raw_indexes[label] = index
                continue
            if raw_indexes[label] != index:
                raw_indexes[label] = None
    return {label: index for label, index in raw_indexes.items() if index is not None}


def _pattern_bound_names(pattern: str) -> List[str]:
    names: List[str] = []
    for name_match in re.finditer(_LEAN_IDENT_RE, str(pattern or "")):
        name = name_match.group(0)
        if name in {"with", "using", "by", "from", "_"}:
            continue
        if name not in names:
            names.append(name)
    return names


def _rcases_generated_case_scopes(
    clean: str,
    fallback_end: int,
) -> List[Tuple[str, int, int]]:
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        return []
    next_start = line_end + 1
    while next_start < len(clean):
        next_end = clean.find("\n", next_start)
        next_end = len(clean) if next_end < 0 else next_end
        line = clean[next_start:next_end]
        if not line.strip():
            if next_end >= len(clean):
                return []
            next_start = next_end + 1
            continue
        stripped = line.lstrip()
        if not stripped.startswith("case "):
            return []
        case_indent = len(line) - len(stripped)
        scopes: List[Tuple[str, int, int]] = []
        case_start = next_start
        case_label = _case_label_for_line(line)
        scan_start = next_start
        while scan_start < len(clean):
            scan_end = clean.find("\n", scan_start)
            scan_end = len(clean) if scan_end < 0 else scan_end
            scan_line = clean[scan_start:scan_end]
            if scan_line.strip():
                scan_indent = len(scan_line) - len(scan_line.lstrip())
                stripped_scan = scan_line.lstrip()
                if scan_indent == case_indent and stripped_scan.startswith("case "):
                    if scan_start != case_start:
                        scopes.append((case_label, case_start, scan_start))
                        case_start = scan_start
                        case_label = _case_label_for_line(scan_line)
                elif scan_indent < case_indent:
                    break
            if scan_end >= len(clean):
                scan_start = scan_end
                break
            scan_start = scan_end + 1
        scopes.append(
            (
                case_label,
                case_start,
                scan_start if scan_start > case_start else len(clean),
            )
        )
        return [(label, start, end) for label, start, end in scopes if label]
    return []


def _case_label_for_line(line: str) -> str:
    match = re.match(rf"\s*case\s+({_LEAN_IDENT_RE})\b", str(line or ""))
    return match.group(1) if match else ""


def _rcases_generated_bullet_scopes(
    clean: str, fallback_end: int
) -> List[Tuple[int, int]]:
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        return []
    next_start = line_end + 1
    while next_start < len(clean):
        next_end = clean.find("\n", next_start)
        next_end = len(clean) if next_end < 0 else next_end
        line = clean[next_start:next_end]
        if not line.strip():
            if next_end >= len(clean):
                return []
            next_start = next_end + 1
            continue
        stripped = line.lstrip()
        if stripped.startswith("case "):
            return []
        if not stripped.startswith("·"):
            return []
        bullet_indent = len(line) - len(stripped)
        scopes: List[Tuple[int, int]] = []
        bullet_start = next_start
        scan_start = next_start
        while scan_start < len(clean):
            scan_end = clean.find("\n", scan_start)
            scan_end = len(clean) if scan_end < 0 else scan_end
            scan_line = clean[scan_start:scan_end]
            if scan_line.strip():
                scan_indent = len(scan_line) - len(scan_line.lstrip())
                if scan_indent == bullet_indent and scan_line.lstrip().startswith("·"):
                    if scan_start != bullet_start:
                        scopes.append((bullet_start, scan_start))
                        bullet_start = scan_start
                elif scan_indent < bullet_indent:
                    break
            if scan_end >= len(clean):
                scan_start = scan_end
                break
            scan_start = scan_end + 1
        scopes.append(
            (bullet_start, scan_start if scan_start > bullet_start else len(clean))
        )
        return scopes
    return []


def _local_value_scope_start(clean: str, start: int, fallback_end: int) -> int:
    line_start = clean.rfind("\n", 0, start) + 1
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        line_end = len(clean)
    same_line_separator = clean.find(";", fallback_end, line_end)
    if same_line_separator >= 0:
        return same_line_separator + 1
    if line_end >= len(clean):
        return len(clean)
    base_line = clean[line_start:line_end]
    base_indent = len(base_line) - len(base_line.lstrip())
    next_start = line_end + 1
    while next_start < len(clean):
        next_end = clean.find("\n", next_start)
        next_end = len(clean) if next_end < 0 else next_end
        line = clean[next_start:next_end]
        if not line.strip():
            if next_end >= len(clean):
                return len(clean)
            next_start = next_end + 1
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= base_indent:
            return line_end + 1
        scan_start = next_end + 1
        while scan_start < len(clean):
            scan_end = clean.find("\n", scan_start)
            scan_end = len(clean) if scan_end < 0 else scan_end
            scan_line = clean[scan_start:scan_end]
            if scan_line.strip():
                scan_indent = len(scan_line) - len(scan_line.lstrip())
                if scan_indent <= base_indent:
                    return scan_start
            if scan_end >= len(clean):
                break
            scan_start = scan_end + 1
        return len(clean)
    return len(clean)


def _local_value_scope_end(clean: str, start: int, fallback_end: int) -> int:
    line_start = clean.rfind("\n", 0, start) + 1
    line_end = clean.find("\n", fallback_end)
    if line_end < 0:
        return len(clean)
    base_line = clean[line_start:line_end]
    base_indent = len(base_line) - len(base_line.lstrip())
    scope_end = line_end
    next_start = line_end + 1
    while next_start < len(clean):
        next_end = clean.find("\n", next_start)
        next_end = len(clean) if next_end < 0 else next_end
        line = clean[next_start:next_end]
        if line.strip():
            indent = len(line) - len(line.lstrip())
            if indent <= base_indent and line.lstrip().startswith("·"):
                break
            if indent < base_indent:
                break
        scope_end = next_end
        if next_end >= len(clean):
            break
        next_start = next_end + 1
    return scope_end


def _binder_group_end(raw: str, start: int) -> int:
    open_to_close = {"(": ")", "{": "}", "[": "]"}
    opener = raw[start] if 0 <= start < len(raw) else ""
    closer = open_to_close.get(opener)
    if closer is None:
        return start
    depth = 0
    for idx in range(start, len(raw)):
        char = raw[idx]
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return idx + 1
    return len(raw)


def _lambda_body_end(clean: str, fun_start: int, body_start: int) -> int:
    prefix = clean[:fun_start].rstrip()
    if prefix.endswith("("):
        open_index = len(prefix) - 1
        depth = 0
        for idx in range(open_index, len(clean)):
            char = clean[idx]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    return idx
    body_line_start = clean.rfind("\n", 0, body_start) + 1
    lambda_indent = len(clean[body_line_start:fun_start]) - len(
        clean[body_line_start:fun_start].lstrip()
    )
    first_newline = clean.find("\n", body_start)
    line_end = len(clean) if first_newline < 0 else first_newline
    depth = 0
    for idx in range(body_start, line_end):
        char = clean[idx]
        if char in "([{":
            depth += 1
            continue
        if char in ")]}":
            if depth == 0:
                return idx
            depth -= 1
            continue
        if (
            depth == 0
            and char == ";"
            and idx > body_start
            and idx + 1 < line_end
            and clean[idx - 1] == "<"
            and clean[idx + 1] == ">"
        ):
            continue
        if depth == 0 and char in ",;":
            return idx
    if first_newline >= 0:
        line_start = first_newline + 1
        end = first_newline
        while line_start < len(clean):
            line_end = clean.find("\n", line_start)
            line_end = len(clean) if line_end < 0 else line_end
            line = clean[line_start:line_end]
            if line.strip():
                indent = len(line) - len(line.lstrip())
                if indent <= lambda_indent:
                    break
            end = line_end
            if line_end >= len(clean):
                break
            line_start = line_end + 1
        if end > first_newline:
            return end
    return line_end


def _local_projection_prefixes(text: str) -> Set[str]:
    clean = _strip_comments_and_strings(text)
    names: Set[str] = set()
    for match in re.finditer(rf"\b(?:let|have|set)\s+({_LEAN_IDENT_RE})\b", clean):
        names.add(match.group(1))
    for match in re.finditer(r"(?m)^\s*(?:intro|intros)[ \t]+([^\n;:=]+)", clean):
        for name in re.findall(_LEAN_IDENT_RE, match.group(1)):
            if name not in {"with", "using", "by", "from"}:
                names.add(name)
    return names


def _prune_shadowed_parent_deps(
    deps: Set[str],
    decl: Declaration,
    search_text: str,
    decl_by_name: Dict[str, Declaration],
    forced_resolutions: Optional[Dict[str, str]] = None,
) -> Set[str]:
    current_parts = [part for part in str(decl.namespace or "").split(".") if part]
    pruned = set(deps)
    by_short: Dict[str, List[str]] = {}
    for dep in deps:
        by_short.setdefault(dep.rsplit(".", 1)[-1], []).append(dep)
    for same_short in by_short.values():
        if len(same_short) <= 1:
            continue
        short = same_short[0].rsplit(".", 1)[-1]
        explicit: Set[str] = set()
        for dep in same_short:
            if "." in dep:
                full_ref_re = re.compile(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(dep)}(?![A-Za-z0-9_'.])"
                )
                root_ref_re = re.compile(
                    rf"(?<![A-Za-z0-9_'.])_root_\.{re.escape(dep)}"
                    rf"(?![A-Za-z0-9_'.])"
                )
                if full_ref_re.search(search_text) or root_ref_re.search(search_text):
                    explicit.add(dep)
            else:
                root_ref_re = re.compile(
                    rf"(?<![A-Za-z0-9_'.])_root_\.{re.escape(dep)}"
                    rf"(?![A-Za-z0-9_'.])"
                )
                if root_ref_re.search(search_text):
                    explicit.add(dep)
        unqualified_re = re.compile(
            rf"(?<![A-Za-z0-9_'.]){re.escape(short)}(?![A-Za-z0-9_'.])"
        )
        resolved = ""
        forced = dict(forced_resolutions or {}).get(short, "")
        if unqualified_re.search(search_text):
            if forced in same_short:
                resolved = forced
            current_type = _decl_result_type(decl.statement)
            if current_type and not resolved:
                type_matches = [
                    dep
                    for dep in same_short
                    if _decl_result_type(
                        decl_by_name[dep].statement if dep in decl_by_name else ""
                    )
                    == current_type
                ]
                if len(type_matches) == 1:
                    resolved = type_matches[0]
            priority: List[str] = []
            if not resolved:
                for size in range(len(current_parts), 0, -1):
                    priority.append(".".join([*current_parts[:size], short]))
                priority.append(short)
                for opened in decl.open_namespaces:
                    opened_raw = str(opened or "").strip(".")
                    if short in _open_hidden_names(decl.open_hiding, opened_raw):
                        continue
                    for opened_prefix in _open_namespace_prefixes(
                        opened_raw,
                        decl.namespace,
                    ):
                        priority.append(f"{opened_prefix}.{short}")
                for alias_spec in decl.open_aliases:
                    if str(alias_spec.get("alias") or "") != short:
                        continue
                    original = _strip_root_prefix(alias_spec.get("original") or "")
                    opened_raw = str(alias_spec.get("namespace") or "").strip(".")
                    if not original or not opened_raw:
                        continue
                    for opened_prefix in _open_namespace_prefixes(
                        opened_raw,
                        decl.namespace,
                    ):
                        priority.append(f"{opened_prefix}.{original}")
                for candidate in priority:
                    if candidate in same_short:
                        resolved = candidate
                        break
        keep = set(explicit)
        if resolved:
            keep.add(resolved)
        if keep:
            for dep in same_short:
                if dep not in keep:
                    pruned.discard(dep)
            continue
        ranked = sorted(
            same_short,
            key=lambda dep: len([part for part in dep.split(".")[:-1]]),
            reverse=True,
        )
        for dep in ranked[1:]:
            if "." not in dep:
                root_ref_re = re.compile(
                    rf"(?<![A-Za-z0-9_'.])_root_\.{re.escape(dep)}"
                    rf"(?![A-Za-z0-9_'.])"
                )
                if not root_ref_re.search(search_text):
                    pruned.discard(dep)
                continue
            full_ref_re = re.compile(
                rf"(?<![A-Za-z0-9_'.]){re.escape(dep)}(?![A-Za-z0-9_'.])"
            )
            if full_ref_re.search(search_text):
                continue
            pruned.discard(dep)
    return pruned


def _local_expected_type_resolutions(
    text: str,
    deps: Set[str],
    decl_by_name: Dict[str, Declaration],
) -> Dict[str, str]:
    by_short: Dict[str, List[str]] = {}
    for dep in deps:
        by_short.setdefault(dep.rsplit(".", 1)[-1], []).append(dep)
    if not by_short:
        return {}
    forced: Dict[str, str] = {}
    raw = str(text or "")
    typed_value_re = re.compile(rf"\b(?:have|let)\s+{_LEAN_IDENT_RE}\s*:")
    for match in typed_value_re.finditer(raw):
        assign = _top_level_assign_after(
            raw,
            match.end(),
            len(raw),
            skip_nested_let=False,
        )
        if assign < 0:
            continue
        expected_type = " ".join(raw[match.end() : assign].split())
        assigned = raw[assign + 2 :]
        ref_pattern = rf"\(?\s*({_LEAN_IDENT_RE})\s*\)?"
        ref_match = re.match(rf"\s*{ref_pattern}(?=\s|$|[;,\n])", assigned)
        if ref_match is not None and ref_match.group(1) == "by":
            ref_match = re.match(
                rf"\s*by\s+(?:exact|simpa\s+using)\s+{ref_pattern}"
                r"(?=\s|$|[;,\n])",
                assigned,
            )
        if ref_match is None:
            continue
        ref = str(ref_match.group(1) or "")
        candidates = by_short.get(ref) or []
        if not expected_type or len(candidates) <= 1:
            continue
        type_matches = [
            dep
            for dep in candidates
            if _decl_result_type(
                decl_by_name[dep].statement if dep in decl_by_name else ""
            )
            == expected_type
        ]
        if len(type_matches) == 1:
            forced[ref] = type_matches[0]
    return forced


def _decl_result_type(statement: str) -> str:
    text = " ".join(str(statement or "").split())
    match = _DECL_RE.search(text)
    if match is None:
        return ""
    cursor = match.end("name")
    depth = 0
    stack: List[str] = []
    closers = {")": "(", "}": "{", "]": "["}
    while cursor < len(text):
        char = text[cursor]
        if char in "({[":
            stack.append(char)
            depth += 1
        elif char in closers:
            if stack and stack[-1] == closers[char]:
                stack.pop()
                depth = max(0, depth - 1)
        elif char == ":" and depth == 0:
            if cursor + 1 >= len(text) or text[cursor + 1] != "=":
                return text[cursor + 1 :].strip()
        cursor += 1
    return ""


def _structure_fields_by_name(decls: List[Declaration]) -> Dict[str, Set[str]]:
    fields_by_type: Dict[str, Set[str]] = {}
    field_re = re.compile(rf"(?m)^\s*({_LEAN_IDENT_RE})\s*:")
    for decl in decls:
        if "structure" not in str(decl.kind or "").split():
            continue
        body = _strip_comments_and_strings(decl.body)
        where_index = body.find("where")
        if where_index < 0:
            continue
        fields = {
            match.group(1)
            for match in field_re.finditer(body[where_index + len("where") :])
        }
        if not fields:
            continue
        aliases = {
            decl.name,
            decl.source_name,
            decl.name.rsplit(".", 1)[-1],
            _strip_root_prefix(decl.name),
            _strip_root_prefix(decl.source_name),
        }
        for alias in aliases:
            if alias:
                fields_by_type.setdefault(alias, set()).update(fields)
    return fields_by_type


def _first_type_name(type_text: str) -> str:
    match = re.search(_LEAN_NAME_RE, str(type_text or ""))
    return _strip_root_prefix(match.group(0)) if match else ""


def _header_binder_types(clean: str, header_end: int) -> Dict[str, str]:
    split = max(0, min(len(clean), int(header_end or 0)))
    header = clean[: _decl_parameter_region_end(clean, split)]
    binder_types: Dict[str, str] = {}
    for spans, (group_start, group_end) in _typed_binder_groups(header):
        group_text = header[group_start:group_end]
        colon = group_text.find(":")
        if colon < 0:
            continue
        type_text = group_text[colon + 1 :].strip()
        if type_text and type_text[-1] in ")}]":
            type_text = type_text[:-1].strip()
        type_name = _first_type_name(type_text)
        if not type_name:
            continue
        for span_start, span_end in spans:
            name = header[span_start:span_end]
            if name and name != "_":
                binder_types[name] = type_name
    return binder_types


def _qualified_reference_is_local_projection(
    qualified_name: str,
    binder_types: Dict[str, str],
    structure_fields: Dict[str, Set[str]],
) -> bool:
    head, separator, tail = str(qualified_name or "").partition(".")
    if not separator or head not in binder_types:
        return False
    field = tail.split(".", 1)[0]
    type_name = _strip_root_prefix(binder_types.get(head, ""))
    if not field or not type_name:
        return False
    return field in structure_fields.get(type_name, set())


def _local_typed_value_scopes(clean: str) -> List[Tuple[str, str, int, int]]:
    scopes: List[Tuple[str, str, int, int]] = []
    simple_typed_re = re.compile(rf"\b(?:let|have|set)\s+({_LEAN_IDENT_RE})\s*:")
    for match in simple_typed_re.finditer(str(clean or "")):
        assign = _top_level_assign_after(
            clean,
            match.end(),
            len(clean),
            skip_nested_let=False,
        )
        if assign < 0:
            continue
        type_name = _first_type_name(clean[match.end() : assign])
        if not type_name:
            continue
        scopes.append(
            (
                match.group(1),
                type_name,
                _local_value_scope_start(clean, match.start(), match.end()),
                _local_value_scope_end(clean, match.start(), match.end()),
            )
        )
    return scopes


def _local_value_receiver_scopes(clean: str) -> List[Tuple[str, int, int]]:
    scopes: List[Tuple[str, int, int]] = []
    for match in re.finditer(rf"\b(?:let|have|set)\s+({_LEAN_IDENT_RE})\b", clean):
        scopes.append(
            (
                match.group(1),
                _local_value_scope_start(clean, match.start(), match.end()),
                _local_value_scope_end(clean, match.start(), match.end()),
            )
        )
    return scopes


def _mask_local_head_qualified_references(
    clean: str,
    header_end: int,
) -> str:
    out = list(str(clean or ""))
    local_scopes: List[Tuple[str, int, int]] = []
    for name in _header_binder_types(clean, header_end):
        local_scopes.append((name, 0, len(clean)))
    for name, _type_name, start, end in _local_typed_value_scopes(clean):
        local_scopes.append((name, start, end))
    for name, start, end in _local_value_receiver_scopes(clean):
        local_scopes.append((name, start, end))
    for name, start, end in local_scopes:
        if not name or name == "_":
            continue
        name_re = re.compile(
            rf"(?<![A-Za-z0-9_']){re.escape(name)}"
            rf"(?:\.{_LEAN_IDENT_RE})+(?![A-Za-z0-9_'])"
        )
        segment_start = max(0, int(start))
        segment_end = max(segment_start, min(len(clean), int(end)))
        for match in name_re.finditer(clean[segment_start:segment_end]):
            abs_start = segment_start + match.start()
            abs_end = segment_start + match.end()
            if clean[max(0, abs_start - len("_root_.")) : abs_start] == "_root_.":
                continue
            for idx in range(abs_start, abs_end):
                out[idx] = " "
    return "".join(out)


def parse_declarations(
    source: str,
    *,
    root_name: str = "",
    source_html_name: str = "",
) -> List[Declaration]:
    """Split a solved Lean file into top-level declarations."""

    match_source = _strip_comments_and_strings(source)
    matches = list(_DECL_RE.finditer(match_source))
    decls: List[Declaration] = []
    root = str(root_name or "").strip()
    for index, match in enumerate(matches):
        start = match.start()
        namespace = _namespace_prefix_at(match_source, start)
        open_namespaces, open_aliases, open_hiding = _open_context_at(
            match_source,
            start,
        )
        inline_specs, inline_aliases = _parse_open_directives(
            str(match.group("inline_open") or ""),
            allow_scoped=True,
        )
        for spec in inline_specs:
            namespace_name = str(spec.get("namespace") or "").strip()
            if namespace_name and namespace_name not in open_namespaces:
                open_namespaces.append(namespace_name)
            hidden = [str(item) for item in list(spec.get("hidden") or []) if str(item)]
            if namespace_name and hidden:
                current = open_hiding.setdefault(namespace_name, [])
                for item in hidden:
                    if item not in current:
                        current.append(item)
        open_aliases.extend(inline_aliases)
        open_namespaces = list(dict.fromkeys(open_namespaces))
        source_name = match.group("name")
        name = _qualified_decl_name(source_name, namespace)
        default_end = (
            matches[index + 1].start() if index + 1 < len(matches) else len(source)
        )
        raw_end = _next_decl_boundary(match_source, start, default_end)
        # The raw slice extends to the next declaration's regex match, which
        # would swallow that declaration's docstring/attribute lines and
        # inflate this declaration's proof_length — trim them off.
        body = _trim_trailing_noncode(source[start:raw_end])
        end = start + len(body)
        header_end = _decl_header_end(source, start, end)
        # Statement: from the name to the first `:=` — best-effort summary
        # for the tooltip. Comments are stripped so tooltip text (and the
        # JSON embedded in the HTML page) never carries free-form comment
        # content from the source.
        header = _strip_comments(source[start:header_end].rsplit(":=", 1)[0])
        statement = " ".join(header.split())
        if len(statement) > 400:
            statement = statement[:400] + "…"
        line_start, col_start = _line_col_for_index(source, start)
        line_end = _line_for_inclusive_end(source, start, end)
        _end_line, col_end = _line_col_for_index(source, max(start, end - 1))
        proof_char_start = min(max(header_end, start), end)
        proof_line = _line_col_for_index(source, proof_char_start)[0]
        proof_line_end = _line_for_inclusive_end(source, proof_char_start, end)
        decls.append(
            Declaration(
                name=name,
                kind=" ".join(match.group("kind").split()),
                line=line_start,
                line_end=line_end,
                col_start=col_start,
                col_end=col_end,
                char_start=start,
                char_end=end,
                byte_start=_byte_len(source[:start]),
                byte_end=_byte_len(source[:end]),
                source_span={"start": start, "end": end},
                proof_line=proof_line,
                proof_line_end=proof_line_end,
                proof_char_start=proof_char_start,
                proof_char_end=end,
                proof_span={"start": proof_char_start, "end": end},
                body=body,
                statement=statement,
                proof_length=body.count("\n") + 1,
                source_hash=_text_hash(body.strip()),
                source_name=source_name,
                namespace=namespace,
                open_namespaces=open_namespaces,
                open_hiding={key: list(value) for key, value in open_hiding.items()},
                open_aliases=[dict(alias) for alias in open_aliases],
                href=_href_for_line(source_html_name, line_start, line_end),
                proof_href=_href_for_line(source_html_name, proof_line, proof_line_end),
                is_root=(name == root) if root else name.startswith("putnam_"),
            )
        )
    return decls


def build_graph(decls: List[Declaration]) -> None:
    """Populate ``deps``/``external_refs`` on each declaration in place."""

    local_names = {decl.name for decl in decls}
    decl_by_name = {decl.name: decl for decl in decls}
    case_label_indexes = _case_label_indexes(decls)
    # Prime-aware boundaries: Lean identifiers may end in ' — a plain \b
    # after a quote matches inside LONGER names (helper' vs helper'2),
    # fabricating edges. Require a non-identifier char on both sides.
    name_patterns_by_decl: Dict[str, Dict[str, List[re.Pattern[str]]]] = {
        decl.name: {
            name: [
                re.compile(rf"(?<![A-Za-z0-9_'.]){re.escape(alias)}(?![A-Za-z0-9_'.])")
                for alias in sorted(
                    _reference_aliases(
                        name,
                        decl.namespace,
                        decl.open_namespaces,
                        decl.open_aliases,
                        decl.open_hiding,
                    ),
                    key=lambda item: (-len(item), item),
                )
            ]
            for name in local_names
        }
        for decl in decls
    }
    full_local_patterns: List[re.Pattern[str]] = [
        re.compile(rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'.])")
        for name in local_names
        if "." in name
    ]
    for decl in decls:
        # Scan the FULL body (comments stripped): dependencies referenced in
        # the declaration's own header (hypothesis types, single-line
        # `:= by exact X` proofs) are real edges. Self-references are
        # excluded by the name != decl.name check below, so there is no
        # need to drop the header line.
        header_end = max(
            0,
            min(len(decl.body), int(decl.proof_char_start - decl.char_start)),
        )
        raw_search_text = _strip_comments_and_strings(decl.body)
        qualified_search_text = _mask_local_head_qualified_references(
            raw_search_text,
            header_end,
        )
        qualified_deps: Set[str] = set()
        for name in local_names:
            if name == decl.name or "." not in name:
                continue
            full_ref_re = re.compile(
                rf"(?<![A-Za-z0-9_'.])(?:_root_\.)?{re.escape(name)}"
                rf"(?![A-Za-z0-9_'.])"
            )
            if full_ref_re.search(qualified_search_text):
                qualified_deps.add(name)
        search_text = raw_search_text
        search_text = _mask_header_binder_scopes(search_text, header_end)
        search_text = _mask_all_quantifier_binders(search_text)
        search_text = _mask_local_lambda_bodies(search_text)
        search_text = _mask_local_value_shadows(search_text, case_label_indexes)
        masked_search = list(search_text)
        decl_match = _DECL_RE.search(search_text[:header_end])
        if decl_match is not None:
            for idx in range(decl_match.start("name"), decl_match.end("name")):
                masked_search[idx] = " "
            search_text = "".join(masked_search)
        deps: Set[str] = set()
        for name, patterns in name_patterns_by_decl.get(decl.name, {}).items():
            if name != decl.name and any(
                pattern.search(search_text) for pattern in patterns
            ):
                deps.add(name)
        deps.update(qualified_deps)
        forced_resolutions = _local_expected_type_resolutions(
            raw_search_text,
            deps,
            decl_by_name,
        )
        deps = _prune_shadowed_parent_deps(
            deps,
            decl,
            search_text,
            decl_by_name,
            forced_resolutions,
        )
        decl.deps = sorted(deps)
        external_search_text = search_text
        for patterns in name_patterns_by_decl.get(decl.name, {}).values():
            for pattern in patterns:
                external_search_text = pattern.sub(" ", external_search_text)
        for pattern in full_local_patterns:
            external_search_text = pattern.sub(" ", external_search_text)
        externals = set()
        for ref in _EXTERNAL_REF_RE.findall(external_search_text):
            if ref in local_names:
                continue
            externals.add(ref)
        decl.external_refs = sorted(externals)


def graph_payload(
    problem: str,
    decls: List[Declaration],
    *,
    include_external: bool = True,
    axioms: Optional[List[str]] = None,
    audit_ok: Optional[bool] = None,
    audit_error: str = "",
    unexpected_axioms: Optional[List[str]] = None,
    artifact_path: str = "",
    source_html_path: str = "",
    proof_graph_record: Optional[Dict[str, Any]] = None,
    root_name: str = "",
) -> Dict[str, Any]:
    _attach_runtime_graph_metadata(
        decls,
        proof_graph_record,
        problem=root_name or problem,
    )
    nodes = []
    links = []
    for decl in decls:
        nodes.append(
            {
                "id": decl.name,
                "decl_name": decl.name,
                "group": "root" if decl.is_root else "local",
                "kind": decl.kind,
                "line": decl.line,
                "line_start": decl.line,
                "line_end": decl.line_end,
                "col_start": decl.col_start,
                "col_end": decl.col_end,
                "char_start": decl.char_start,
                "char_end": decl.char_end,
                "byte_start": decl.byte_start,
                "byte_end": decl.byte_end,
                "source_span": dict(decl.source_span),
                "proof_start_line": decl.proof_line,
                "proof_end_line": decl.proof_line_end,
                "proof_char_start": decl.proof_char_start,
                "proof_char_end": decl.proof_char_end,
                "proof_span": dict(decl.proof_span),
                "proof_length": decl.proof_length,
                "statement": decl.statement,
                "source_hash": decl.source_hash,
                "href": decl.href,
                "proof_href": decl.proof_href,
                "graph_node_id": decl.graph_node_id,
                "runtime_source_hash_match": decl.runtime_source_hash_match,
            }
        )
        for dep in decl.deps:
            links.append({"source": decl.name, "target": dep, "kind": "local"})
    if include_external:
        external_names: Set[str] = set()
        for decl in decls:
            external_names.update(decl.external_refs)
        for name in sorted(external_names):
            nodes.append(
                {
                    "id": name,
                    "group": "external",
                    "kind": "external",
                    "line": 0,
                    "proof_length": 1,
                    "statement": name,
                }
            )
        for decl in decls:
            for ref in decl.external_refs:
                links.append({"source": decl.name, "target": ref, "kind": "external"})
    local_count = sum(1 for node in nodes if node["group"] != "external")
    return {
        "problem": problem,
        "artifact_path": str(artifact_path or ""),
        "source_html_path": str(source_html_path or ""),
        "local_declarations": local_count,
        "external_references": len(nodes) - local_count,
        "edges": len(links),
        "axioms": list(axioms or []),
        "axiom_audit_ok": audit_ok,
        "axiom_audit_error": str(audit_error or ""),
        "unexpected_axioms": list(unexpected_axioms or []),
        "nodes": nodes,
        "links": links,
    }


def _attach_runtime_graph_metadata(
    decls: List[Declaration],
    proof_graph_record: Optional[Dict[str, Any]],
    *,
    problem: str,
) -> None:
    if not isinstance(proof_graph_record, dict):
        return
    raw_nodes = proof_graph_record.get("nodes")
    if not isinstance(raw_nodes, list):
        return
    graph_nodes = [node for node in raw_nodes if isinstance(node, dict)]
    helper_name_to_node_id = {
        str(name or "").strip(): str(node_id or "").strip()
        for name, node_id in dict(
            proof_graph_record.get("helper_name_to_node_id") or {}
        ).items()
        if str(name or "").strip() and str(node_id or "").strip()
    }
    root_node_id = str(proof_graph_record.get("root_node_id") or "root").strip()
    nodes_by_id = {
        str(node.get("node_id") or "").strip(): node
        for node in graph_nodes
        if str(node.get("node_id") or "").strip()
    }
    helpers_by_name: Dict[str, Dict[str, Any]] = {}
    for node in graph_nodes:
        if str(node.get("kind") or "") != "helper":
            continue
        name = str(node.get("name") or "").strip()
        if name and name not in helpers_by_name:
            helpers_by_name[name] = node

    def runtime_decl_source_hash(node: Dict[str, Any]) -> str:
        metadata = dict(node.get("metadata") or {})
        return str(
            metadata.get("verified_helper_source_hash")
            or metadata.get("declaration_source_hash")
            or metadata.get("root_declaration_source_hash")
            or node.get("source_hash")
            or ""
        ).strip()

    def maybe_bind(candidate: Optional[Dict[str, Any]], decl: Declaration) -> bool:
        if candidate is None:
            return False
        runtime_hash = runtime_decl_source_hash(candidate)
        if runtime_hash and runtime_hash != decl.source_hash:
            decl.runtime_source_hash_match = False
            return False
        decl.graph_node_id = str(candidate.get("node_id") or "").strip()
        if runtime_hash:
            decl.runtime_source_hash_match = True
        return True

    for decl in decls:
        if decl.is_root or decl.name == str(problem or "").strip():
            if maybe_bind(nodes_by_id.get(root_node_id), decl):
                continue
        if not decl.graph_node_id:
            node_id = helper_name_to_node_id.get(decl.name)
            if maybe_bind(nodes_by_id.get(node_id) if node_id else None, decl):
                continue
        if not decl.graph_node_id:
            maybe_bind(helpers_by_name.get(decl.name), decl)


def source_map_payload(
    problem: str,
    decls: List[Declaration],
    *,
    artifact_path: str = "",
    source_html_path: str = "",
) -> Dict[str, Any]:
    return {
        "problem": str(problem or ""),
        "artifact_path": str(artifact_path or ""),
        "source_html_path": str(source_html_path or ""),
        "declarations": [
            {
                "decl_index": index,
                "decl_name": decl.name,
                "kind": decl.kind,
                "is_root": bool(decl.is_root),
                "line_start": decl.line,
                "line_end": decl.line_end,
                "col_start": decl.col_start,
                "col_end": decl.col_end,
                "char_start": decl.char_start,
                "char_end": decl.char_end,
                "byte_start": decl.byte_start,
                "byte_end": decl.byte_end,
                "source_span": dict(decl.source_span),
                "proof_start_line": decl.proof_line,
                "proof_end_line": decl.proof_line_end,
                "proof_char_start": decl.proof_char_start,
                "proof_char_end": decl.proof_char_end,
                "proof_span": dict(decl.proof_span),
                "source_hash": decl.source_hash,
                "href": decl.href,
                "proof_href": decl.proof_href,
                "graph_node_id": decl.graph_node_id,
                "runtime_source_hash_match": decl.runtime_source_hash_match,
            }
            for index, decl in enumerate(decls)
        ],
    }


def render_source_html(problem: str, source: str) -> str:
    rows = []
    for idx, line in enumerate(str(source or "").splitlines(), 1):
        rows.append(
            '<tr id="L{idx}"><td class="ln"><a href="#L{idx}">{idx}</a></td>'
            '<td class="src"><code>{line}</code></td></tr>'.format(
                idx=idx,
                line=html.escape(line),
            )
        )
    return """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Lean Source — {problem}</title>
<style>
  body {{ margin: 0; background: #101418; color: #d7dee6; font: 13px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }}
  header {{ position: sticky; top: 0; padding: 10px 14px; background: #161c22; border-bottom: 1px solid #2a323c; font-family: system-ui, sans-serif; }}
  table {{ border-collapse: collapse; width: 100%; }}
  td {{ vertical-align: top; }}
  .ln {{ width: 1%; min-width: 52px; padding: 0 10px; text-align: right; user-select: none; color: #708090; border-right: 1px solid #26313b; }}
  .ln a {{ color: inherit; text-decoration: none; }}
  .src {{ padding-left: 12px; white-space: pre; }}
  tr:target .ln, tr:target .src {{ background: #243447; }}
  code {{ font: inherit; }}
</style>
</head>
<body>
<header>{problem}</header>
<table>
{rows}
</table>
</body>
</html>
""".format(problem=html.escape(str(problem or "")), rows="\n".join(rows))


_HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Lean Dependency Graph — __PROBLEM__</title>
<style>
  body { margin: 0; font: 13px/1.4 system-ui, sans-serif; background: #101418; color: #e6e6e6; }
  #hud { position: fixed; top: 0; left: 0; right: 0; padding: 10px 16px;
         background: rgba(16,20,24,.92); border-bottom: 1px solid #2a323c; z-index: 2; }
  #hud h1 { font-size: 15px; margin: 0 0 2px; }
  #hud .meta { color: #9aa7b4; font-size: 12px; }
  #hud .axioms { color: #7fd18b; font-size: 12px; }
  #tooltip { position: fixed; max-width: 560px; padding: 8px 10px; background: #1b232c;
             border: 1px solid #33404d; border-radius: 6px; pointer-events: none;
             opacity: 0; z-index: 3; font-size: 12px; }
  #tooltip .name { color: #8ec9ff; font-weight: 600; }
  #tooltip .stmt { color: #c8d2dc; margin-top: 4px; white-space: pre-wrap;
                   font-family: ui-monospace, monospace; font-size: 11px; }
  svg { width: 100vw; height: 100vh; }
  .legend { position: fixed; bottom: 12px; left: 16px; color: #9aa7b4; font-size: 12px; z-index: 2; }
  .legend span { display: inline-block; margin-right: 14px; }
  .legend i { display: inline-block; width: 10px; height: 10px; border-radius: 50%;
              margin-right: 5px; vertical-align: -1px; }
</style>
</head>
<body>
<div id="hud">
  <h1>Lean Dependency Graph — __PROBLEM__</h1>
  <div class="meta">__LOCAL__ local declarations · __EXTERNAL__ external references (syntactic) · __EDGES__ edges</div>
  <div class="axioms">__AXIOMS__</div>
</div>
<div class="legend">
  <span><i style="background:#ffb454"></i>root theorem</span>
  <span><i style="background:#8ec9ff"></i>helper (theorem/lemma)</span>
  <span><i style="background:#c39ef7"></i>def / abbrev</span>
  <span><i style="background:#5a6672"></i>external (Mathlib)</span>
</div>
<div id="tooltip"></div>
<svg></svg>
<script>
const data = __DATA__;
const color = n => n.group === "root" ? "#ffb454"
  : n.group === "external" ? "#5a6672"
  : /def|abbrev|structure|inductive|instance/.test(n.kind) ? "#c39ef7" : "#8ec9ff";
const radius = n => n.group === "external" ? 3.5
  : Math.max(6, Math.min(26, 4 + 2.6 * Math.sqrt(n.proof_length)));
const esc = s => String(s ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
const ns = "http://www.w3.org/2000/svg";
const svg = document.querySelector("svg");
const width = window.innerWidth, height = window.innerHeight;
let view = { x: 0, y: 0, w: width, h: height };
svg.setAttribute("viewBox", `${view.x} ${view.y} ${view.w} ${view.h}`);
const container = document.createElementNS(ns, "g");
svg.appendChild(container);
const nodes = data.nodes.map((n, i) => ({ ...n, index: i, r: radius(n) }));
const byId = new Map(nodes.map(n => [n.id, n]));
const links = data.links.map(l => ({ ...l, sourceNode: byId.get(l.source), targetNode: byId.get(l.target) }))
  .filter(l => l.sourceNode && l.targetNode);
function place() {
  const cx = width / 2, cy = height / 2 + 18;
  const local = nodes.filter(n => n.group !== "external" && n.group !== "root");
  const external = nodes.filter(n => n.group === "external");
  const roots = nodes.filter(n => n.group === "root");
  roots.forEach((n, i) => { n.x = cx + i * 34; n.y = cy; });
  local.forEach((n, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / Math.max(1, local.length);
    const r = Math.max(110, Math.min(width, height) * 0.28);
    n.x = cx + Math.cos(a) * r;
    n.y = cy + Math.sin(a) * r;
  });
  external.forEach((n, i) => {
    const a = i * 2 * Math.PI / Math.max(1, external.length);
    const r = Math.max(180, Math.min(width, height) * 0.43);
    n.x = cx + Math.cos(a) * r;
    n.y = cy + Math.sin(a) * r;
  });
}
function el(name, attrs = {}) {
  const e = document.createElementNS(ns, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  return e;
}
place();
const linkEls = links.map(l => {
  const e = el("line", {
    stroke: l.kind === "external" ? "#232c34" : "#3f4f5f",
    "stroke-width": l.kind === "external" ? "0.5" : "1.4",
    "stroke-opacity": "0.7",
  });
  container.appendChild(e);
  return e;
});
const nodeEls = nodes.map(n => {
  const g = el("g", { cursor: n.href ? "pointer" : "grab" });
  const c = el("circle", {
    r: n.r, fill: color(n),
    stroke: n.group === "root" ? "#fff" : "none", "stroke-width": "1.5",
  });
  g.appendChild(c);
  if (n.group !== "external") {
    const t = el("text", { "font-size": "10", fill: "#aeb9c4", dx: n.r + 3, dy: 3 });
    t.textContent = n.id;
    g.appendChild(t);
  }
  container.appendChild(g);
  return g;
});
const tip = document.querySelector("#tooltip");
function draw() {
  links.forEach((l, i) => {
    linkEls[i].setAttribute("x1", l.sourceNode.x);
    linkEls[i].setAttribute("y1", l.sourceNode.y);
    linkEls[i].setAttribute("x2", l.targetNode.x);
    linkEls[i].setAttribute("y2", l.targetNode.y);
  });
  nodes.forEach((n, i) => nodeEls[i].setAttribute("transform", `translate(${n.x},${n.y})`));
}
function showTip(e, n) {
  const lineRange = n.line_end && n.line_end !== n.line ? `${n.line}-${n.line_end}` : (n.line || "");
  const clickHint = n.href ? " · click to source" : "";
  tip.style.opacity = 1;
  tip.style.left = Math.min(e.clientX + 14, width - 580) + "px";
  tip.style.top = (e.clientY + 12) + "px";
  tip.innerHTML = `<div class="name">${esc(n.id)}</div>
    <div>${esc(n.kind)}${lineRange ? " · lines " + esc(lineRange) : ""} · ${esc(n.proof_length)} line(s)${clickHint}</div>
    <div class="stmt">${esc(n.statement)}</div>`;
}
let drag = null;
nodeEls.forEach((g, i) => {
  const n = nodes[i];
  let moved = false;
  g.addEventListener("pointerdown", e => {
    moved = false;
    drag = { node: n, x: e.clientX, y: e.clientY, ox: n.x, oy: n.y };
    g.setPointerCapture(e.pointerId);
  });
  g.addEventListener("pointermove", e => {
    showTip(e, n);
    if (!drag || drag.node !== n) return;
    const sx = view.w / width, sy = view.h / height;
    n.x = drag.ox + (e.clientX - drag.x) * sx;
    n.y = drag.oy + (e.clientY - drag.y) * sy;
    moved = moved || Math.abs(e.clientX - drag.x) + Math.abs(e.clientY - drag.y) > 3;
    draw();
  });
  g.addEventListener("pointerup", e => {
    if (drag && drag.node === n && n.href && !moved) window.open(n.href, "_blank", "noopener");
    drag = null;
  });
  g.addEventListener("pointerleave", () => { tip.style.opacity = 0; });
});
let pan = null;
svg.addEventListener("pointerdown", e => {
  if (e.target !== svg) return;
  pan = { x: e.clientX, y: e.clientY, vx: view.x, vy: view.y };
  svg.setPointerCapture(e.pointerId);
});
svg.addEventListener("pointermove", e => {
  if (!pan) return;
  view.x = pan.vx - (e.clientX - pan.x) * view.w / width;
  view.y = pan.vy - (e.clientY - pan.y) * view.h / height;
  svg.setAttribute("viewBox", `${view.x} ${view.y} ${view.w} ${view.h}`);
});
svg.addEventListener("pointerup", () => { pan = null; });
svg.addEventListener("wheel", e => {
  e.preventDefault();
  const factor = e.deltaY < 0 ? 0.9 : 1.1;
  const mx = view.x + e.clientX * view.w / width;
  const my = view.y + e.clientY * view.h / height;
  view.w *= factor; view.h *= factor;
  view.x = mx - e.clientX * view.w / width;
  view.y = my - e.clientY * view.h / height;
  svg.setAttribute("viewBox", `${view.x} ${view.y} ${view.w} ${view.h}`);
});
draw();
</script>
</body>
</html>
"""


def _substitute_html_template(values: Dict[str, str]) -> str:
    marker_re = re.compile(r"__(PROBLEM|LOCAL|EXTERNAL|EDGES|AXIOMS|DATA)__")
    return marker_re.sub(lambda match: values[match.group(1)], _HTML_TEMPLATE)


def render_html(payload: Dict) -> str:
    axioms = payload.get("axioms") or []
    audit_ok = payload.get("axiom_audit_ok")
    audit_error = str(payload.get("axiom_audit_error") or "").strip()
    unexpected = list(payload.get("unexpected_axioms") or [])
    nonstandard_axioms = [axiom for axiom in axioms if axiom not in _STANDARD_AXIOMS]
    if axioms and audit_ok:
        axioms_line = "axioms: " + ", ".join(axioms) + " ✓ standard trust base"
    elif audit_ok:
        axioms_line = "axioms: none ✓ standard trust base"
    elif audit_ok is False and unexpected:
        axioms_line = "⚠ TRUST-EXPANDING axioms: " + ", ".join(unexpected)
    elif audit_ok is False and audit_error:
        axioms_line = "⚠ axiom audit failed: " + audit_error
    elif nonstandard_axioms:
        axioms_line = (
            "⚠ TRUST-EXPANDING axioms: "
            + ", ".join(nonstandard_axioms)
            + " (beyond the kernel trust base — e.g. native_decide)"
        )
    else:
        axioms_line = (
            "axioms: (not audited — run "
            "python -m ensemble_prover.extract_solved --audit-existing)"
        )
    # "</" must not appear literally inside the <script> block: a statement
    # containing "</script>" would end the tag and inject markup into the
    # (published) page. "<\/" is identical JSON after JS string parsing.
    embedded = (
        json.dumps(payload, ensure_ascii=False)
        .replace("</", "<\\/")
        .replace("<", "\\u003c")
    )
    return _substitute_html_template(
        {
            "PROBLEM": html.escape(str(payload["problem"])),
            "LOCAL": str(payload["local_declarations"]),
            "EXTERNAL": str(payload["external_references"]),
            "EDGES": str(payload["edges"]),
            "AXIOMS": html.escape(axioms_line),
            "DATA": embedded,
        }
    )


def _write_text_atomic(path: Path, text: str) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(
        prefix=f".{target.name}.",
        suffix=".tmp",
        dir=str(target.parent),
    )
    os.close(fd)
    tmp_path = Path(tmp_name)
    try:
        tmp_path.write_text(text, encoding="utf-8")
        tmp_path.replace(target)
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def _write_bytes_atomic(path: Path, data: bytes) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(
        prefix=f".{target.name}.",
        suffix=".tmp",
        dir=str(target.parent),
    )
    os.close(fd)
    tmp_path = Path(tmp_name)
    try:
        tmp_path.write_bytes(data)
        tmp_path.replace(target)
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def _write_artifact_set_atomic(files: Dict[Path, str]) -> None:
    """Write a related artifact group, restoring prior files on any failure."""

    snapshots: Dict[Path, Tuple[str, bytes]] = {}
    for raw_path in files:
        path = Path(raw_path)
        if path.is_file():
            snapshots[path] = ("file", path.read_bytes())
        elif path.exists():
            snapshots[path] = ("other", b"")
        else:
            snapshots[path] = ("missing", b"")
    try:
        for raw_path, text in files.items():
            _write_text_atomic(Path(raw_path), text)
    except Exception:
        for path, (kind, data) in snapshots.items():
            try:
                if kind == "file":
                    _write_bytes_atomic(path, data)
                elif kind == "missing" and path.exists() and not path.is_dir():
                    path.unlink()
            except Exception:
                pass
        raise


def _load_axiom_audit(solved_dir: Path) -> Dict[str, Dict]:
    report_path = solved_dir / "axiom_audit.json"
    if not report_path.exists():
        return {}
    try:
        rows = json.loads(report_path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    audit: Dict[str, Dict] = {}
    for row in rows:
        if row.get("file"):
            audit[str(row.get("file") or "")] = {
                "ok": bool(row.get("ok")),
                "axioms": list(row.get("axioms") or []),
                "unexpected": list(row.get("unexpected_axioms") or []),
                "error": str(row.get("error") or "").strip(),
                "source_hash": str(
                    row.get("source_hash") or row.get("file_hash") or ""
                ).strip(),
            }
    return audit


def _render_artifacts(
    *,
    source: str,
    lean_path: Path,
    source_html_name: str,
    include_external: bool,
    axioms: Optional[List[str]],
    audit_ok: Optional[bool],
    audit_error: str,
    unexpected_axioms: Optional[List[str]],
    proof_graph_record: Optional[Dict[str, Any]],
    artifact_path: str,
) -> Optional[Dict[str, Any]]:
    source_hash = _text_hash(source)
    decls = parse_declarations(
        source,
        root_name="",
        source_html_name=source_html_name,
    )
    if not decls:
        return None
    root_name = _infer_root_name_for_decls(lean_path.stem, decls)
    for decl in decls:
        decl.is_root = decl.name == root_name
    build_graph(decls)
    payload = graph_payload(
        lean_path.stem,
        decls,
        include_external=include_external,
        axioms=axioms,
        audit_ok=audit_ok,
        audit_error=audit_error,
        unexpected_axioms=unexpected_axioms,
        artifact_path=artifact_path,
        source_html_path=source_html_name,
        proof_graph_record=proof_graph_record,
        root_name=root_name,
    )
    payload["source_hash"] = source_hash
    source_map = source_map_payload(
        lean_path.stem,
        decls,
        artifact_path=artifact_path,
        source_html_path=source_html_name,
    )
    source_map["source_hash"] = source_hash
    return {
        "payload": payload,
        "source_map": source_map,
        "graph_json": json.dumps(payload, indent=2, ensure_ascii=False),
        "source_map_json": json.dumps(source_map, indent=2, ensure_ascii=False),
        "graph_html": render_html(payload),
        "source_html": render_source_html(lean_path.stem, source),
    }


def export_file(
    lean_path: Path,
    out_dir: Path,
    *,
    include_external: bool = True,
    axioms: Optional[List[str]] = None,
    audit_ok: Optional[bool] = None,
    audit_error: str = "",
    unexpected_axioms: Optional[List[str]] = None,
    proof_graph_record: Optional[Dict[str, Any]] = None,
) -> Optional[Dict]:
    source = lean_path.read_text(encoding="utf-8")
    source_html_name = f"{lean_path.stem}.source.html"
    artifacts = _render_artifacts(
        source=source,
        lean_path=lean_path,
        source_html_name=source_html_name,
        include_external=include_external,
        axioms=axioms,
        audit_ok=audit_ok,
        audit_error=audit_error,
        unexpected_axioms=unexpected_axioms,
        proof_graph_record=proof_graph_record,
        artifact_path=str(lean_path),
    )
    if artifacts is None:
        return None
    artifact_files = {
        out_dir / f"{lean_path.stem}.json": str(artifacts["graph_json"]),
        out_dir / f"{lean_path.stem}.source_map.json": str(
            artifacts["source_map_json"]
        ),
        out_dir / f"{lean_path.stem}.html": str(artifacts["graph_html"]),
        out_dir / source_html_name: str(artifacts["source_html"]),
    }
    _write_artifact_set_atomic(artifact_files)
    return artifacts["payload"]


def _render_index(rows: List[Tuple[str, Dict]], out_dir: Path) -> None:
    def _axiom_cell(payload: Dict) -> str:
        axioms = payload.get("axioms") or []
        if payload.get("axiom_audit_ok"):
            return "✓ standard"
        if payload.get("axiom_audit_ok") is False:
            unexpected = list(payload.get("unexpected_axioms") or [])
            if unexpected:
                return "⚠ " + ", ".join(unexpected)
            error = str(payload.get("axiom_audit_error") or "").strip()
            if error:
                return "⚠ audit failed"
        if not axioms:
            return "—"
        nonstandard = [axiom for axiom in axioms if axiom not in _STANDARD_AXIOMS]
        if not nonstandard:
            return "—"
        return "⚠ " + ", ".join(nonstandard)

    items = "\n".join(
        f'<tr><td><a href="{quote(stem + ".html")}">'
        f"{html.escape(stem)}</a></td>"
        f"<td>{payload['local_declarations']}</td>"
        f"<td>{payload['external_references']}</td>"
        f"<td>{payload['edges']}</td>"
        f"<td>{html.escape(_axiom_cell(payload))}</td></tr>"
        for stem, payload in rows
    )
    page_html = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>Solved-proof dependency graphs</title>
<style>
 body {{ font: 14px system-ui, sans-serif; background: #101418; color: #e6e6e6; padding: 24px; }}
 a {{ color: #8ec9ff; }} table {{ border-collapse: collapse; }}
 td, th {{ padding: 5px 14px; border-bottom: 1px solid #2a323c; text-align: left; }}
</style></head><body>
<h1>Solved-proof dependency graphs ({len(rows)})</h1>
<table><tr><th>problem</th><th>local decls</th><th>external refs</th><th>edges</th><th>axioms</th></tr>
{items}
</table></body></html>
"""
    (out_dir / "index.html").write_text(page_html, encoding="utf-8")


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Export dependency-graph artifacts for solved Lean proofs."
    )
    parser.add_argument("--solved-dir", default=str(SOLVED_DIR))
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Output directory (default: <solved-dir>/depgraphs).",
    )
    parser.add_argument(
        "--problem", default=None, help="Only files whose stem starts with this."
    )
    parser.add_argument("--file", default=None, help="Export one specific .lean file.")
    parser.add_argument(
        "--no-external",
        action="store_true",
        help="Omit the syntactic external-reference nodes.",
    )
    args = parser.parse_args(list(argv or []))

    solved_dir = Path(args.solved_dir)
    out_dir = Path(args.out_dir) if args.out_dir else solved_dir / "depgraphs"
    audit = _load_axiom_audit(solved_dir)

    if args.file:
        files = [Path(args.file)]
    else:
        files = sorted(
            path
            for path in solved_dir.glob("*.lean")
            if not path.name.startswith(".")
            and (not args.problem or path.stem.startswith(args.problem))
        )
    if not files:
        print("No .lean files matched.")
        return 1

    rows: List[Tuple[str, Dict]] = []
    for lean_path in files:
        # The audit report is keyed by basename and describes the files
        # INSIDE solved_dir. Never attach its trust badge to an outside
        # --file path that merely shares a basename with an audited export.
        try:
            in_solved_dir = lean_path.resolve().parent == solved_dir.resolve()
        except Exception:
            in_solved_dir = False
        file_audit = (audit.get(lean_path.name) or {}) if in_solved_dir else {}
        if file_audit:
            current_hash = _text_hash(lean_path.read_text(encoding="utf-8"))
            if str(file_audit.get("source_hash") or "") != current_hash:
                file_audit = {}
        payload = export_file(
            lean_path,
            out_dir,
            include_external=not bool(args.no_external),
            axioms=file_audit.get("axioms"),
            audit_ok=file_audit.get("ok"),
            audit_error=str(file_audit.get("error") or ""),
            unexpected_axioms=list(file_audit.get("unexpected") or []),
        )
        if payload is None:
            print(f"  ! {lean_path.name}: no declarations found, skipped")
            continue
        rows.append((lean_path.stem, payload))
        print(
            f"  ✓ {lean_path.stem}: {payload['local_declarations']} decls, "
            f"{payload['external_references']} external refs, "
            f"{payload['edges']} edges"
        )
    if not args.file:
        _render_index(rows, out_dir)
    print(f"\nWrote {len(rows)} graph artifact(s) to {out_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
