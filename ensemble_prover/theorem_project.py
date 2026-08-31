"""Resolve, validate, and snapshot generic Lean theorem projects."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any, Iterable, Mapping, Optional, Sequence

from .lean_decl_parser import find_decl_header_end
from .utils import _first_top_level_colon_after, has_sorry_or_admit


THEOREM_PROJECT_SCHEMA_VERSION = 2
GENERIC_ADAPTER_ID = "generic"
PUTNAMBENCH_ADAPTER_ID = "putnam_bench"

_IDENT_COMPONENT = r"(?:«[^»\r\n]+»|(?:[^\W\d]|_)[\w']*)"
_DOTTED_IDENT = rf"(?:_root_\.)?{_IDENT_COMPONENT}(?:\.{_IDENT_COMPONENT})*"
_ATTR = r"(?:@\[[^\]]*\]\s*)"
_SCOPED_LINE_COMMAND = (
    r"(?:set_option|include|omit|open|attribute|universe|variable|local|scoped|"
    r"#[A-Za-z_][A-Za-z0-9_']*)"
)
_SCOPED_COMMAND = r"(?:[A-Za-z_][A-Za-z0-9_']*|#[A-Za-z_][A-Za-z0-9_']*)"
_COMMAND_KEYWORD = (
    r"(?:theorem|lemma|def|abbrev|instance|namespace|section|end|mutual|"
    r"set_option|include|omit|open|attribute|universe|variable|local|scoped|"
    r"export|syntax|macro|macro_rules|elab|elab_rules|inductive|structure|"
    r"class|axiom|constant|opaque|example|notation|prefix|postfix|infix|"
    r"infixl|infixr)"
)
_DECL_RE = re.compile(
    rf"(?<!\S)(?P<scoped>(?:{_SCOPED_COMMAND}"
    rf"(?:[ \t]+[^\r\n]+?)?[ \t]+in[ \t]+)*)"
    rf"(?P<prefix>[ \t]*(?:{_ATTR})*"
    rf"(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)"
    rf"(?P<kind>theorem|lemma|def|abbrev|instance)\s+(?P<name>{_DOTTED_IDENT})"
    rf"(?P<universe_suffix>\.\{{[^}}\r\n]+\}})?(?=\s|:|\(|\{{|\[)",
    flags=re.UNICODE,
)
_NAMESPACE_RE = re.compile(
    rf"(?<!\S)namespace[ \t]+(?P<name>{_DOTTED_IDENT})(?=\s|$)",
    flags=re.UNICODE,
)
_SECTION_RE = re.compile(
    rf"(?<!\S)(?:(?:{_ATTR})|(?:public|protected)\s+)*section"
    rf"(?:[ \t]+(?P<name>(?!{_COMMAND_KEYWORD}\b){_DOTTED_IDENT}))?"
    rf"(?=\s|$)",
    flags=re.UNICODE,
)
_END_RE = re.compile(
    rf"(?<!\S)end(?:[ \t]+(?P<name>(?!{_COMMAND_KEYWORD}\b){_DOTTED_IDENT}))?"
    rf"(?=\s|$)",
    flags=re.UNICODE,
)
_MUTUAL_RE = re.compile(r"(?<!\S)mutual\b")
_TARGET_CONTEXT_MARKER = "-- ensemble-theorem-target-context: "


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _canonical_json(value: Mapping[str, Any]) -> bytes:
    return json.dumps(
        dict(value),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _mask_noncode(text: str) -> str:
    """Mask comments and literals while preserving source offsets/newlines."""

    src = str(text or "")
    out = list(src)
    n = len(src)
    i = 0

    def mask(start: int, end: int) -> None:
        for pos in range(start, min(end, n)):
            if out[pos] not in {"\n", "\r"}:
                out[pos] = " "

    while i < n:
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
        raw_match = re.match(r"r(?P<hashes>#+)?\"", src[i:])
        if raw_match is not None and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_")):
            hashes = raw_match.group("hashes") or ""
            close = '"' + hashes
            body_start = i + raw_match.end()
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
                if src.startswith("--", end):
                    newline = src.find("\n", end + 2)
                    end = n if newline < 0 else newline
                    continue
                raw_match = re.match(r"r(?P<hashes>#+)?\"", src[end:])
                if raw_match is not None and (
                    end == 0
                    or not (src[end - 1].isalnum() or src[end - 1] == "_")
                ):
                    hashes = raw_match.group("hashes") or ""
                    close = '"' + hashes
                    body_start = end + raw_match.end()
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


def _mask_attribute_contents(text: str) -> str:
    """Mask balanced ``@[...]`` payloads while retaining their outer shape.

    Lean attributes may contain nested list syntax.  A declaration-prefix
    regex cannot distinguish the inner ``]`` from the attribute terminator;
    doing the balancing once here keeps the source offsets stable and lets the
    structural scanner consume the resulting ``@[   ]`` prefix safely.
    """

    source = str(text or "")
    out = list(source)
    cursor = 0
    while cursor < len(source) - 1:
        if not source.startswith("@[", cursor):
            cursor += 1
            continue
        depth = 1
        end = cursor + 2
        while end < len(source) and depth:
            if source[end] == "[":
                depth += 1
            elif source[end] == "]":
                depth -= 1
            end += 1
        if depth:
            # Leave malformed input visible to the normal scanner.  It will
            # fail to resolve a target instead of fabricating a declaration.
            cursor += 2
            continue
        for index in range(cursor + 2, end - 1):
            if out[index] not in {"\n", "\r"}:
                out[index] = " "
        cursor = end
    return "".join(out)


def _strip_root_prefix(name: str) -> str:
    clean = str(name or "").strip()
    return clean[len("_root_.") :] if clean.startswith("_root_.") else clean


def _name_final_component(name: str) -> str:
    clean = _strip_root_prefix(name)
    depth = 0
    last_dot = -1
    for index, char in enumerate(clean):
        if char == "«":
            depth += 1
        elif char == "»" and depth:
            depth -= 1
        elif char == "." and depth == 0:
            last_dot = index
    return clean[last_dot + 1 :]


def _qualified_name(namespace: Sequence[str], source_name: str) -> str:
    source = str(source_name or "").strip()
    if source.startswith("_root_."):
        return _strip_root_prefix(source)
    prefix = ".".join(str(item).strip() for item in namespace if str(item).strip())
    return f"{prefix}.{source}" if prefix else source


@dataclass(frozen=True)
class LeanTheoremDeclaration:
    kind: str
    source_name: str
    canonical_name: str
    namespace: tuple[str, ...]
    declaration_start: int
    keyword_start: int
    name_start: int
    name_end: int
    header_end: int
    statement_type: str
    docstring: str = ""
    docstring_start: Optional[int] = None
    universe_suffix: str = ""
    private: bool = False
    public: bool = False
    scoped_prefix: str = ""
    command_prefix: str = ""


def _extract_docstring_before(text: str, start: int) -> tuple[Optional[int], str]:
    prefix = str(text or "")[: max(0, int(start))]
    trimmed = prefix.rstrip()
    if not trimmed.endswith("-/"):
        return None, ""
    close_at = len(trimmed) - 2
    depth = 1
    cursor = close_at
    begin: Optional[int] = None
    while cursor > 0:
        nested_close = trimmed.rfind("-/", 0, cursor)
        nested_open = trimmed.rfind("/-", 0, cursor)
        if nested_close > nested_open:
            depth += 1
            cursor = nested_close
            continue
        if nested_open < 0:
            break
        depth -= 1
        if depth == 0:
            begin = nested_open
            break
        cursor = nested_open
    if begin is None or not trimmed.startswith("/--", begin):
        return None, ""
    return begin, trimmed[begin:].strip()


def _statement_type(
    text: str,
    *,
    keyword_start: int,
    name_end: int,
    header_end: int,
    display_name: str,
) -> str:
    header = text[keyword_start:header_end]
    name_end_relative = name_end - keyword_start
    colon = _first_top_level_colon_after(header, name_end_relative)
    if colon < 0:
        raise ValueError(f"header for {display_name} has no top-level ':'")
    binder_part = header[name_end_relative:colon].strip()
    type_part = header[colon + 1 :].strip()
    if type_part.endswith(":="):
        type_part = type_part[:-2].strip()
    if not type_part:
        raise ValueError(f"header for {display_name} has an empty theorem type")
    return f"∀ {binder_part}, {type_part}" if binder_part else type_part


def _active_command_scopes(
    text: str, end: int
) -> tuple[tuple[str, str, int, int], ...]:
    """Return command scopes active immediately before ``end``."""

    masked = _mask_attribute_contents(_mask_noncode(str(text or "")[:end]))
    events: list[tuple[int, str, re.Match[str]]] = []
    for kind, pattern in (
        ("namespace", _NAMESPACE_RE),
        ("section", _SECTION_RE),
        ("mutual", _MUTUAL_RE),
        ("end", _END_RE),
    ):
        events.extend((match.start(), kind, match) for match in pattern.finditer(masked))
    events.sort(key=lambda item: item[0])
    scopes: list[tuple[str, str, int, int]] = []
    for _offset, kind, match in events:
        if kind in {"namespace", "section"}:
            scopes.append(
                (
                    kind,
                    str(match.group("name") or "").strip(),
                    match.start(),
                    match.end(),
                )
            )
        elif kind == "mutual":
            scopes.append((kind, "", match.start(), match.end()))
        elif scopes:
            requested = str(match.group("name") or "").strip()
            if not requested:
                scopes.pop()
            else:
                for index in range(len(scopes) - 1, -1, -1):
                    if scopes[index][1] == requested:
                        del scopes[index:]
                        break
    return tuple(scopes)


def _active_command_scope_closers(text: str, end: int) -> tuple[str, ...]:
    """Return the ``end`` commands needed after an isolated declaration."""

    return tuple(
        f"end {name}" if name else "end"
        for _kind, name, _start, _finish in reversed(
            _active_command_scopes(text, end)
        )
        if _kind != "mutual"
    )


def _remove_active_mutual_openers(text: str, end: int) -> str:
    """Hold out the target's active mutual group from standalone context."""

    chars = list(str(text or ""))
    for kind, _name, start, _finish in _active_command_scopes(text, end):
        if kind != "mutual":
            continue
        # Co-mutual declarations are not sound upstream premises: their bodies
        # may refer back to the selected target. Remove the whole active group
        # prefix, not merely its opener, while preserving line structure.
        for index in range(start, min(end, len(chars))):
            if chars[index] not in "\r\n":
                chars[index] = " "
    return "".join(chars)


def _multiline_scoped_prefix_before(
    text: str,
    keyword_start: int,
) -> tuple[int, str]:
    """Recover target-only command wrappers split across physical lines."""

    source = str(text or "")
    masked = _mask_attribute_contents(_mask_noncode(source[:keyword_start]))
    command_re = re.compile(
        rf"(?m)^[ \t]*(?:{_SCOPED_LINE_COMMAND}\b|"
        rf"{_SCOPED_COMMAND}\b[^\r\n]*\bin\b)"
    )
    current = len(masked)
    earliest = current
    closest_in_end: Optional[int] = None
    declaration_tail_re = re.compile(
        r"(?:\s|@\[[^\]]*\]|\b(?:public|private|protected|"
        r"noncomputable|unsafe|partial)\b)*\Z"
    )
    recognized = {
        "set_option", "include", "omit", "open", "attribute", "universe",
        "variable", "local", "scoped",
    }

    def valid_candidate(
        candidate: re.Match[str],
    ) -> Optional[tuple[int, tuple[tuple[str, str], ...]]]:
        segment = masked[candidate.start() : current]
        for in_match in reversed(list(re.finditer(r"\bin\b", segment))):
            in_end = candidate.start() + in_match.end()
            if declaration_tail_re.fullmatch(masked[in_end:current]) is None:
                continue
            parsed = _split_scoped_command_wrappers(
                source[candidate.start() : in_end]
            )
            if parsed:
                return in_end, parsed
        return None

    while current > 0:
        candidates = list(command_re.finditer(masked, 0, current))
        if not candidates:
            break
        candidate = candidates[-1]
        valid = valid_candidate(candidate)
        # A scalar continuation such as `false in` is identifier-shaped but
        # belongs to a preceding recognized `set_option` command. Prefer that
        # complete structural parse over inventing a `false` command wrapper.
        if valid is not None and valid[1][0][0] not in recognized and len(candidates) > 1:
            previous = candidates[-2]
            previous_valid = valid_candidate(previous)
            if (
                previous_valid is not None
                and previous_valid[1][0][0] in recognized
            ):
                candidate = previous
                valid = previous_valid
        if valid is None:
            break
        in_end, _parsed = valid
        earliest = candidate.start()
        if closest_in_end is None:
            closest_in_end = in_end
        current = candidate.start()
    if closest_in_end is None:
        return keyword_start, ""
    return earliest, source[earliest:closest_in_end].strip()


def theorem_declaration_context(
    text: str,
    declaration: LeanTheoremDeclaration,
) -> tuple[int, str]:
    """Return the reusable-prefix cut and target-only command wrapper."""

    preamble_end = (
        declaration.docstring_start
        if declaration.docstring_start is not None
        else declaration.declaration_start
    )
    wrapper_start, multiline_scoped_prefix = _multiline_scoped_prefix_before(
        text,
        declaration.keyword_start,
    )
    # The backward recovery can include outer multiline wrappers plus an inner
    # same-line wrapper captured by _DECL_RE. Prefer that complete chain.
    target_scoped_prefix = (
        multiline_scoped_prefix or declaration.scoped_prefix
    ).strip()
    active_mutuals = tuple(
        scope
        for scope in _active_command_scopes(text, declaration.declaration_start)
        if scope[0] == "mutual"
    )
    if active_mutuals:
        mutual_start = active_mutuals[-1][2]
        mutual_wrapper_start, mutual_wrapper = _multiline_scoped_prefix_before(
            text,
            mutual_start,
        )
        if mutual_wrapper:
            target_scoped_prefix = "\n".join(
                part
                for part in (mutual_wrapper.strip(), target_scoped_prefix)
                if part
            )
            wrapper_start = min(wrapper_start, mutual_wrapper_start)
    if target_scoped_prefix:
        wrapper_start = min(wrapper_start, declaration.declaration_start)
        preamble_end = min(preamble_end, wrapper_start)
    return preamble_end, target_scoped_prefix


def _split_scoped_command_wrappers(prefix: str) -> tuple[tuple[str, str], ...]:
    """Split a recovered ``... in`` wrapper chain without losing layout."""

    source = str(prefix or "")
    masked = _mask_noncode(source)
    wrappers: list[tuple[str, str]] = []
    cursor = 0
    length = len(masked)
    while cursor < length:
        while cursor < length and masked[cursor].isspace():
            cursor += 1
        if cursor >= length:
            break
        command = re.match(_SCOPED_COMMAND, masked[cursor:])
        if command is None:
            return ()
        kind = command.group(0)
        scan = cursor + command.end()
        stack: list[str] = []
        quote_depth = 0
        end: Optional[int] = None
        pairs = {"(": ")", "[": "]", "{": "}"}
        while scan < length:
            char = masked[scan]
            if char == "«":
                quote_depth += 1
            elif char == "»" and quote_depth:
                quote_depth -= 1
            elif not quote_depth and char in pairs:
                stack.append(pairs[char])
            elif not quote_depth and stack and char == stack[-1]:
                stack.pop()
            elif (
                not quote_depth
                and not stack
                and masked.startswith("in", scan)
                and (scan == 0 or not (masked[scan - 1].isalnum() or masked[scan - 1] in "_'") )
                and (
                    scan + 2 >= length
                    or not (masked[scan + 2].isalnum() or masked[scan + 2] in "_'")
                )
            ):
                end = scan + 2
                break
            scan += 1
        if end is None:
            return ()
        wrappers.append((kind, source[cursor:end].strip()))
        cursor = end
    return tuple(wrappers)


def theorem_proof_scoped_prefix(prefix: str) -> str:
    """Return wrappers safe around a fully elaborated target type."""

    wrappers = _split_scoped_command_wrappers(prefix)
    if not wrappers and str(prefix or "").strip():
        # Fail closed: unknown/unparsed source context remains available to the
        # exact declaration probe but must not mutate the canonical type.
        return ""
    proof_context_commands = {"open", "set_option", "attribute"}
    return "\n".join(
        command
        for kind, command in wrappers
        if kind in proof_context_commands
    )


def theorem_probe_scoped_prefix(prefix: str) -> str:
    """Return type-relevant wrappers safe around a synthetic proof stub."""

    wrappers = _split_scoped_command_wrappers(prefix)
    if not wrappers and str(prefix or "").strip():
        return ""
    return "\n".join(
        command
        for kind, command in wrappers
        if kind not in {"#guard_msgs", "#min_imports"}
        and not (
            kind == "set_option"
            and re.match(r"set_option\s+warningAsError\b", command) is not None
        )
    )


def encode_theorem_target_context(
    preamble: str,
    *,
    proof_scoped_prefix: str = "",
    omit_variables: Sequence[str] = (),
) -> str:
    """Attach immutable per-request root context as an ignored Lean comment."""

    clean, _prefix, _variables = decode_theorem_target_context(preamble)
    payload = json.dumps(
        {
            "proof_scoped_prefix": str(proof_scoped_prefix or "").strip(),
            "omit_variables": [
                str(item).strip() for item in omit_variables if str(item).strip()
            ],
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    separator = "" if not clean or clean.endswith("\n") else "\n"
    return f"{clean}{separator}{_TARGET_CONTEXT_MARKER}{payload}\n"


def decode_theorem_target_context(
    preamble: str,
) -> tuple[str, str, tuple[str, ...]]:
    """Remove and decode the canonical target-context marker."""

    source = str(preamble or "")
    payload: Mapping[str, Any] = {}
    retained: list[str] = []
    for line in source.splitlines(keepends=True):
        stripped = line.strip()
        if not stripped.startswith(_TARGET_CONTEXT_MARKER):
            retained.append(line)
            continue
        try:
            candidate = json.loads(stripped[len(_TARGET_CONTEXT_MARKER) :])
        except (json.JSONDecodeError, TypeError):
            continue
        if isinstance(candidate, Mapping):
            payload = candidate
    variables = tuple(
        dict.fromkeys(
            str(item).strip()
            for item in payload.get("omit_variables", ())
            if str(item).strip()
        )
    )
    return (
        "".join(retained),
        str(payload.get("proof_scoped_prefix") or "").strip(),
        variables,
    )


def has_theorem_target_context(preamble: str) -> bool:
    """Whether a checker preamble carries canonical request-bound context."""

    return _TARGET_CONTEXT_MARKER in str(preamble or "")


def scan_lean_declarations(text: str) -> tuple[LeanTheoremDeclaration, ...]:
    """Return explicitly typed declarations outside comments and literals."""

    source = str(text or "")
    masked = _mask_attribute_contents(_mask_noncode(source))
    events: list[tuple[int, str, re.Match[str]]] = []
    for kind, pattern in (
        ("namespace", _NAMESPACE_RE),
        ("section", _SECTION_RE),
        ("mutual", _MUTUAL_RE),
        ("end", _END_RE),
        ("declaration", _DECL_RE),
    ):
        events.extend((match.start(), kind, match) for match in pattern.finditer(masked))
    events.sort(key=lambda item: (item[0], item[1] != "declaration"))

    scopes: list[tuple[str, str]] = []
    declarations: list[LeanTheoremDeclaration] = []
    for _, event_kind, match in events:
        if event_kind == "namespace":
            scopes.append(("namespace", str(match.group("name") or "").strip()))
            continue
        if event_kind == "section":
            scopes.append(("section", str(match.group("name") or "").strip()))
            continue
        if event_kind == "mutual":
            scopes.append(("mutual", ""))
            continue
        if event_kind == "end":
            if not scopes:
                continue
            requested = str(match.group("name") or "").strip()
            if not requested:
                scopes.pop()
                continue
            for index in range(len(scopes) - 1, -1, -1):
                frame_name = scopes[index][1]
                if frame_name and (
                    frame_name == requested or frame_name.endswith("." + requested)
                ):
                    del scopes[index:]
                    break
            continue

        kind = str(match.group("kind") or "")
        source_name = str(match.group("name") or "").strip()
        keyword_start = match.start("kind")
        name_start = match.start("name")
        universe_suffix = str(match.group("universe_suffix") or "")
        name_end = (
            match.end("universe_suffix") if universe_suffix else match.end("name")
        )
        header_end = find_decl_header_end(
            source,
            name_end,
            allow_where=True,
            allow_equations=kind in {"theorem", "lemma"},
        )
        if header_end is None:
            raise ValueError(f"failed to find declaration terminator for {source_name}")
        namespace = tuple(
            frame_name
            for frame_kind, frame_name in scopes
            if frame_kind == "namespace" and frame_name
        )
        canonical = _qualified_name(namespace, source_name)
        docstring_start, docstring = _extract_docstring_before(source, match.start())
        if not docstring:
            inner_docstring_start, inner_docstring = _extract_docstring_before(
                source,
                keyword_start,
            )
            if inner_docstring:
                # A doc comment may live inside ``set_option ... in``. It is
                # useful description text, but cannot independently mark the
                # preamble cut: retaining the wrapper prefix would leave an
                # incomplete command. Cut at the whole declaration instead.
                docstring = inner_docstring
                docstring_start = (
                    inner_docstring_start
                    if inner_docstring_start is not None
                    and inner_docstring_start < match.start()
                    else None
                )
        try:
            statement_type = _statement_type(
                source,
                keyword_start=keyword_start,
                name_end=name_end,
                header_end=header_end,
                display_name=canonical,
            )
        except ValueError:
            if kind in {"theorem", "lemma"}:
                raise
            # Inferred ``def foo := ...`` declarations have no searchable
            # declared type at the source boundary.
            continue
        declarations.append(
            LeanTheoremDeclaration(
                kind=kind,
                source_name=source_name,
                canonical_name=canonical,
                namespace=namespace,
                declaration_start=match.start(),
                keyword_start=keyword_start,
                name_start=name_start,
                name_end=name_end,
                header_end=header_end,
                statement_type=statement_type,
                docstring=docstring,
                docstring_start=docstring_start,
                universe_suffix=universe_suffix,
                private=bool(
                    re.search(r"\bprivate\b", str(match.group("prefix") or ""))
                ),
                public=bool(
                    re.search(r"\bpublic\b", str(match.group("prefix") or ""))
                ),
                scoped_prefix=str(match.group("scoped") or "").strip(),
                command_prefix=source[
                    match.start("prefix") : match.start("kind")
                ],
            )
        )
    return tuple(declarations)


def scan_lean_theorems(text: str) -> tuple[LeanTheoremDeclaration, ...]:
    """Return source-ordered theorem/lemma declarations only."""

    return tuple(
        declaration
        for declaration in scan_lean_declarations(text)
        if declaration.kind in {"theorem", "lemma"}
    )


def select_lean_theorem(
    declarations: Sequence[LeanTheoremDeclaration],
    theorem_name: str,
) -> LeanTheoremDeclaration:
    requested = _strip_root_prefix(theorem_name)
    if not requested:
        raise ValueError("theorem name is required")
    exact = [item for item in declarations if item.canonical_name == requested]
    if len(exact) == 1:
        return exact[0]
    if len(exact) > 1:
        raise ValueError(f"duplicate theorem declaration for {requested!r}")
    short_matches = [
        item
        for item in declarations
        if item.source_name == requested
        or _name_final_component(item.canonical_name) == requested
    ]
    if len(short_matches) == 1 and _name_final_component(requested) == requested:
        return short_matches[0]
    if short_matches:
        candidates = ", ".join(sorted(item.canonical_name for item in short_matches))
        raise ValueError(
            f"ambiguous theorem name {requested!r}; use one of: {candidates}"
        )
    available = ", ".join(item.canonical_name for item in declarations[:12])
    suffix = f"; available declarations: {available}" if available else ""
    raise ValueError(f"theorem {requested!r} was not found{suffix}")


def normalize_imports(imports: Iterable[str]) -> tuple[str, ...]:
    normalized: list[str] = []
    for raw in imports:
        value = str(raw or "").strip()
        if value.startswith("import "):
            value = value[len("import ") :].strip()
        if (
            not value
            or value.startswith("_root_.")
            or not is_valid_lean_qualified_name(value)
        ):
            raise ValueError(f"invalid Lean import module: {raw!r}")
        if value not in normalized:
            normalized.append(value)
    return tuple(normalized)


def scan_lean_imports(text: str) -> tuple[str, ...]:
    source = str(text or "")
    imports: list[str] = []
    for line in _mask_noncode(source).splitlines():
        match = re.fullmatch(
            r"\s*(?:public\s+)?import\s+(.+?)\s*",
            line,
        )
        if match is None:
            continue
        module = str(match.group(1) or "").strip()
        if is_valid_lean_qualified_name(module) and module not in imports:
            imports.append(module)
    return tuple(imports)


def split_lean_import_header(text: str) -> tuple[str, str]:
    """Split leading prelude/module/import commands from declaration content."""

    source = str(text or "")
    lines = source.splitlines()
    masked_lines = _mask_noncode(source).splitlines()
    end = 0
    for index, masked_line in enumerate(masked_lines):
        stripped = masked_line.strip()
        if (
            not stripped
            or stripped == "prelude"
            or stripped == "module"
            or stripped.startswith("module ")
            or re.fullmatch(r"(?:public\s+)?import\s+.+", stripped) is not None
        ):
            end = index + 1
            continue
        break
    return "\n".join(lines[:end]), "\n".join(lines[end:])


def merge_imports(preamble: str, imports: Sequence[str]) -> str:
    additions = normalize_imports(imports)
    source = str(preamble or "")
    if not additions:
        return source
    lines = source.splitlines()
    masked_lines = _mask_noncode(source).splitlines()
    existing: list[str] = []
    header_prefix_end = 0
    last_import_end: Optional[int] = None
    for index, masked_line in enumerate(masked_lines):
        stripped = masked_line.strip()
        if (
            not stripped
            or stripped == "prelude"
            or stripped == "module"
            or stripped.startswith("module ")
        ):
            if last_import_end is None:
                header_prefix_end = index + 1
            continue
        match = re.fullmatch(r"(?:public\s+)?import\s+(.+?)\s*", stripped)
        if match is None:
            break
        module = str(match.group(1) or "").strip()
        if module and module not in existing:
            existing.append(module)
        last_import_end = index + 1
    new_lines = [f"import {module}" for module in additions if module not in existing]
    if not new_lines:
        return source
    insert_at = last_import_end if last_import_end is not None else header_prefix_end
    lines[insert_at:insert_at] = new_lines
    trailing_newline = source.endswith(("\n", "\r"))
    merged = "\n".join(lines)
    return merged + ("\n" if trailing_newline else "")


def theorem_reusable_preamble(
    text: str,
    declaration: LeanTheoremDeclaration,
    imports: Sequence[str] = (),
) -> tuple[str, str]:
    """Build the target-independent prefix and return its root wrapper."""

    preamble_end, target_scoped_prefix = theorem_declaration_context(
        text,
        declaration,
    )
    preamble = _remove_active_mutual_openers(
        str(text or "")[:preamble_end],
        declaration.declaration_start,
    )
    return merge_imports(preamble, imports), target_scoped_prefix


def active_include_variables(text: str, end: int) -> tuple[str, ...]:
    """Return section variables persistently included at the target boundary."""

    masked = _mask_attribute_contents(_mask_noncode(str(text or "")[:end]))
    events: list[tuple[int, str, Any]] = []
    for kind, pattern in (
        ("namespace", _NAMESPACE_RE),
        ("section", _SECTION_RE),
        ("mutual", _MUTUAL_RE),
        ("end", _END_RE),
    ):
        events.extend((match.start(), kind, match) for match in pattern.finditer(masked))
    lines = masked.splitlines(keepends=True)
    offsets: list[int] = []
    cursor = 0
    for line in lines:
        offsets.append(cursor)
        cursor += len(line)
    include_head_re = re.compile(
        r"^(?P<indent>[ \t]*)(?P<kind>include|omit)\b(?P<names>[^\r\n]*)"
    )
    for index, line in enumerate(lines):
        match = include_head_re.match(line)
        if match is None:
            continue
        scan = offsets[index] + match.start("names")
        name_parts: list[str] = []
        command_words = {
            "theorem", "lemma", "def", "abbrev", "instance", "namespace",
            "section", "end", "mutual", "set_option", "include", "omit",
            "open", "attribute", "universe", "variable",
            "public", "private", "protected", "noncomputable", "unsafe",
            "partial", "local", "scoped", "export", "syntax", "macro",
            "macro_rules", "elab", "elab_rules", "inductive", "structure",
            "class", "axiom", "constant", "opaque", "example", "notation",
            "prefix", "postfix", "infix", "infixl", "infixr",
        }
        while scan < len(masked):
            while scan < len(masked) and masked[scan].isspace():
                scan += 1
            token = re.match(_IDENT_COMPONENT, masked[scan:], flags=re.UNICODE)
            if token is None:
                break
            value = token.group(0)
            if value == "in":
                name_parts.append("in")
                break
            if value in command_words:
                break
            name_parts.append(value)
            scan += token.end()
        events.append(
            (
                offsets[index],
                "include_state",
                (
                    str(match.group("kind") or ""),
                    " ".join(part for part in name_parts if part),
                ),
            )
        )
    events.sort(key=lambda item: item[0])
    included: list[str] = []
    scopes: list[tuple[str, str, tuple[str, ...]]] = []
    for _offset, kind, match in events:
        if kind in {"namespace", "section", "mutual"}:
            name = (
                str(match.groupdict().get("name") or "").strip()
                if kind != "mutual"
                else ""
            )
            scopes.append((kind, name, tuple(included)))
            continue
        if kind == "end":
            if not scopes:
                continue
            requested = str(match.group("name") or "").strip()
            remove_at = len(scopes) - 1
            if requested:
                matches = [
                    index
                    for index, (_scope_kind, name, _snapshot) in enumerate(scopes)
                    if name
                    and (name == requested or name.endswith("." + requested))
                ]
                if not matches:
                    continue
                remove_at = matches[-1]
            included = list(scopes[remove_at][2])
            del scopes[remove_at:]
            continue
        include_kind, names_text = match
        names_text = str(names_text or "").strip()
        # Scoped include/omit wrappers are target-local and handled by exact
        # source elaboration; they do not alter persistent section state.
        bare_in = False
        for token in re.finditer("in", names_text):
            before = names_text[token.start() - 1] if token.start() else ""
            after = names_text[token.end()] if token.end() < len(names_text) else ""
            before_ident = bool(before) and (before.isalnum() or before in "_'«")
            after_ident = bool(after) and (after.isalnum() or after in "_'»")
            if not before_ident and not after_ident:
                bare_in = True
                break
        if bare_in:
            continue
        names = re.findall(_IDENT_COMPONENT, names_text, flags=re.UNICODE)
        if str(include_kind) == "include":
            for name in names:
                if name not in included:
                    included.append(name)
        else:
            included = [name for name in included if name not in set(names)]
    return tuple(included)


def theorem_artifact_slug(theorem_name: str) -> str:
    logical = _strip_root_prefix(theorem_name)
    safe = re.sub(r"[^A-Za-z0-9_'-]+", "_", logical).strip("_-")
    safe = re.sub(r"_+", "_", safe)[:72] or "theorem"
    if safe == logical and len(logical) <= 72:
        return safe
    return f"{safe}_{hashlib.sha256(logical.encode('utf-8')).hexdigest()[:10]}"


def generic_theorem_artifact_slug(
    theorem_name: str,
    *,
    project_path: Path,
    lean_file: Path,
    imports: Sequence[str],
    source_dirs: Sequence[Path],
) -> str:
    """Return a source-bound, collision-resistant generic run stem.

    A logical Lean name is only unique inside one environment.  Binding the
    stem to the canonical project and source paths prevents unrelated theorem
    projects that both declare (for example) ``target`` from sharing run and
    publication identities.
    """

    logical = _strip_root_prefix(theorem_name)
    safe = re.sub(r"[^A-Za-z0-9_'-]+", "_", logical).strip("_-")
    safe = re.sub(r"_+", "_", safe)[:64] or "theorem"
    if not re.match(r"[A-Za-z_]", safe):
        safe = f"theorem_{safe}"
    identity = _canonical_json(
        {
            "schema": "theorem-project-artifact-v2",
            "project_path": str(Path(project_path).expanduser().resolve()),
            "lean_file": str(Path(lean_file).expanduser().resolve()),
            "theorem_name": logical,
            "imports": [str(module) for module in imports],
            "source_dirs": [
                str(Path(path).expanduser().resolve()) for path in source_dirs
            ],
        }
    )
    digest = hashlib.sha256(identity).hexdigest()[:12]
    return f"{safe}_{digest}"


def is_valid_lean_qualified_name(name: str) -> bool:
    return re.fullmatch(_DOTTED_IDENT, str(name or "").strip(), re.UNICODE) is not None


def _lean_name_components(name: str) -> tuple[str, ...]:
    """Decode a validated Lean name into filesystem module components.

    Dots inside ``«...»`` are part of one Lean ``Name.str`` component,
    whereas dots outside quoted identifiers separate module components.  The
    guillemets are parser escapes and are not part of the corresponding Lean
    source filename (for example ``import «Init»`` resolves ``Init.olean``).
    """

    value = str(name or "").strip()
    if not is_valid_lean_qualified_name(value):
        return ()
    value = _strip_root_prefix(value)
    components: list[str] = []
    current: list[str] = []
    quoted = False
    for char in value:
        if char == "«" and not quoted:
            quoted = True
            continue
        if char == "»" and quoted:
            quoted = False
            continue
        if char == "." and not quoted:
            components.append("".join(current))
            current = []
            continue
        current.append(char)
    components.append("".join(current))
    if any(
        not component
        or component in {".", ".."}
        or "/" in component
        or "\\" in component
        or "\x00" in component
        for component in components
    ):
        return ()
    return tuple(components)


def _lean_module_source_file(root: Path, module: str) -> Optional[Path]:
    components = _lean_name_components(module)
    if not components:
        return None
    relative = Path(*components[:-1], components[-1] + ".lean")
    candidate = (root / relative).resolve()
    if not _is_within(candidate, root) or not candidate.is_file():
        return None
    return candidate


def _find_project_module_source_anywhere(
    project: Path,
    module: str,
) -> Optional[Path]:
    """Resolve computed Lake srcDir layouts by an unambiguous path suffix."""

    components = _lean_name_components(module)
    if not components:
        return None
    suffix = Path(*components[:-1], components[-1] + ".lean").parts
    matches: list[Path] = []
    for candidate in Path(project).resolve().rglob(components[-1] + ".lean"):
        if ".lake" in candidate.parts or not candidate.is_file():
            continue
        if tuple(candidate.parts[-len(suffix) :]) == suffix:
            matches.append(candidate.resolve())
    unique = tuple(dict.fromkeys(matches))
    if len(unique) > 1:
        rendered = ", ".join(str(path) for path in unique[:4])
        raise ValueError(
            f"ambiguous local source for Lean module {module!r}: {rendered}"
        )
    return unique[0] if unique else None


def is_valid_lean_universe_suffix(value: str) -> bool:
    suffix = str(value or "").strip()
    if not suffix:
        return True
    return (
        re.fullmatch(
            rf"\.\{{\s*{_IDENT_COMPONENT}(?:\s+{_IDENT_COMPONENT})*\s*\}}",
            suffix,
            re.UNICODE,
        )
        is not None
    )


def _tree_content_hash(
    root: Path,
    *,
    include_lake_manifest: bool = True,
) -> str:
    digest = hashlib.sha256()
    wanted_names = {
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
    }
    paths = [
        path
        for path in root.rglob("*")
        if path.is_file()
        and ".lake" not in path.parts
        and (path.suffix == ".lean" or path.name in wanted_names)
        and (include_lake_manifest or path.name != "lake-manifest.json")
    ]
    for path in sorted(paths, key=lambda item: str(item.relative_to(root))):
        digest.update(str(path.relative_to(root)).encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def _compiled_content_hash(roots: Sequence[Path]) -> str:
    digest = hashlib.sha256()
    for root in roots:
        for path in sorted(root.rglob("*.olean"), key=lambda item: str(item)):
            if not path.is_file():
                continue
            digest.update(str(path.relative_to(root)).encode("utf-8"))
            digest.update(b"\0")
            digest.update(path.read_bytes())
            digest.update(b"\0")
    return digest.hexdigest()


def theorem_project_tree_content_hash(root: Path) -> str:
    """Return the canonical project/source hash recorded in an input spec."""

    return _tree_content_hash(Path(root))


def theorem_project_compiled_content_hash(roots: Sequence[Path]) -> str:
    """Return the canonical compiled-module hash recorded in an input spec."""

    return _compiled_content_hash(tuple(Path(root) for root in roots))


def _project_environment_hash(
    project: Path,
    import_sources: Iterable[Path],
    *,
    include_lake_manifest: bool = True,
) -> str:
    """Hash manifests plus the transitive project-local import closure.

    Hashing every ``.lean`` below the project made Mini's own run/export files
    mutate input identity. Lake semantics depend on manifests and imported
    modules, not unrelated potential module filenames, so follow the actual
    local import graph from the resolver's direct project imports.
    """

    project = Path(project).resolve()
    roots = _project_module_source_roots(project)
    files: dict[str, Path] = {}
    for name in ("lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        if name == "lake-manifest.json" and not include_lake_manifest:
            continue
        candidate = project / name
        if candidate.is_file():
            resolved = candidate.resolve()
            files[name] = resolved
    pending = [Path(path).resolve() for path in import_sources]
    visited: set[Path] = set()
    while pending:
        source = pending.pop()
        if source in visited or not source.is_file():
            continue
        visited.add(source)
        provenance_key = (
            str(source.relative_to(project))
            if _is_within(source, project)
            else f"external:{source}"
        )
        files[provenance_key] = source
        try:
            imports = scan_lean_imports(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeError):
            imports = ()
        for module in imports:
            dependency: Optional[Path] = None
            for root in roots:
                dependency = _lean_module_source_file(root, module)
                if dependency is not None and dependency not in visited:
                    pending.append(dependency)
                    break
            if dependency is None:
                dependency = _find_project_module_source_anywhere(project, module)
                if dependency is not None and dependency not in visited:
                    pending.append(dependency)
    digest = hashlib.sha256()
    for provenance_key, path in sorted(files.items()):
        digest.update(provenance_key.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def theorem_project_environment_hash(
    project: Path,
    import_sources: Iterable[Path],
) -> str:
    """Public canonical hash for a theorem project's effective local inputs."""

    return _project_environment_hash(project, import_sources)


def _project_declared_source_roots(project: Path) -> tuple[Path, ...]:
    roots: list[Path] = []
    for manifest_name in ("lakefile.lean", "lakefile.toml"):
        manifest = project / manifest_name
        if not manifest.is_file():
            continue
        text = manifest.read_text(encoding="utf-8")
        for match in re.finditer(
            r"\bsrcDir\s*(?::=|=)\s*[\"']([^\"']+)[\"']",
            text,
        ):
            candidate = (project / str(match.group(1))).resolve()
            if candidate.is_dir() and candidate not in roots:
                roots.append(candidate)
        for match in re.finditer(
            r"\.submodules\s+`([A-Za-z_][A-Za-z0-9_'.]*)",
            text,
        ):
            module_path = Path(*str(match.group(1)).split("."))
            candidate = (project / module_path).resolve()
            if candidate.is_dir() and candidate not in roots:
                roots.append(candidate)
        # Lake projects commonly mix default-layout libraries with unrelated
        # custom-srcDir tools. A project-wide ``explicit_layout`` flag would
        # hide the default library directories as soon as any other target
        # declares srcDir (Mathlib is a real example), so collect declared
        # library-name directories independently.
        library_names: list[str] = []
        for match in re.finditer(
            r"\blean_lib\s+(?:«([^»]+)»|([A-Za-z_][A-Za-z0-9_']*))",
            text,
        ):
            library_names.append(str(match.group(1) or match.group(2) or ""))
        for block in re.finditer(
            r"(?ms)^\[\[lean_lib\]\]\s*$([\s\S]*?)(?=^\[\[|\Z)",
            text,
        ):
            name_match = re.search(
                r"(?m)^\s*name\s*=\s*[\"']([^\"']+)[\"']",
                block.group(1),
            )
            if name_match is not None:
                library_names.append(str(name_match.group(1)))
        for library_name in library_names:
            components = _lean_name_components(library_name)
            if not components:
                continue
            candidate = (project / Path(*components)).resolve()
            if candidate.is_dir() and candidate not in roots:
                roots.append(candidate)
    return tuple(roots)


def _project_module_source_roots(project: Path) -> tuple[Path, ...]:
    """Return roots against which Lake resolves source module filenames."""

    roots: list[Path] = []
    for manifest_name in ("lakefile.lean", "lakefile.toml"):
        manifest = project / manifest_name
        if not manifest.is_file():
            continue
        text = manifest.read_text(encoding="utf-8")
        for match in re.finditer(
            r"\bsrcDir\s*(?::=|=)\s*[\"']([^\"']+)[\"']",
            text,
        ):
            candidate = (project / str(match.group(1))).resolve()
            if candidate.is_dir() and candidate not in roots:
                roots.append(candidate)
    project = project.resolve()
    if project not in roots:
        roots.append(project)
    return tuple(roots)


def _is_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except (OSError, ValueError):
        return False


def _compiled_roots_for_external_source(root: Path) -> tuple[Path, ...]:
    root = root.resolve()
    candidates: list[Path] = [
        root / ".lake" / "build" / "lib" / "lean",
        root / ".lake" / "build" / "lib",
        root / "build" / "lib" / "lean",
        root,
    ]
    # A supporting source directory is commonly ``external-project/src``;
    # Lake places its compiled modules beside that directory under the
    # containing project, not underneath ``src``. Only accept a containing
    # Lake project when the requested directory is one of its declared source
    # roots, so an unrelated scratch directory cannot borrow arbitrary oleans
    # from an ancestor project.
    for project in (root, *root.parents):
        if not any(
            (project / manifest).is_file()
            for manifest in ("lakefile.lean", "lakefile.toml")
        ):
            continue
        declared = _project_declared_source_roots(project)
        if root != project.resolve() and not any(
            _is_within(root, declared_root) for declared_root in declared
        ):
            break
        candidates[0:0] = [
            project / ".lake" / "build" / "lib" / "lean",
            project / ".lake" / "build" / "lib",
            project / "build" / "lib" / "lean",
        ]
        break
    candidates = list(dict.fromkeys(candidate.resolve() for candidate in candidates))
    for candidate in candidates:
        if not candidate.is_dir():
            continue
        try:
            has_olean = next(candidate.rglob("*.olean"), None) is not None
        except OSError:
            has_olean = False
        if has_olean:
            # Candidates are ordered from the compiler's most precise module
            # root to broad compatibility fallbacks. Multiple nested LEAN_PATH
            # roots make the same module resolvable through different names.
            return (candidate.resolve(),)
    external_project = _external_lake_project_for_source(root)
    if external_project is not None:
        # Permit a first-use external Lake project. Preflight builds it before
        # any Lean process starts; the modern Lake module root is predictable.
        return (
            (external_project / ".lake" / "build" / "lib" / "lean").resolve(),
            (external_project / ".lake" / "build" / "lib").resolve(),
        )
    return ()


def _external_lake_project_for_source(root: Path) -> Optional[Path]:
    root = Path(root).resolve()
    for project in (root, *root.parents):
        if not any(
            (project / manifest).is_file()
            for manifest in ("lakefile.lean", "lakefile.toml")
        ):
            continue
        # The nearest containing Lake project is authoritative even when its
        # srcDir is computed in lakefile.lean and cannot be recovered by regex.
        return project.resolve()
    return None


@dataclass(frozen=True)
class TheoremProjectRequest:
    lean_file: Path
    theorem_name: str
    project_path: Path
    imports: tuple[str, ...] = ()
    source_dirs: tuple[Path, ...] = ()
    description: Optional[str] = None

    def normalized(self) -> "TheoremProjectRequest":
        lean_file = Path(self.lean_file).expanduser().resolve(strict=True)
        if not lean_file.is_file() or lean_file.suffix != ".lean":
            raise ValueError(f"Lean input must be an existing .lean file: {lean_file}")
        project = Path(self.project_path).expanduser().resolve(strict=True)
        if not project.is_dir():
            raise ValueError(f"Lean project path is not a directory: {project}")
        if not any((project / name).is_file() for name in ("lakefile.lean", "lakefile.toml")):
            raise ValueError(
                f"Lean project has no lakefile.lean or lakefile.toml: {project}"
            )
        theorem_name = _strip_root_prefix(self.theorem_name)
        if not theorem_name:
            raise ValueError("theorem name is required")
        source_dirs: list[Path] = []
        for raw in self.source_dirs:
            source_dir = Path(raw).expanduser().resolve(strict=True)
            if not source_dir.is_dir():
                raise ValueError(f"supporting source path is not a directory: {source_dir}")
            if source_dir not in source_dirs:
                source_dirs.append(source_dir)
        return TheoremProjectRequest(
            lean_file=lean_file,
            theorem_name=theorem_name,
            project_path=project,
            imports=normalize_imports(self.imports),
            source_dirs=tuple(source_dirs),
            description=(
                str(self.description).strip() if self.description is not None else None
            ),
        )


@dataclass(frozen=True)
class TheoremProblem:
    path: Path
    theorem_name: str
    preamble: str
    lean_preamble: str
    statement_type: str
    docstring: str
    solution_comment: str = ""
    project_path: Optional[Path] = None
    imports: tuple[str, ...] = ()
    source_dirs: tuple[Path, ...] = ()
    module_search_paths: tuple[Path, ...] = ()
    project_imports: tuple[str, ...] = ()
    project_import_sources: Mapping[str, str] = field(default_factory=dict)
    support_project_builds: Mapping[str, tuple[str, ...]] = field(
        default_factory=dict
    )
    raw_text: str = ""
    elaboration_source: str = ""
    target_scoped_prefix: str = ""
    target_omit_variables: tuple[str, ...] = ()
    declaration_name: str = ""
    declaration_universe_suffix: str = ""
    declaration_public: bool = False
    source_docstring: str = ""
    adapter_id: str = GENERIC_ADAPTER_ID
    adapter_metadata: Mapping[str, Any] = field(default_factory=dict)
    input_spec: Mapping[str, Any] = field(default_factory=dict)
    input_spec_hash: str = ""

    @property
    def artifact_slug(self) -> str:
        if self.adapter_id == PUTNAMBENCH_ADAPTER_ID:
            return theorem_artifact_slug(self.theorem_name)
        if self.project_path is None:
            raise ValueError("generic theorem artifact identity requires a project path")
        return generic_theorem_artifact_slug(
            self.theorem_name,
            project_path=self.project_path,
            lean_file=self.path,
            imports=self.imports,
            source_dirs=self.source_dirs,
        )

    @property
    def official_answer_symbols(self) -> tuple[str, ...]:
        raw = self.adapter_metadata.get("official_answer_symbols", ())
        return tuple(str(item) for item in raw if str(item).strip())

    @property
    def exclude_entire_source_from_retrieval(self) -> bool:
        return bool(
            self.adapter_metadata.get(
                "exclude_entire_source_from_retrieval",
                True,
            )
        )

    def theorem_project_record(self) -> dict[str, Any]:
        return dict(self.input_spec)


@dataclass(frozen=True)
class PutnamProblem(TheoremProblem):
    adapter_id: str = PUTNAMBENCH_ADAPTER_ID


def _resolve_theorem_project(
    request: TheoremProjectRequest,
    *,
    adapter_id: str,
    adapter_options: Optional[Mapping[str, Any]] = None,
    allow_sorry_or_admit_prefix: bool = False,
) -> TheoremProblem:
    req = request.normalized()
    source = req.lean_file.read_text(encoding="utf-8")
    declaration = select_lean_theorem(scan_lean_theorems(source), req.theorem_name)
    source_docstring = declaration.docstring
    if has_sorry_or_admit(declaration.statement_type):
        raise ValueError(
            f"target theorem type contains sorry/admit: {declaration.canonical_name}"
        )
    description = req.description if req.description is not None else source_docstring
    if declaration.private:
        raise ValueError(
            f"private theorem targets are not externally addressable: "
            f"{declaration.canonical_name}; expose a public theorem wrapper"
        )
    preamble, target_scoped_prefix = theorem_reusable_preamble(
        source,
        declaration,
        req.imports,
    )
    target_omit_variables = active_include_variables(
        source,
        declaration.declaration_start,
    )
    # Command wrappers belong to the selected declaration, not to the
    # reusable prefix in which Mini verifies generated helpers. In particular,
    # retaining a split ``set_option ... in`` here leaves a dangling command,
    # while turning it into a global option silently changes helper
    # elaboration. The boundary helper holds it out; LeanRunner and export
    # reapply it only around the generated root command.
    if not allow_sorry_or_admit_prefix and has_sorry_or_admit(preamble):
        raise ValueError(
            "generic theorem prefix contains sorry/admit; remove the unsound "
            "dependency or use a benchmark adapter with an explicit assumption policy"
        )

    # Elaborate the selected declaration in its exact command context without
    # compiling its existing proof body or any unrelated downstream command.
    # Keep the theorem/lemma command itself: changing it to an axiom loses
    # `include x in` auto-bound variables. The placeholder is isolated to this
    # non-evidentiary type probe and locally suppresses its expected warning.
    local_header = (
        declaration.command_prefix
        + source[declaration.keyword_start : declaration.header_end]
    ).strip()
    probe_scoped_prefix = theorem_probe_scoped_prefix(target_scoped_prefix)
    isolated_header = "\n".join(
        part
        for part in (
            preamble.rstrip(),
            probe_scoped_prefix,
            "set_option warningAsError false in",
            local_header,
        )
        if part
    ).rstrip()
    # find_decl_header_end includes a genuine top-level assignment opener but
    # stops before an equation clause. Looking for any earlier `:=` confuses
    # let-bindings/named arguments inside an equation-style theorem type with
    # the declaration terminator.
    if not isolated_header.endswith(":="):
        isolated_header += " :="
    closers = _active_command_scope_closers(source, declaration.declaration_start)
    elaboration_source = (
        isolated_header
        + " by\n  set_option warningAsError false in\n  sorry\n"
        + ("\n".join(closers) + "\n" if closers else "")
    )
    elaboration_source = merge_imports(elaboration_source, req.imports)
    lean_preamble = encode_theorem_target_context(
        preamble,
        proof_scoped_prefix=theorem_proof_scoped_prefix(target_scoped_prefix),
        omit_variables=target_omit_variables,
    )

    declared_roots = _project_declared_source_roots(req.project_path)
    project_source_roots = _project_module_source_roots(req.project_path)
    project_import_sources: dict[str, str] = {}
    for module in scan_lean_imports(preamble):
        for root in project_source_roots:
            source_path = _lean_module_source_file(root, module)
            if source_path is not None:
                project_import_sources[module] = str(source_path)
                break
        if module not in project_import_sources:
            source_path = _find_project_module_source_anywhere(
                req.project_path,
                module,
            )
            if source_path is not None:
                project_import_sources[module] = str(source_path)
    project_imports = tuple(project_import_sources)
    module_roots: list[Path] = []
    support_project_builds: dict[str, tuple[str, ...]] = {}
    support_records: list[dict[str, Any]] = []
    for source_dir in req.source_dirs:
        owning_lake_project = _external_lake_project_for_source(source_dir)
        nested_external_project = (
            owning_lake_project
            if owning_lake_project is not None
            and owning_lake_project != req.project_path
            else None
        )
        project_declared = nested_external_project is None and (
            source_dir == req.project_path
            or any(_is_within(source_dir, root) for root in declared_roots)
        )
        external_project = (
            None
            if project_declared
            else nested_external_project
            or _external_lake_project_for_source(source_dir)
        )
        compiled_roots = () if project_declared else _compiled_roots_for_external_source(source_dir)
        if not project_declared and not compiled_roots:
            raise ValueError(
                "supporting source directory is neither declared by the Lake project "
                f"nor backed by compiled .olean modules: {source_dir}"
            )
        if not project_declared and external_project is None:
            raise ValueError(
                "external supporting sources require a containing Lake project "
                f"for freshness validation: {source_dir}"
            )
        support_import_sources: dict[str, str] = {}
        if external_project is not None:
            for module in scan_lean_imports(preamble):
                for root in _project_module_source_roots(external_project):
                    candidate = _lean_module_source_file(root, module)
                    if candidate is not None and _is_within(candidate, source_dir):
                        support_import_sources[module] = str(candidate)
                        break
                if module not in support_import_sources:
                    candidate = _find_project_module_source_anywhere(
                        external_project,
                        module,
                    )
                    if candidate is not None and _is_within(candidate, source_dir):
                        support_import_sources[module] = str(candidate)
            project_key = str(external_project)
            support_project_builds[project_key] = tuple(
                dict.fromkeys(
                    (
                        *support_project_builds.get(project_key, ()),
                        *support_import_sources,
                    )
                )
            )
        for compiled_root in compiled_roots:
            if compiled_root not in module_roots:
                module_roots.append(compiled_root)
        support_records.append(
            {
                "path": str(source_dir),
                "content_hash": _tree_content_hash(source_dir),
                "source_input_hash": _tree_content_hash(
                    source_dir,
                    include_lake_manifest=False,
                ),
                "project_declared": project_declared,
                "compiled_module_roots": [str(path) for path in compiled_roots],
                "compiled_content_hash": _compiled_content_hash(compiled_roots),
                "build_project_path": str(external_project or ""),
                "build_targets": list(support_import_sources),
                "build_import_sources": dict(support_import_sources),
                "build_project_input_hash": (
                    _project_environment_hash(
                        external_project,
                        (Path(path) for path in support_import_sources.values()),
                    )
                    if external_project is not None
                    else ""
                ),
                "build_project_source_input_hash": (
                    _project_environment_hash(
                        external_project,
                        (Path(path) for path in support_import_sources.values()),
                        include_lake_manifest=False,
                    )
                    if external_project is not None
                    else ""
                ),
            }
        )

    spec: dict[str, Any] = {
        "schema_version": THEOREM_PROJECT_SCHEMA_VERSION,
        "adapter_id": adapter_id,
        "lean_file": str(req.lean_file),
        "source_sha256": _sha256_bytes(source.encode("utf-8")),
        "theorem_name": declaration.canonical_name,
        "declaration_name": declaration.source_name,
        "declaration_universe_suffix": declaration.universe_suffix,
        "declaration_public": declaration.public,
        "source_statement_type": declaration.statement_type.strip(),
        "preamble_sha256": _sha256_bytes(preamble.encode("utf-8")),
        "lean_preamble_sha256": _sha256_bytes(lean_preamble.encode("utf-8")),
        "elaboration_source_sha256": _sha256_bytes(
            elaboration_source.encode("utf-8")
        ),
        "target_scoped_prefix": target_scoped_prefix,
        "target_omit_variables": list(target_omit_variables),
        "project_path": str(req.project_path),
        "project_input_hash": _project_environment_hash(
            req.project_path,
            (Path(path) for path in project_import_sources.values()),
        ),
        "project_source_input_hash": _project_environment_hash(
            req.project_path,
            (Path(path) for path in project_import_sources.values()),
            include_lake_manifest=False,
        ),
        "imports": list(req.imports),
        "module_search_paths": [str(path) for path in module_roots],
        "project_imports": list(project_imports),
        "project_import_sources": dict(project_import_sources),
        "support_project_builds": {
            project: list(targets)
            for project, targets in support_project_builds.items()
        },
        "source_dirs": support_records,
        "description": description or "",
        "description_sha256": _sha256_bytes((description or "").encode("utf-8")),
        "source_docstring_sha256": _sha256_bytes(
            source_docstring.encode("utf-8")
        ),
        "solution_comment_sha256": _sha256_bytes(b""),
        "adapter_options": dict(adapter_options or {}),
        "adapter_metadata": {},
    }
    spec_hash = _sha256_bytes(_canonical_json(spec))
    spec["input_spec_hash"] = spec_hash
    return TheoremProblem(
        path=req.lean_file,
        theorem_name=declaration.canonical_name,
        declaration_name=declaration.source_name,
        declaration_universe_suffix=declaration.universe_suffix,
        declaration_public=declaration.public,
        preamble=preamble,
        lean_preamble=lean_preamble,
        statement_type=declaration.statement_type.strip(),
        docstring=description or "",
        source_docstring=source_docstring,
        solution_comment="",
        project_path=req.project_path,
        imports=req.imports,
        source_dirs=req.source_dirs,
        module_search_paths=tuple(module_roots),
        project_imports=project_imports,
        project_import_sources=project_import_sources,
        support_project_builds=support_project_builds,
        raw_text=source,
        elaboration_source=elaboration_source,
        target_scoped_prefix=target_scoped_prefix,
        target_omit_variables=target_omit_variables,
        adapter_id=adapter_id,
        adapter_metadata={},
        input_spec=spec,
        input_spec_hash=spec_hash,
    )


def resolve_theorem_project(request: TheoremProjectRequest) -> TheoremProblem:
    """Resolve a sound, semantics-preserving generic theorem-project input."""

    return _resolve_theorem_project(request, adapter_id=GENERIC_ADAPTER_ID)


def with_elaborated_statement_type(
    problem: TheoremProblem,
    statement_type: str,
    *,
    rendering: str = "",
) -> TheoremProblem:
    """Bind Lean's elaborated declaration type into problem provenance."""

    elaborated = str(statement_type or "").strip()
    if not elaborated:
        raise ValueError("Lean returned an empty elaborated theorem type")
    spec = dict(problem.input_spec)
    spec.pop("input_spec_hash", None)
    # Preserve the parser-bound source statement across a second, safer
    # printer pass. Rebinding an already elaborated problem must never relabel
    # Lean's first display rendering as immutable source provenance.
    spec["source_statement_type"] = str(
        spec.get("source_statement_type") or problem.statement_type
    ).strip()
    spec["elaborated_statement_type"] = elaborated
    clean_rendering = str(rendering or "").strip()
    if clean_rendering:
        spec["elaborated_statement_type_rendering"] = clean_rendering
    else:
        spec.pop("elaborated_statement_type_rendering", None)
    spec_hash = _sha256_bytes(_canonical_json(spec))
    spec["input_spec_hash"] = spec_hash
    return replace(
        problem,
        statement_type=elaborated,
        input_spec=spec,
        input_spec_hash=spec_hash,
    )


def with_theorem_execution_context(
    problem: TheoremProblem,
    *,
    preamble: str,
    lean_preamble: str,
    adapter_metadata: Optional[Mapping[str, Any]] = None,
    docstring: Optional[str] = None,
    source_docstring: Optional[str] = None,
    solution_comment: Optional[str] = None,
) -> TheoremProblem:
    """Bind an adapter-approved proof context into immutable provenance."""

    spec = dict(problem.input_spec)
    spec.pop("input_spec_hash", None)
    spec["preamble_sha256"] = _sha256_bytes(str(preamble).encode("utf-8"))
    spec["lean_preamble_sha256"] = _sha256_bytes(
        str(lean_preamble).encode("utf-8")
    )
    bound_adapter_metadata = dict(
        problem.adapter_metadata
        if adapter_metadata is None
        else adapter_metadata
    )
    spec["adapter_metadata"] = json.loads(
        _canonical_json({"value": bound_adapter_metadata})
    )["value"]
    bound_docstring = problem.docstring if docstring is None else str(docstring)
    bound_source_docstring = (
        problem.source_docstring
        if source_docstring is None
        else str(source_docstring)
    )
    bound_solution_comment = (
        problem.solution_comment
        if solution_comment is None
        else str(solution_comment)
    )
    spec["description"] = bound_docstring
    spec["description_sha256"] = _sha256_bytes(
        bound_docstring.encode("utf-8")
    )
    spec["source_docstring_sha256"] = _sha256_bytes(
        bound_source_docstring.encode("utf-8")
    )
    spec["solution_comment_sha256"] = _sha256_bytes(
        bound_solution_comment.encode("utf-8")
    )
    spec_hash = _sha256_bytes(_canonical_json(spec))
    spec["input_spec_hash"] = spec_hash
    return replace(
        problem,
        preamble=str(preamble),
        lean_preamble=str(lean_preamble),
        adapter_metadata=bound_adapter_metadata,
        docstring=bound_docstring,
        source_docstring=bound_source_docstring,
        solution_comment=bound_solution_comment,
        input_spec=spec,
        input_spec_hash=spec_hash,
    )


def refresh_theorem_project_environment(problem: TheoremProblem) -> TheoremProblem:
    """Rebind provenance after a necessary Lake build changes environment files."""

    spec = dict(problem.input_spec)
    spec.pop("input_spec_hash", None)
    project = Path(str(spec.get("project_path") or problem.project_path or ""))
    if not project.is_dir():
        raise ValueError(f"theorem project disappeared during preflight: {project}")
    spec["project_input_hash"] = _project_environment_hash(
        project,
        (
            Path(str(path))
            for path in dict(spec.get("project_import_sources") or {}).values()
        ),
    )
    refreshed_support: list[dict[str, Any]] = []
    refreshed_module_roots: list[Path] = []
    for raw_record in list(spec.get("source_dirs") or ()):
        if not isinstance(raw_record, Mapping):
            raise ValueError("invalid supporting-source provenance record")
        record = dict(raw_record)
        source_root = Path(str(record.get("path") or ""))
        compiled_roots = tuple(
            Path(str(path))
            for path in list(record.get("compiled_module_roots") or ())
        )
        if str(record.get("build_project_path") or ""):
            compiled_roots = _compiled_roots_for_external_source(source_root)
            record["compiled_module_roots"] = [str(path) for path in compiled_roots]
        if not source_root.is_dir() or any(not path.is_dir() for path in compiled_roots):
            raise ValueError("supporting source environment changed during preflight")
        if _tree_content_hash(
            source_root,
            include_lake_manifest=False,
        ) != str(
            record.get("source_input_hash") or ""
        ):
            raise ValueError(
                "supporting source inputs changed during preflight; resolve "
                "the request again"
            )
        for compiled_root in compiled_roots:
            if compiled_root not in refreshed_module_roots:
                refreshed_module_roots.append(compiled_root)
        record["content_hash"] = _tree_content_hash(source_root)
        record["compiled_content_hash"] = _compiled_content_hash(compiled_roots)
        build_project_text = str(record.get("build_project_path") or "")
        if build_project_text:
            build_project = Path(build_project_text)
            if not build_project.is_dir():
                raise ValueError("supporting Lake project changed during preflight")
            build_import_sources = {
                str(key): str(value)
                for key, value in dict(
                    record.get("build_import_sources") or {}
                ).items()
            }
            build_source_hash = _project_environment_hash(
                build_project,
                (Path(path) for path in build_import_sources.values()),
                include_lake_manifest=False,
            )
            if build_source_hash != str(
                record.get("build_project_source_input_hash") or ""
            ):
                raise ValueError(
                    "supporting Lake source inputs changed during preflight; "
                    "resolve the request again"
                )
            record["build_project_input_hash"] = _project_environment_hash(
                build_project,
                (Path(path) for path in build_import_sources.values()),
            )
        refreshed_support.append(record)
    spec["source_dirs"] = refreshed_support
    spec["module_search_paths"] = [str(path) for path in refreshed_module_roots]
    spec_hash = _sha256_bytes(_canonical_json(spec))
    spec["input_spec_hash"] = spec_hash
    return replace(
        problem,
        module_search_paths=tuple(refreshed_module_roots),
        input_spec=spec,
        input_spec_hash=spec_hash,
    )


def validate_theorem_project_source(problem: TheoremProblem) -> None:
    """Fail closed if the resolved target source changed before execution."""

    recorded_spec_hash = str(problem.input_spec.get("input_spec_hash") or "").strip()
    unhashed_spec = dict(problem.input_spec)
    unhashed_spec.pop("input_spec_hash", None)
    current_spec_hash = _sha256_bytes(_canonical_json(unhashed_spec))
    if (
        not recorded_spec_hash
        or recorded_spec_hash != str(problem.input_spec_hash or "").strip()
        or recorded_spec_hash != current_spec_hash
    ):
        raise ValueError(
            "theorem-project input provenance changed after resolution; resolve "
            "the request again before proof search"
        )
    expected_statement = str(
        problem.input_spec.get("elaborated_statement_type")
        or problem.input_spec.get("source_statement_type")
        or ""
    ).strip()
    executable_contract = (
        bool(expected_statement)
        and str(problem.statement_type or "").strip() == expected_statement
        and str(problem.theorem_name or "").strip()
        == str(problem.input_spec.get("theorem_name") or "").strip()
        and str(problem.declaration_name or "").strip()
        == str(problem.input_spec.get("declaration_name") or "").strip()
        and str(problem.declaration_universe_suffix or "")
        == str(problem.input_spec.get("declaration_universe_suffix") or "")
        and bool(problem.declaration_public)
        is bool(problem.input_spec.get("declaration_public"))
        and str(problem.adapter_id or "").strip()
        == str(problem.input_spec.get("adapter_id") or "").strip()
        and _canonical_json({"value": dict(problem.adapter_metadata)})
        == _canonical_json(
            {"value": dict(problem.input_spec.get("adapter_metadata") or {})}
        )
        and str(problem.docstring or "")
        == str(problem.input_spec.get("description") or "")
        and _sha256_bytes(str(problem.docstring or "").encode("utf-8"))
        == str(problem.input_spec.get("description_sha256") or "")
        and _sha256_bytes(str(problem.source_docstring or "").encode("utf-8"))
        == str(problem.input_spec.get("source_docstring_sha256") or "")
        and _sha256_bytes(str(problem.solution_comment or "").encode("utf-8"))
        == str(problem.input_spec.get("solution_comment_sha256") or "")
        and str(problem.target_scoped_prefix or "")
        == str(problem.input_spec.get("target_scoped_prefix") or "")
        and list(problem.target_omit_variables)
        == list(problem.input_spec.get("target_omit_variables") or ())
        and _sha256_bytes(str(problem.preamble or "").encode("utf-8"))
        == str(problem.input_spec.get("preamble_sha256") or "")
        and _sha256_bytes(str(problem.lean_preamble or "").encode("utf-8"))
        == str(problem.input_spec.get("lean_preamble_sha256") or "")
        and _sha256_bytes(str(problem.elaboration_source or "").encode("utf-8"))
        == str(problem.input_spec.get("elaboration_source_sha256") or "")
        and str(Path(problem.project_path or "").expanduser().resolve())
        == str(problem.input_spec.get("project_path") or "")
        and list(problem.imports) == list(problem.input_spec.get("imports") or ())
        and [str(Path(path).expanduser().resolve()) for path in problem.source_dirs]
        == [
            str(Path(str(record.get("path") or "")).expanduser().resolve())
            for record in list(problem.input_spec.get("source_dirs") or ())
            if isinstance(record, Mapping)
        ]
        and [
            str(Path(path).expanduser().resolve())
            for path in problem.module_search_paths
        ]
        == list(problem.input_spec.get("module_search_paths") or ())
        and list(problem.project_imports)
        == list(problem.input_spec.get("project_imports") or ())
        and {str(key): str(value) for key, value in problem.project_import_sources.items()}
        == {
            str(key): str(value)
            for key, value in dict(
                problem.input_spec.get("project_import_sources") or {}
            ).items()
        }
        and {
            str(key): list(value)
            for key, value in problem.support_project_builds.items()
        }
        == {
            str(key): list(value)
            for key, value in dict(
                problem.input_spec.get("support_project_builds") or {}
            ).items()
        }
        and _sha256_bytes(str(problem.raw_text or "").encode("utf-8"))
        == str(problem.input_spec.get("source_sha256") or "")
    )
    if not executable_contract:
        raise ValueError(
            "theorem-project executable contract changed after resolution; "
            "resolve the request again before proof search"
        )
    project = Path(str(problem.input_spec.get("project_path") or ""))
    project_import_sources = {
        str(key): str(value)
        for key, value in dict(
            problem.input_spec.get("project_import_sources") or {}
        ).items()
    }
    current_project_source_hash = _project_environment_hash(
        project,
        (Path(path) for path in project_import_sources.values()),
        include_lake_manifest=False,
    )
    if current_project_source_hash != str(
        problem.input_spec.get("project_source_input_hash") or ""
    ):
        raise ValueError(
            "theorem-project source environment changed after resolution; "
            "resolve the request again before proof search"
        )
    for raw_record in list(problem.input_spec.get("source_dirs") or ()):
        if not isinstance(raw_record, Mapping):
            raise ValueError("invalid supporting-source provenance record")
        record = dict(raw_record)
        source_root = Path(str(record.get("path") or ""))
        if _tree_content_hash(
            source_root,
            include_lake_manifest=False,
        ) != str(record.get("source_input_hash") or ""):
            raise ValueError(
                "supporting source environment changed after resolution; "
                "resolve the request again before proof search"
            )
        build_project_text = str(record.get("build_project_path") or "")
        if build_project_text:
            build_import_sources = {
                str(key): str(value)
                for key, value in dict(
                    record.get("build_import_sources") or {}
                ).items()
            }
            build_source_hash = _project_environment_hash(
                Path(build_project_text),
                (Path(path) for path in build_import_sources.values()),
                include_lake_manifest=False,
            )
            if build_source_hash != str(
                record.get("build_project_source_input_hash") or ""
            ):
                raise ValueError(
                    "supporting Lake source environment changed after resolution; "
                    "resolve the request again before proof search"
                )
    expected_path = str(problem.input_spec.get("lean_file") or "").strip()
    expected_hash = str(problem.input_spec.get("source_sha256") or "").strip()
    current_path = problem.path.expanduser().resolve(strict=True)
    if not expected_path or str(current_path) != expected_path or not expected_hash:
        raise ValueError("theorem-project target source provenance is incomplete")
    current_hash = _sha256_bytes(
        current_path.read_text(encoding="utf-8").encode("utf-8")
    )
    if current_hash != expected_hash:
        raise ValueError(
            "theorem-project target source changed after resolution; resolve the "
            "request again before proof search"
        )


def infer_lake_project(source_file: Path) -> Optional[Path]:
    current = Path(source_file).expanduser().resolve().parent
    for candidate in (current, *current.parents):
        if any((candidate / name).is_file() for name in ("lakefile.lean", "lakefile.toml")):
            return candidate
    return None


__all__ = [
    "GENERIC_ADAPTER_ID",
    "PUTNAMBENCH_ADAPTER_ID",
    "LeanTheoremDeclaration",
    "PutnamProblem",
    "TheoremProblem",
    "TheoremProjectRequest",
    "active_include_variables",
    "decode_theorem_target_context",
    "encode_theorem_target_context",
    "infer_lake_project",
    "generic_theorem_artifact_slug",
    "has_theorem_target_context",
    "is_valid_lean_qualified_name",
    "merge_imports",
    "normalize_imports",
    "refresh_theorem_project_environment",
    "resolve_theorem_project",
    "scan_lean_declarations",
    "scan_lean_theorems",
    "select_lean_theorem",
    "theorem_artifact_slug",
    "theorem_declaration_context",
    "theorem_proof_scoped_prefix",
    "theorem_probe_scoped_prefix",
    "theorem_reusable_preamble",
    "theorem_project_compiled_content_hash",
    "theorem_project_environment_hash",
    "theorem_project_tree_content_hash",
    "validate_theorem_project_source",
    "with_elaborated_statement_type",
    "with_theorem_execution_context",
]
