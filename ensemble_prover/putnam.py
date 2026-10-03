"""PutnamBench adapter for the generic theorem-project interface."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Callable, Iterable, Optional, Sequence

from .lean_decl_parser import find_decl_header_end
from .lean_source_lexing import _command_matches, _identifier_token_end, _mask_noncode
from .theorem_project import (
    PUTNAMBENCH_ADAPTER_ID,
    PutnamProblem,
    TheoremProjectRequest,
    _DOTTED_IDENT,
    _active_command_scopes,
    _component_identity,
    _name_final_component,
    _qualified_name,
    _raw_name_components,
    _resolve_theorem_project,
    active_include_variables,
    decode_theorem_target_context,
    encode_theorem_target_context,
    infer_lake_project,
    merge_imports,
    scan_lean_theorems,
    select_lean_theorem,
    theorem_proof_scoped_prefix,
    theorem_reusable_preamble,
    with_theorem_execution_context,
)
from .utils import _first_top_level_colon_after


def problem_docstring_text(
    problem: Any,
    *,
    fallback: str = "(no natural-language description provided)",
) -> str:
    """Return normalized natural-language problem text for any problem-like object."""

    text = str(getattr(problem, "docstring", "") or "").strip()
    return text or fallback


_DECL_RE = re.compile(
    rf"(?m)^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+({_DOTTED_IDENT})"
)
_SORRY_DEF_RE = re.compile(
    rf"(?m)^\s*(?:noncomputable\s+)?(abbrev|def)\s+({_DOTTED_IDENT})\s*:\s*(.*?)\s*"
    r"(?P<assignment>:=)\s*(?P<placeholder>sorry)\s*$"
)
# Two-line pattern: sorry def followed by a solution-value comment (PutnamBench convention).
_SORRY_VALUE_RE = re.compile(
    rf"(?m)^(\s*(?:noncomputable\s+)?)(abbrev|def)\s+({_DOTTED_IDENT})\s*:\s*(.*?)\s*"
    r"(?P<assignment>:=)\s*(?P<placeholder>sorry)[^\S\n]*\n[^\S\n]*--[^\S\n]*"
    r"(?P<solution_value>.+?)[^\S\n]*$"
)


def _strip_comments_and_strings_for_sorry_scan(text: str) -> str:
    """Erase Lean comments/string contents before looking for code `sorry`.

    Preamble sanitization operates before the theorem, where explanatory
    comments commonly mention unfinished `sorry` proofs.  Treating those
    comments as executable `sorry` can replace the wrong declaration and
    corrupt namespace/section balance.
    """

    # Keep escaped names so a qualified token such as ``Foo.«x».sorry``
    # remains one identifier rather than exposing its final component.
    return _mask_noncode(text)


def _contains_code_sorry(text: str) -> bool:
    masked = _strip_comments_and_strings_for_sorry_scan(text)
    index = 0
    while index < len(masked):
        end = _identifier_token_end(masked, start=index)
        if end > index:
            if masked[index:end] == "sorry":
                return True
            index = end
        else:
            index += 1
    return False


def _code_declaration_matches(
    pattern: re.Pattern[str], text: str, *, kind_group: int = 1,
) -> Iterable[re.Match[str]]:
    """Keep original captures only when declaration syntax is code."""

    masked = _mask_noncode(text, mask_quoted_identifiers=True)
    for match in pattern.finditer(text):
        start, end = match.span(kind_group)
        if masked[start:end] != match.group(kind_group):
            continue
        # A regex prefix is not a declaration name. Check the shared lexical
        # token as well, preserving apostrophes, qualified and escaped names.
        name_start, name_end = match.span(kind_group + 1)
        if _identifier_token_end(text, start=name_start) != name_end:
            continue
        # A real declaration keyword can precede a multiline escaped type
        # containing the text ``:= sorry``. The placeholder pattern must also
        # point at executable assignment/body tokens, not that type's text.
        syntax_groups = (name for name in ("assignment", "placeholder") if name in pattern.groupindex)
        if any(masked[match.start(name):match.end(name)] != match.group(name)
               for name in syntax_groups):
            continue
        yield match


def _replace_code_declarations(
    pattern: re.Pattern[str], replacement: Callable[[re.Match[str]], str],
    text: str, *, kind_group: int = 1,
) -> str:
    parts: list[str] = []
    cursor = 0
    for match in _code_declaration_matches(pattern, text, kind_group=kind_group):
        parts.extend((text[cursor:match.start()], replacement(match)))
        cursor = match.end()
    parts.append(text[cursor:])
    return "".join(parts)


# Lean commands that may only start a new top-level declaration or scope.  A
# preamble declaration body ends right before one of these so sanitization
# cannot swallow a following scope closer or prerequisite declaration.
_PREAMBLE_BOUNDARY_COMMANDS = frozenset(
    {
        "namespace",
        "section",
        "end",
        "open",
        "variable",
        "include",
        "omit",
        "set_option",
        "attribute",
        "local",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "noncomputable",
        "private",
        "protected",
        "instance",
        "example",
        "class",
        "structure",
        "inductive",
        "axiom",
        "constant",
        "opaque",
        "mutual",
    }
)
_COMMAND_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def _lean_identifier_continues(text: str, index: int) -> bool:
    """Return whether the Lean identifier token at *text* continues at *index*.

    The shared lexer follows Lean's ``isIdRest`` and qualified-name rules,
    including letter-like symbols such as ``℘`` that Python's Unicode
    alphanumeric predicate excludes. A keyword prefix of ``end℘`` or
    ``end.foo`` must not cut a declaration body in half.
    """

    return _identifier_token_end(text) > index


def _is_top_level_preamble_boundary(line: str) -> bool:
    """Return whether an unindented line starts a new top-level command.

    Only a line whose first token is a Lean command keyword bounds a
    declaration body.  Multiline Lean bodies routinely continue with
    unindented non-command lines (``by``, ``trivial``, a bare application);
    treating every column-zero line as a boundary would truncate them, and
    matching literal prefixes would miss a bare ``end`` or an ``axiom``.  The
    keyword must also be followed by an identifier boundary so the valid
    identifiers ``end!`` and ``end₁`` are not read as the ``end`` command.
    """

    if not line:
        return False
    if line[:1] in {" ", "\t"}:
        return False
    stripped = str(line).strip()
    if not stripped:
        return False
    if stripped.startswith(("/--", "/-!")):
        return True
    match = _COMMAND_WORD_RE.match(stripped)
    if match is None:
        return False
    if _lean_identifier_continues(stripped, match.end()):
        return False
    return match.group(0) in _PREAMBLE_BOUNDARY_COMMANDS


def _find_decl_body_end(text: str, header_end: int) -> int:
    """Best-effort end of a preamble declaration body.

    We only need this for sanitization, not full Lean parsing.  The scanner
    keeps indented tactic/value bodies with the declaration and stops before
    the next top-level preamble command such as `namespace`, `end`, or another
    declaration.  This prevents replacing a `sorry` declaration from swallowing
    the following `end Namespace`.
    """

    src = str(text or "")
    if header_end >= len(src):
        return len(src)
    first_newline = src.find("\n", header_end)
    if first_newline == -1:
        return len(src)
    # Scan the complete source so a literal/comment opened on an earlier line
    # cannot turn its contents into a command. Preserve documentation openers:
    # they belong to the following declaration and must survive replacement.
    masked = _mask_noncode(src, preserve_doc_comments=True)
    # Keep escaped names intact for token boundaries (``end.«name»`` is a
    # reference), while excluding lines inside a multiline escaped name.
    for line in _command_matches(re.compile(r"(?m)^[^\n]*"), masked):
        if line.start() <= first_newline:
            continue
        if _is_top_level_preamble_boundary(line.group()):
            return line.start()
    return len(src)


def _axiomatize_concrete_solution_decls(preamble: str) -> str:
    """Hide concrete `*_solution` definitions without eating later commands."""

    text = str(preamble or "")
    replacements: list[tuple[int, int, str]] = []
    for match in _code_declaration_matches(_DECL_RE, text):
        kind = match.group(1)
        name = match.group(2)
        if kind not in {"def", "abbrev"} or not _component_identity(
            _name_final_component(name)
        ).endswith("_solution"):
            continue
        header_end = find_decl_header_end(text, match.end())
        if header_end is None:
            continue
        header = text[match.start() : header_end]
        if ":=" not in header:
            continue
        try:
            parsed_name, typ = _header_to_type(header)
        except Exception:
            continue
        decl_end = _find_decl_body_end(text, header_end)
        replacements.append(
            (match.start(), decl_end, f"axiom {parsed_name} : {typ}\n")
        )

    if not replacements:
        return text
    out = text
    for start, end, repl in reversed(replacements):
        out = out[:start] + repl + out[end:]
    return out


def _find_theorem_header(
    text: str, theorem_name: Optional[str] = None
) -> tuple[int, int, str]:
    """
    Returns (start_idx, end_idx, name) for the theorem header, where end_idx is the
    index just after the first ':=' token following the theorem start.
    """
    declarations = scan_lean_theorems(text)
    if not declarations:
        raise ValueError("No theorem found")
    declaration = (
        select_lean_theorem(declarations, theorem_name)
        if theorem_name
        else declarations[0]
    )
    return (
        declaration.declaration_start,
        declaration.header_end,
        declaration.canonical_name,
    )


def _extract_docstring_before(text: str, theorem_start: int) -> str:
    """
    Best-effort: extract the nearest Lean docstring '/-- ... -/' immediately preceding the theorem.
    """
    prefix = text[:theorem_start]
    end = prefix.rfind("-/")
    if end == -1:
        return ""
    start = prefix.rfind("/--", 0, end)
    if start == -1:
        return ""
    # Ensure there's only whitespace/newlines between docstring end and theorem.
    between = prefix[end + 2 :]
    if between.strip():
        return ""
    return prefix[start : end + 2].strip()


def _header_to_type(header: str) -> tuple[str, str]:
    # Remove trailing ':=' so we don't accidentally select that ':' as the type separator.
    if ":=" in header:
        header = header.rsplit(":=", 1)[0]
    m = re.search(r"\b(theorem|lemma|def|abbrev)\s+", header)
    if not m:
        raise ValueError("Header missing declaration name")
    name_end = _identifier_token_end(header, start=m.end())
    name = header[m.end():name_end]
    if not name:
        raise ValueError("Header missing declaration name")
    colon_pos = _first_top_level_colon_after(header, name_end)
    if colon_pos == -1:
        raise ValueError(f"Header for {name} missing top-level ':'")
    binder_part = header[name_end:colon_pos].strip()
    type_part = header[colon_pos + 1 :].strip()
    # Drop any trailing ':=' if present (some callers may include it).
    if type_part.endswith(":="):
        type_part = type_part[:-2].strip()
    if binder_part:
        return name, f"∀ {binder_part}, {type_part}"
    return name, type_part


def _sanitize_preamble(preamble: str, *, fill_values: bool = False) -> str:
    """
    Replace placeholder definitions like ``abbrev foo : T := sorry``.

    When *fill_values* is True (for Lean checking), substitute concrete values
    from next-line solution comments so the constant is reducible/unfoldable.

    When *fill_values* is False (for LLM prompts), convert to opaque
    ``axiom foo : T`` and strip solution comments — the LLM must derive the
    answer independently.
    """

    def _repl_value(match: re.Match[str]) -> str:
        prefix = match.group(1)  # e.g. "noncomputable " or ""
        kind = match.group(2)  # "abbrev" or "def"
        name = match.group(3)
        typ = match.group(4).strip()
        value = match.group("solution_value").strip()
        # A ``sorry`` placeholder elaborates regardless of whether its eventual
        # body is executable.  The answer supplied by PutnamBench may not be:
        # for example ``Real.exp 1`` has no compiler implementation.  Always
        # make the filled checker-only declaration noncomputable so replacing
        # the placeholder cannot introduce a compiler-IR failure.  This does
        # not affect the prompt-safe preamble, which uses an opaque axiom.
        if "noncomputable" not in prefix.split():
            prefix = f"{prefix}noncomputable "
        return f"{prefix}{kind} {name} : {typ} := {value}"

    def _repl_axiom_with_comment(match: re.Match[str]) -> str:
        """Replace sorry def + solution comment → axiom (strips both lines)."""
        name = match.group(3)
        typ = match.group(4).strip()
        return f"axiom {name} : {typ}"

    def _repl_axiom(match: re.Match[str]) -> str:
        name = match.group(2)
        typ = match.group(3).strip()
        return f"axiom {name} : {typ}"

    if fill_values:
        # Pass 0: sorry defs with a next-line solution comment → fill in value.
        sanitized = _replace_code_declarations(
            _SORRY_VALUE_RE, _repl_value, preamble, kind_group=2,
        )
    else:
        # Pass 0: sorry defs with a next-line solution comment → axiom
        # (strips both the sorry line AND the solution comment line).
        sanitized = _replace_code_declarations(
            _SORRY_VALUE_RE, _repl_axiom_with_comment, preamble, kind_group=2,
        )

    # Pass 1: remaining sorry defs (no solution comment) → opaque axiom.
    sanitized = _replace_code_declarations(_SORRY_DEF_RE, _repl_axiom, sanitized)

    if not fill_values:
        # Some local or generated Putnam files already contain concrete answer
        # definitions.  The prompt-safe preamble must hide those values as
        # axioms, but only the declaration body should be replaced; namespace,
        # section, and helper commands following it must remain balanced.
        sanitized = _axiomatize_concrete_solution_decls(sanitized)

    # Then, replace any declaration block containing `sorry` with an axiom.
    matches = list(_code_declaration_matches(_DECL_RE, sanitized))
    if not matches:
        return sanitized

    out_parts: list[str] = []
    cursor = 0
    for i, m in enumerate(matches):
        start = m.start()
        header_end = find_decl_header_end(sanitized, m.end())
        if header_end is None:
            continue
        end = _find_decl_body_end(sanitized, header_end)
        block = sanitized[start:end]
        if not _contains_code_sorry(block):
            continue
        if ":=" not in block:
            continue
        header = sanitized[start:header_end]
        try:
            name, typ = _header_to_type(header)
        except Exception:
            continue
        out_parts.append(sanitized[cursor:start])
        out_parts.append(f"axiom {name} : {typ}\n")
        cursor = end

    if cursor == 0:
        return sanitized
    out_parts.append(sanitized[cursor:])
    return "".join(out_parts)


def _extract_solution_comment(
    preamble: str,
    *,
    theorem_name: str,
) -> str:
    # The suffix belongs inside the final decoded component, including when
    # the theorem is escaped. Canonical names already resolve `_root_` and
    # enclosing namespaces; do not reinterpret them as source references.
    target_components = tuple(map(_component_identity, _raw_name_components(theorem_name)))
    preferred_components = (
        (*target_components[:-1], target_components[-1] + "_solution")
        if target_components else ()
    )
    fallback = ""
    for match in _code_declaration_matches(
        _SORRY_VALUE_RE, str(preamble or ""), kind_group=2,
    ):
        name = str(match.group(3) or "").strip()
        comment = str(match.group("solution_value") or "").strip()
        if not comment:
            continue
        namespace = tuple(
            scope_name
            for kind, scope_name, _start, _end in _active_command_scopes(preamble, match.start(3))
            if kind == "namespace"
        )
        components = tuple(map(
            _component_identity, _raw_name_components(_qualified_name(namespace, name)),
        ))
        if preferred_components and components == preferred_components:
            return comment
        if not fallback and _component_identity(_name_final_component(name)).endswith("_solution"):
            fallback = comment
    return fallback


def load_putnam_problem(
    path: str | Path, theorem_name: Optional[str] = None
) -> PutnamProblem:
    p = Path(path)
    text = p.read_text(encoding="utf-8")
    declarations = scan_lean_theorems(text)
    if not declarations:
        raise ValueError("No theorem found")
    declaration = (
        select_lean_theorem(declarations, theorem_name)
        if theorem_name
        else declarations[0]
    )
    docstring = declaration.docstring
    name = declaration.canonical_name
    statement_type = declaration.statement_type
    preamble, target_scoped_prefix = theorem_reusable_preamble(
        text,
        declaration,
    )
    preamble = preamble.rstrip() + "\n"
    target_omit_variables = active_include_variables(
        text,
        declaration.declaration_start,
    )
    solution_comment = _extract_solution_comment(preamble, theorem_name=name)
    prompt_preamble = _sanitize_preamble(preamble, fill_values=False)
    answer_safe_lean_preamble = encode_theorem_target_context(
        prompt_preamble,
        proof_scoped_prefix=theorem_proof_scoped_prefix(target_scoped_prefix),
        omit_variables=target_omit_variables,
    )
    lean_preamble = encode_theorem_target_context(
        _sanitize_preamble(preamble, fill_values=True),
        proof_scoped_prefix=theorem_proof_scoped_prefix(target_scoped_prefix),
        omit_variables=target_omit_variables,
    )
    return PutnamProblem(
        path=p,
        theorem_name=name,
        preamble=prompt_preamble,
        lean_preamble=lean_preamble,
        statement_type=statement_type.strip(),
        docstring=docstring,
        solution_comment=solution_comment,
        target_scoped_prefix=target_scoped_prefix,
        target_omit_variables=target_omit_variables,
        adapter_metadata={
            "answer_safe_lean_preamble": answer_safe_lean_preamble
        },
    )


def load_putnam_project(
    path: str | Path,
    theorem_name: Optional[str] = None,
    *,
    project_path: str | Path | None = None,
    imports: Sequence[str] = (),
    source_dirs: Sequence[str | Path] = (),
    description: Optional[str] = None,
) -> PutnamProblem:
    """Resolve PutnamBench through the generic theorem-project boundary.

    The adapter preserves the benchmark's answer-safe/checker preamble split;
    the generic loader itself never applies these transformations.
    """

    source_path = Path(path).expanduser().resolve(strict=True)
    raw_text = source_path.read_text(encoding="utf-8")
    declarations = scan_lean_theorems(raw_text)
    if not declarations:
        raise ValueError("No theorem found")
    selected = (
        select_lean_theorem(declarations, theorem_name)
        if theorem_name
        else declarations[0]
    )
    resolved_project = (
        Path(project_path).expanduser().resolve(strict=True)
        if project_path is not None
        else infer_lake_project(source_path)
    )
    if resolved_project is None:
        raise ValueError(
            f"could not infer a Lake project for Putnam source {source_path}; "
            "pass --project-path"
        )
    from .putnam_answer_input import PUTNAM_ANSWER_MARKER, load_putnam_answer_project

    if raw_text.startswith(PUTNAM_ANSWER_MARKER + "\n"):
        return load_putnam_answer_project(
            TheoremProjectRequest(
                lean_file=source_path,
                theorem_name=selected.canonical_name,
                project_path=resolved_project,
                imports=tuple(imports),
                source_dirs=tuple(Path(item) for item in source_dirs),
                description=description,
            )
        )
    generic = _resolve_theorem_project(
        TheoremProjectRequest(
            lean_file=source_path,
            theorem_name=selected.canonical_name,
            project_path=resolved_project,
            imports=tuple(imports),
            source_dirs=tuple(Path(item) for item in source_dirs),
            description=description,
        ),
        adapter_id=PUTNAMBENCH_ADAPTER_ID,
        allow_sorry_or_admit_prefix=True,
    )
    legacy = load_putnam_problem(source_path, theorem_name=selected.canonical_name)
    legacy_lean_preamble, _legacy_scope, _legacy_omit = (
        decode_theorem_target_context(legacy.lean_preamble)
    )
    answer_symbol = f"{legacy.theorem_name}_solution"
    answer_safe_preamble = merge_imports(legacy.preamble, generic.imports)
    answer_safe_lean_preamble = encode_theorem_target_context(
        answer_safe_preamble,
        proof_scoped_prefix=theorem_proof_scoped_prefix(
            generic.target_scoped_prefix
        ),
        omit_variables=generic.target_omit_variables,
    )
    proof_lean_preamble = encode_theorem_target_context(
        merge_imports(legacy_lean_preamble, generic.imports),
        proof_scoped_prefix=theorem_proof_scoped_prefix(
            generic.target_scoped_prefix
        ),
        omit_variables=generic.target_omit_variables,
    )
    adapter_metadata = {
        "official_answer_symbols": (answer_symbol,),
        "answer_safe_preamble": True,
        "answer_safe_lean_preamble": answer_safe_lean_preamble,
        "exclude_entire_source_from_retrieval": True,
    }
    generic = with_theorem_execution_context(
        generic,
        preamble=answer_safe_preamble,
        lean_preamble=proof_lean_preamble,
        adapter_metadata=adapter_metadata,
        docstring=(
            str(description).strip()
            if description is not None
            else legacy.docstring
        ),
        source_docstring=legacy.docstring,
        solution_comment=legacy.solution_comment,
    )
    return PutnamProblem(
        path=generic.path,
        theorem_name=generic.theorem_name,
        declaration_name=generic.declaration_name,
        declaration_universe_suffix=generic.declaration_universe_suffix,
        declaration_public=generic.declaration_public,
        preamble=answer_safe_preamble,
        lean_preamble=proof_lean_preamble,
        statement_type=generic.statement_type,
        docstring=generic.docstring,
        source_docstring=generic.source_docstring,
        solution_comment=generic.solution_comment,
        project_path=generic.project_path,
        imports=generic.imports,
        source_dirs=generic.source_dirs,
        module_search_paths=generic.module_search_paths,
        project_imports=generic.project_imports,
        project_import_sources=generic.project_import_sources,
        support_project_builds=generic.support_project_builds,
        raw_text=generic.raw_text,
        elaboration_source=generic.elaboration_source,
        target_scoped_prefix=generic.target_scoped_prefix,
        target_omit_variables=generic.target_omit_variables,
        adapter_metadata=generic.adapter_metadata,
        input_spec=generic.input_spec,
        input_spec_hash=generic.input_spec_hash,
    )


_PUTNAM_BENCH_PROBLEM_STEM_RE = re.compile(
    r"^putnam_\d{4}_[ab]\d+(?:_solution(?:_[A-Za-z0-9_']+)?)?$",
    re.IGNORECASE,
)


def is_putnam_bench_problem_source(path: str | Path) -> bool:
    """Return True for PutnamBench contest problem files, not library modules."""

    return bool(_PUTNAM_BENCH_PROBLEM_STEM_RE.fullmatch(Path(path).stem))


def is_putnam_bench_problem_declaration(name: str) -> bool:
    """Return True for PutnamBench contest theorem or solution identifiers."""

    token = str(name or "").strip().split(".")[-1]
    return bool(_PUTNAM_BENCH_PROBLEM_STEM_RE.fullmatch(token))


def iter_putnam_src(
    putnam_src_dir: str | Path,
) -> Iterable[Path]:
    root = Path(putnam_src_dir)
    yield from sorted(root.glob("*.lean"))
