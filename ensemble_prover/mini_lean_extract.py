"""Lean proof extraction helpers for mini-prover runs."""

from __future__ import annotations

import re
import textwrap
import unicodedata
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from .helper_salvage import (
    dedupe_helpers_by_name_last_wins,
    order_helpers_for_incremental_validation,
)
from .lean_syntax import normalize_nat_factorial_notation
from .proof_dossier import (
    helper_decl_body,
    helper_decl_kind,
    helper_decl_name,
    helper_decl_statement,
)
from .proof_state import lean_referenced_helper_names
from .utils import extract_code_fences, extract_proof_candidates


def _extract_first_proof(llm_output: str) -> Optional[str]:
    candidates = extract_proof_candidates(llm_output or "")
    return candidates[0] if candidates else None


# ---------------------------------------------------------------------------
# Helper extraction.
#
# The model is now allowed to emit top-level helper declarations before the
# main proof. We slice the lean fenced block into (helpers, main_proof) and
# pass helpers as ``lemmas=`` to ``LeanRunner.check`` (which inserts them
# between the preamble and the ``example`` line in the synthesized file).
# ---------------------------------------------------------------------------

# Top-level declaration headers we recognize as helpers. ``example`` and bare
# ``by`` are the main-proof markers. The regex anchors to start-of-line so we
# don't misclassify ``theorem`` keywords inside nested ``have`` blocks.
_TOP_LEVEL_HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|by\b)",
    re.MULTILINE,
)
_DECLARATION_BODY_HEADER_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
}

_PLAUSIBLE_PROOF_CHATTER_HEADS = {
    "another",
    "answer",
    "assistant",
    "continue",
    "conclude",
    "done",
    "finished",
    "i",
    "look",
    "maybe",
    "no",
    "none",
    "okay",
    "perhaps",
    "please",
    "proof",
    "retry",
    "search",
    "searching",
    "sure",
    "think",
    "thus",
    "the",
    "theorem",
    "this",
    "try",
    "unfortunately",
    "unknown",
    "we",
    "yes",
    "you",
}

_PLAUSIBLE_PROOF_CHATTER_WORDS = {
    "again",
    "following",
    "how",
    "look",
    "needed",
    "please",
    "result",
    "search",
}

_PLAUSIBLE_LEAN_IDENT_START = r"(?:[^\W\d]|_)"
_PLAUSIBLE_LEAN_IDENT = rf"{_PLAUSIBLE_LEAN_IDENT_START}[\w']*[!?]?"
_EXAMPLE_BINDER_RESERVED_NAMES = frozenset(
    {
        "by",
        "calc",
        "do",
        "else",
        "exists",
        "forall",
        "fun",
        "have",
        "if",
        "in",
        "let",
        "match",
        "show",
        "then",
        "where",
    }
)
_LEAN_OPERATOR_ASCII_CHARS = frozenset(
    "!#$%&*+/:;<=>?@\\^|-~"
)
_NON_PROOF_BARE_TYPE_HEADS = frozenset(
    {"fin", "list", "nat", "prop", "set", "sort", "type"}
)
_LOWERCASE_PROOF_APPLICATION_HEADS = frozenset(
    {"absurd", "cast", "congr", "funext", "id", "mp", "propext"}
)


def _is_plausible_lean_symbolic_atom(
    atom: str, operand_pattern: re.Pattern[str]
) -> bool:
    """Accept Lean operator runs, including compact operand notation.

    Lean permits user-defined symbolic operators, so an exhaustive token list
    would reject executable terms. Restrict symbols to Lean's ASCII operator
    alphabet and Unicode symbol categories, and require every interleaved
    non-symbol run to remain an already-recognized Lean operand.
    """

    if not atom:
        return False

    def is_symbol(character: str) -> bool:
        return (
            character in _LEAN_OPERATOR_ASCII_CHARS
            or unicodedata.category(character).startswith("S")
        )

    saw_symbol = False
    start = 0
    symbol_run = is_symbol(atom[0])
    for index in range(1, len(atom) + 1):
        next_symbol = is_symbol(atom[index]) if index < len(atom) else None
        if next_symbol == symbol_run:
            continue
        chunk = atom[start:index]
        if symbol_run:
            saw_symbol = True
        elif not operand_pattern.fullmatch(chunk):
            return False
        start = index
        symbol_run = bool(next_symbol)
    return saw_symbol


def _has_plausible_lean_proof_head(atoms: Sequence[str]) -> bool:
    """Require evidence beyond a plain multiword identifier phrase."""

    if not atoms:
        return False
    raw_head = atoms[0]
    unqualified = raw_head.lstrip("@").split(".", 1)[0]
    normalized = unqualified.lower().rstrip("!?;")
    if (
        normalized in _NON_PROOF_BARE_TYPE_HEADS
        and "." not in raw_head
    ):
        return False
    if len(atoms) == 1:
        return True

    def has_proof_evidence(atom: str) -> bool:
        identifier = atom.lstrip("@").split(".", 1)[0]
        return bool(
            len(identifier) == 1
            or "." in atom
            or atom.startswith(("(", "@", "«"))
            or atom.endswith(("!", "?"))
            or "_" in identifier
            or any(character.isdigit() for character in identifier)
            or any(character.isupper() for character in identifier[1:])
        )

    if has_proof_evidence(raw_head):
        return True
    has_hypothesis_argument = any(
        re.fullmatch(r"h(?:[p-z][0-9_]*|[A-Z0-9_].*)?", atom)
        for atom in atoms[1:]
    )
    plausible_lowercase_head = (
        normalized.startswith("h") and has_hypothesis_argument
        or normalized in _LOWERCASE_PROOF_APPLICATION_HEADS
    )
    return plausible_lowercase_head and (
        has_hypothesis_argument
        or any(has_proof_evidence(atom) for atom in atoms[1:])
    )

_CONSTRUCTION_COLLAPSE_RE = re.compile(
    r"\b(?:"
    r"known[-\s]?answer|"
    r"no[-\s]?construction|"
    r"opaque (?:constant|proposition|solution|placeholder|value|set)|"
    r"official solution(?: set| value)?|"
    r"solution placeholder|"
    r"benchmark(?:'s)? solution value|"
    r"proof obligation (?:is|looks|seems) (?:too )?(?:large|big|complex)|"
    r"(?:too|very) (?:large|big|complex) (?:to|for) (?:prove|construct|finish)|"
    r"would require (?:many|substantial|additional|a lot of) (?:lemmas|construction|work)|"
    r"(?:complete|full) (?:lean )?(?:proof|solution) requires|"
    r"requires? (?:an? )?explicit construction|"
    r"need(?:s)? (?:a|several|many) (?:durable )?(?:lemma|lemmas|subgoal|subgoals)|"
    r"full proof (?:is )?not provided|"
    r"explicit construction omitted|"
    r"no construction provided|"
    r"not derivable by simplification|"
    r"not available in (?:the )?(?:current context|mathlib)|"
    r"no such (?:lemmas|constructions) are available|"
    r"cannot (?:construct|complete|finish) (?:the )?(?:full )?proof"
    r")\b",
    re.IGNORECASE,
)

_NOOP_ROOT_PROOF_RE = re.compile(
    r"^by\s*(?:classical\s*)?"
    r"(?:(?:simpa|simp|aesop)(?:\s*(?:only\s*)?\[[^\]]*\])?|"
    r"rfl|trivial)\s*$",
    re.DOTALL,
)
_BRACKETED_STITCHING_TACTIC_RE = re.compile(
    r"^by\s*(?:classical\s*)?"
    r"(?:simpa|simp|aesop)\s*(?:only\s*)?\[([^\]]+)\]\s*$",
    re.DOTALL,
)
_LEAN_IDENTIFIER_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b")
_LEAN_TACTIC_ARG_WORDS = {
    "at",
    "by",
    "false",
    "only",
    "true",
}
_SOLUTION_PLACEHOLDER_IDENTIFIER_RE = re.compile(
    r"\bputnam_\d{4}_[ab]\d+_solution\b"
)

_FORBIDDEN_LEAN_COMMAND_RE = re.compile(
    # Top-level commands the model is not allowed to emit because they can
    # mutate the verification environment in ways the recorder cannot
    # capture as a separate effect (only the source text shows). All of:
    #   #cmd                — meta-introspection (#check / #print / #eval)
    #   import              — extends the import graph beyond what the
    #                         answer-safe preamble fixed
    #   axiom               — adds an unproven assumption to the env
    #   set_option          — can relax compilation strictness
    #                         (autoImplicit, maxHeartbeats, linter.*)
    #                         and change verifiability
    #   attribute           — globally tags lemmas (e.g. ``[simp]``),
    #                         shifting tactic behavior for everything
    #                         downstream in the file
    #   register_simp_attr  — defines new simp attribute namespaces
    #   local               — modifier prefix for ``local notation`` /
    #                         ``local instance`` / etc.; covers all of
    #                         them in one sweep
    #
    # Anchor: the regex is line-oriented and may match indented commands
    # because models sometimes hide extra top-level commands after a proof
    # body. ``_find_forbidden_lean_command`` applies the narrow exception for
    # legitimate local ``open ... in`` proof-body lines.
    r"(?m)^\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"("
    r"#\w+"
    r"|import\b"
    r"|axiom\b"
    r"|set_option\b"
    r"|attribute\b"
    r"|register_simp_attr\b"
    r"|register_option\b"
    r"|constant\b"
    r"|opaque\b"
    r"|structure\b"
    r"|class\b"
    r"|inductive\b"
    r"|coinductive\b"
    r"|mutual\b"
    r"|namespace\b"
    r"|section\b"
    r"|end\b"
    r"|open\b"
    r"|variable\b"
    r"|variables\b"
    r"|universe\b"
    r"|universes\b"
    r"|syntax\b"
    r"|macro\b"
    r"|elab\b"
    r"|elab_rules\b"
    r"|notation\b"
    r"|infix\b"
    r"|prefix\b"
    r"|postfix\b"
    r"|scoped\b"
    r"|initialize\b"
    r"|builtin_initialize\b"
    r"|declare_syntax_cat\b"
    r"|export\b"
    r"|alias\b"
    r"|run_cmd\b"
    r"|local\b"
    r")"
)


_SAFE_LEADING_IMPORT_RE = re.compile(
    r"^import\s+[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*$"
)
_LEAN_OPEN_NAME_COMPONENT_RE = r"(?:«[^»\r\n]+»|[^\W\d][\w']*)"
_LEAN_OPEN_NAME_RE = (
    _LEAN_OPEN_NAME_COMPONENT_RE
    + r"(?:\."
    + _LEAN_OPEN_NAME_COMPONENT_RE
    + r")*"
)
_SAFE_LEADING_OPEN_RE = re.compile(
    r"^open(?:\s+scoped)?\s+"
    + _LEAN_OPEN_NAME_RE
    + r"(?:\s+"
    + _LEAN_OPEN_NAME_RE
    + r")*$"
)
_LOCAL_OPEN_TERM_PREFIX_RE = re.compile(
    r"^\s*open(?:\s+scoped)?\s+"
    + _LEAN_OPEN_NAME_RE
    + r"(?:\s+"
    + _LEAN_OPEN_NAME_RE
    + r")*\s+in\b"
)


def _is_safe_leading_open_command(text: str) -> bool:
    if _SAFE_LEADING_OPEN_RE.fullmatch(text) is None:
        return False
    names_text = re.sub(r"^open(?:\s+scoped)?\s+", "", text, count=1)
    names = re.findall(_LEAN_OPEN_NAME_RE, names_text)
    return bool(names and all(name != "in" for name in names))


def _partition_redundant_preamble_commands(src: str) -> Tuple[str, List[str]]:
    """Remove safe leading imports and retain the semantics of leading opens.

    Imports are genuinely redundant because the verifier supplies the frozen
    benchmark preamble.  An ``open`` command is different: it changes name
    resolution in the submitted proof and therefore cannot be discarded.  We
    collect conservative, command-only ``open`` lines so the proof extractor
    can replay them as term-local scopes.  Any line containing extra syntax
    (for example ``open X in #eval ...``) is left in the source and reaches the
    normal forbidden-command policy instead of being silently erased.
    """
    lines = (src or "").splitlines()
    masked_lines = _strip_lean_comments(src or "").splitlines()
    out: List[str] = []
    open_commands: List[str] = []
    in_preamble = True
    for line_index, line in enumerate(lines):
        # A trailing Lean comment is not part of the command.  Classify the
        # lexically stripped surface so ``open Set -- interval notation`` is
        # retained as the exact local scope ``open Set`` instead of being
        # misrouted to the forbidden-command lane.
        masked_line = (
            masked_lines[line_index]
            if line_index < len(masked_lines)
            else ""
        )
        command_text = masked_line.strip()
        if not in_preamble:
            out.append(line)
            continue
        if in_preamble and _SAFE_LEADING_IMPORT_RE.fullmatch(command_text):
            continue
        if in_preamble and _is_safe_leading_open_command(command_text):
            open_commands.append(command_text)
            continue
        if in_preamble and not command_text:
            # Leading comments/blank lines carry no proof semantics.  Drop
            # them as a unit while still in the preamble: retaining an opening
            # block-comment line but stripping a later ``-/ open Set`` line
            # would manufacture an unterminated comment in the extracted
            # source.
            continue
        in_preamble = False
        # When the first real command shares a line with the end of a leading
        # block comment, publish only its lexically visible code.  Later lines
        # are preserved byte-for-byte, including proof-body comments.
        first_code_index = len(masked_line) - len(masked_line.lstrip())
        closes_leading_comment = "-/" in line[:first_code_index]
        out.append(command_text if closes_leading_comment else line)
    return "\n".join(out).strip(), open_commands


def _strip_redundant_preamble_commands(src: str) -> str:
    """Drop safe leading imports/opens for command-oriented extraction.

    Proof extraction uses :func:`_partition_redundant_preamble_commands`
    directly and restores collected ``open`` commands as local proof scopes.
    Other command scanners only need the preamble-free source.
    """

    stripped, _open_commands = _partition_redundant_preamble_commands(src)
    return stripped


def _scope_proof_with_open_commands(
    proof: Optional[str], open_commands: Sequence[str]
) -> Optional[str]:
    """Replay safe leading ``open`` commands inside an extracted proof term."""

    text = str(proof or "").strip()
    commands = [str(command or "").strip() for command in open_commands]
    commands = [command for command in commands if command]
    if not text or not commands:
        return proof

    scope_lines = [f"  {command} in" for command in commands]
    if text.startswith("by") and (
        len(text) == 2 or text[2].isspace()
    ):
        body = textwrap.dedent(text[2:].lstrip("\r\n"))
        body_lines = body.splitlines()
        indented_body = [f"  {line}" if line else "" for line in body_lines]
        return "\n".join(["by", *scope_lines, *indented_body]).strip()

    # Declaration bodies may be term-mode rather than tactic-mode.  Keep the
    # resulting artifact proof-shaped while putting the exact term under the
    # same nested local-open scope used for tactic proofs.
    term_lines = text.splitlines()
    indented_term = [f"    {line}" if line else "" for line in term_lines]
    return "\n".join(
        ["by", *scope_lines, "  exact (", *indented_term, "  )"]
    )


def _scope_helper_with_open_commands(
    helper: str,
    open_commands: Sequence[str],
) -> str:
    """Replay leading ``open`` commands around a helper declaration.

    Leading opens scope every command in the original fenced block, not only
    its final proof.  Lean's command grammar supports the same nested
    ``open ... in`` form, so keep extracted helpers self-contained instead of
    silently changing how their statements and bodies resolve names.
    """

    text = str(helper or "").strip()
    commands = [str(command or "").strip() for command in open_commands]
    commands = [command for command in commands if command]
    if not text or not commands:
        return text
    body_lines = text.splitlines()
    scoped_lines = [f"  {command} in" for command in commands]
    indented_body = [f"  {line}" if line else "" for line in body_lines]
    return "\n".join([*scoped_lines, *indented_body]).strip()


def _is_local_open_scoped_proof(src: str) -> bool:
    """Return whether ``src`` is a proof term under nested local opens."""

    text = str(src or "").strip()
    masked = _strip_lean_comments_and_strings(text)
    offset = 0
    saw_open = False
    while True:
        match = _LOCAL_OPEN_TERM_PREFIX_RE.match(masked[offset:])
        if match is None:
            break
        saw_open = True
        offset += match.end()
        while offset < len(masked) and masked[offset].isspace():
            offset += 1
    remainder = text[offset:]
    if _FORBIDDEN_LEAN_COMMAND_RE.match(remainder):
        return False
    return bool(saw_open and _is_plausible_main_proof(remainder))


def _is_local_open_scoped_helper(src: str) -> bool:
    """Return whether nested local opens terminate in a helper declaration."""

    text = str(src or "").strip()
    masked = _strip_lean_comments_and_strings(text)
    offset = 0
    saw_open = False
    while True:
        match = _LOCAL_OPEN_TERM_PREFIX_RE.match(masked[offset:])
        if match is None:
            break
        saw_open = True
        offset += match.end()
        while offset < len(masked) and masked[offset].isspace():
            offset += 1
    return bool(saw_open and helper_decl_kind(text[offset:]))


def _strip_balanced_outer_proof_parentheses(text: str) -> str:
    """Peel only parentheses that enclose one complete candidate term.

    This is a classifier; the extractor still returns the original bytes.
    Strings and comments are blanked with length preserved so delimiters in
    non-code text cannot manufacture an outer wrapper.
    """

    raw = str(text or "")
    masked = _strip_lean_comments_and_strings(raw)
    left = 0
    right = len(raw)
    while True:
        while left < right and masked[left].isspace():
            left += 1
        while right > left and masked[right - 1].isspace():
            right -= 1
        if right - left < 2 or masked[left] != "(" or masked[right - 1] != ")":
            break
        depth = 0
        closes_at_end = False
        for index in range(left, right):
            token = masked[index]
            if token == "(":
                depth += 1
            elif token == ")":
                depth -= 1
                if depth < 0:
                    return raw[left:right].strip()
                if depth == 0:
                    closes_at_end = index == right - 1
                    break
        if not closes_at_end:
            break
        left += 1
        right -= 1
    return raw[left:right].strip()


def _is_plausible_main_proof(
    proof: Optional[str], *, _allow_symbolic_expression: bool = False
) -> bool:
    """Return whether an extracted candidate looks like a Lean proof expression."""
    if not proof:
        return False
    original = _strip_lean_comments_and_strings(str(proof)).strip()
    if original == "()":
        return True
    s = _strip_balanced_outer_proof_parentheses(original)
    if not s:
        return False
    if s.startswith("⟨") and s.endswith("⟩"):
        return bool(s[1:-1].strip())
    lowered = s.lower()
    head = lowered.split(None, 1)[0]
    if head == "fun":
        return "=>" in s or "↦" in s
    if head == "show":
        return bool(re.search(r"\bfrom\b", s))
    if head == "calc":
        return ":=" in s
    if head == "match":
        return bool(re.search(r"\bwith\b", s))
    if head in {"rfl", "trivial"}:
        return s == head
    if head == "have":
        return False
    if head == "if":
        words = set(re.findall(r"[A-Za-z]+", lowered))
        return (
            "then" in words
            and "else" in words
            and not words.intersection(_PLAUSIBLE_PROOF_CHATTER_WORDS)
        )
    if head == "let":
        return ":=" in s and (";" in s or "\n" in s)
    if head == "nomatch":
        return bool(re.fullmatch(r"nomatch\s+\S+", s))
    if head == "do":
        body = s[2:].strip()
        body_head = body.split(None, 1)[0].lower() if body else ""
        return "←" in body or "<-" in body or body_head in {
            "exact",
            "pure",
            "return",
        }
    if head == "by":
        body = s[2:].strip()
        if not body:
            return False
        if body.startswith("·"):
            for line in body.splitlines():
                line_body = line.strip().removeprefix("·").strip()
                if not line_body:
                    continue
                line_atoms = _split_plausible_lean_atoms(line_body)
                if not line_atoms:
                    return False
                line_head = line_atoms[0].lower().rstrip("!?;")
                if line_head in _PLAUSIBLE_PROOF_CHATTER_HEADS:
                    return False
            return True
        body_atoms = _split_plausible_lean_atoms(body)
        if not body_atoms:
            return False
        body_head = body_atoms[0].lower().rstrip("!?;")
        if body_head in _PLAUSIBLE_PROOF_CHATTER_HEADS:
            return False
        return bool(
            re.fullmatch(
                rf"(?:{_PLAUSIBLE_LEAN_IDENT_START}[\w'.]*|«[^»]+»)(?:[!?])?",
                body_atoms[0],
            )
        )
    atoms = _split_plausible_lean_atoms(s)
    if not atoms:
        return False
    atom_pattern = re.compile(
        rf"@?{_PLAUSIBLE_LEAN_IDENT}"
        rf"(?:\.(?:{_PLAUSIBLE_LEAN_IDENT}|\d+|\{{[^}}]+\}}))*|"
        r"«[^»]+»|_|\d+"
    )
    operator_pattern = re.compile(
        r"▸|∘|::|\$|\|>|<\||<;>"
    )
    for atom in atoms:
        if atom_pattern.fullmatch(atom) or operator_pattern.fullmatch(atom):
            continue
        if _allow_symbolic_expression and _is_plausible_lean_symbolic_atom(
            atom, atom_pattern
        ):
            continue
        if atom.startswith("(") and atom.endswith(")"):
            inner = atom[1:-1].strip()
            if not (
                _is_plausible_main_proof(
                    inner, _allow_symbolic_expression=True
                )
                or any(marker in inner for marker in (":", ":=", ","))
            ):
                return False
            continue
        if atom.startswith("{") and atom.endswith("}"):
            if ":=" not in atom and ":" not in atom:
                return False
            continue
        if atom.startswith("[") and atom.endswith("]"):
            continue
        return False
    normalized_head = (
        atoms[0].lstrip("@").split(".", 1)[0].lower().rstrip("!?;")
    )
    return (
        normalized_head not in _PLAUSIBLE_PROOF_CHATTER_HEADS
        and _has_plausible_lean_proof_head(atoms)
    )


def _split_plausible_lean_atoms(text: str) -> Optional[List[str]]:
    """Split top-level Lean atoms while retaining nested argument groups."""

    pairs = {"(": ")", "[": "]", "{": "}", "«": "»"}
    closing = set(pairs.values())
    stack: List[str] = []
    atoms: List[str] = []
    start: Optional[int] = None
    for index, token in enumerate(text):
        if token.isspace() and not stack:
            if start is not None:
                atoms.append(text[start:index])
                start = None
            continue
        if start is None:
            start = index
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or stack.pop() != token:
                return None
    if stack:
        return None
    if start is not None:
        atoms.append(text[start:])
    return atoms


def _append_lean_padding(out: List[str], ch: str) -> None:
    # Preserve the original newline spelling as well as byte/character
    # positions.  Mapping both halves of CRLF to ``\n`` makes ``splitlines``
    # see two masked lines for every one source line, which misaligns callers
    # that compare the masked and original sources line-by-line.
    out.append(ch if ch in "\r\n" else " ")


def _lean_char_literal_end(src: str, start: int) -> int:
    if start >= len(src) or src[start] != "'":
        return start
    if start + 2 < len(src) and src[start + 2] == "'":
        return start + 3
    if start + 3 < len(src) and src[start + 1] == "\\" and src[start + 3] == "'":
        return start + 4
    return start


def _lean_quoted_identifier_end(src: str, start: int) -> int:
    """Return the exclusive end of a Lean ``«quoted identifier»`` token."""

    if start >= len(src) or src[start] != "«":
        return start
    end = src.find("»", start + 1)
    return len(src) if end < 0 else end + 1


def _lean_raw_string_end(src: str, start: int) -> int:
    """Return the exclusive end of a Lean raw string, or *start*."""

    if start >= len(src) or src[start] != "r":
        return start
    quote_index = start + 1
    while quote_index < len(src) and src[quote_index] == "#":
        quote_index += 1
    if quote_index >= len(src) or src[quote_index] != '"':
        return start
    terminator = '"' + src[start + 1 : quote_index]
    end = src.find(terminator, quote_index + 1)
    return len(src) if end < 0 else end + len(terminator)


def _consume_lean_raw_string(
    src: str,
    start: int,
    out: List[str],
    *,
    strip_strings: bool,
) -> int:
    end = _lean_raw_string_end(src, start)
    if end <= start:
        return start
    while start < end:
        if strip_strings:
            _append_lean_padding(out, src[start])
        else:
            out.append(src[start])
        start += 1
    return end


def _lean_interpolated_string_quote_index(src: str, start: int) -> Optional[int]:
    n = len(src)
    if start >= n or not (src[start].isalpha() or src[start] == "_"):
        return None
    i = start + 1
    while i < n and (src[i].isalnum() or src[i] == "_"):
        i += 1
    if i + 1 < n and src[i] == "!" and src[i + 1] == '"':
        return i + 1
    return None


def _consume_lean_string(
    src: str,
    start: int,
    out: List[str],
    *,
    strip_strings: bool,
    preserve_interpolations: bool = False,
) -> int:
    n = len(src)
    if start >= n:
        return start
    if strip_strings:
        _append_lean_padding(out, src[start])
    else:
        out.append(src[start])
    i = start + 1
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if (
            strip_strings
            and preserve_interpolations
            and ch == "{"
            and nxt != "{"
        ):
            out.append(ch)
            i = _consume_lean_interpolation_expr(
                src,
                i + 1,
                out,
                strip_strings=strip_strings,
                preserve_interpolations=preserve_interpolations,
            )
            continue
        if strip_strings:
            _append_lean_padding(out, ch)
        else:
            out.append(ch)
        i += 1
        if ch == "\\" and i < n:
            escaped = src[i]
            if strip_strings:
                _append_lean_padding(out, escaped)
            else:
                out.append(escaped)
            i += 1
            continue
        if ch == '"':
            break
    return i


def _consume_lean_interpolation_expr(
    src: str,
    start: int,
    out: List[str],
    *,
    strip_strings: bool,
    preserve_interpolations: bool,
) -> int:
    i = start
    n = len(src)
    depth = 0
    while i < n:
        raw_end = _lean_raw_string_end(src, i)
        if raw_end > i:
            i = _consume_lean_raw_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
            )
            continue
        quote_index = _lean_interpolated_string_quote_index(src, i)
        if quote_index is not None:
            while i < quote_index:
                out.append(src[i])
                i += 1
            i = _consume_lean_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
                preserve_interpolations=preserve_interpolations,
            )
            continue

        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        quoted_end = _lean_quoted_identifier_end(src, i)
        if quoted_end > i:
            out.extend(src[i:quoted_end])
            i = quoted_end
            continue

        char_end = _lean_char_literal_end(src, i)
        if char_end > i:
            while i < char_end:
                if strip_strings:
                    _append_lean_padding(out, src[i])
                else:
                    out.append(src[i])
                i += 1
            continue

        if ch == '"':
            i = _consume_lean_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
                preserve_interpolations=preserve_interpolations,
            )
            continue

        if ch == "-" and nxt == "-":
            i += 2
            out.extend("  ")
            while i < n and src[i] not in "\r\n":
                _append_lean_padding(out, src[i])
                i += 1
            continue

        if ch == "/" and nxt == "-":
            depth_comment = 0
            while i < n:
                ch = src[i]
                nxt = src[i + 1] if i + 1 < n else ""
                if ch == "/" and nxt == "-":
                    depth_comment += 1
                    out.extend("  ")
                    i += 2
                    continue
                if ch == "-" and nxt == "/" and depth_comment > 0:
                    depth_comment -= 1
                    out.extend("  ")
                    i += 2
                    if depth_comment == 0:
                        break
                    continue
                _append_lean_padding(out, ch)
                i += 1
            continue

        if ch == "{":
            depth += 1
            out.append(ch)
            i += 1
            continue

        if ch == "}":
            out.append(ch)
            i += 1
            if depth == 0:
                return i
            depth -= 1
            continue

        out.append(ch)
        i += 1
    return i


def _scan_lean_comments(
    src: str,
    *,
    strip_strings: bool = False,
    preserve_interpolations: bool = False,
) -> Tuple[str, List[str]]:
    """Strip Lean comments while respecting strings; optionally blank strings."""
    if not src:
        return "", []
    out: List[str] = []
    comments: List[str] = []
    i = 0
    n = len(src)
    while i < n:
        raw_end = _lean_raw_string_end(src, i)
        if raw_end > i:
            i = _consume_lean_raw_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
            )
            continue
        quote_index = _lean_interpolated_string_quote_index(src, i)
        if quote_index is not None:
            token_start = i
            if not preserve_interpolations:
                # Even when the caller wants the *whole* interpolated string
                # masked/preserved, we must parse its interpolation braces to
                # find the real outer closing quote.  A nested string such as
                # ``s!"x {"#check Nat"}"`` otherwise makes the first inner
                # quote look like the end of the outer string and leaks its
                # remaining text back into policy scanners.
                scratch: List[str] = []
                token_end = _consume_lean_string(
                    src,
                    quote_index,
                    scratch,
                    strip_strings=True,
                    preserve_interpolations=True,
                )
                if strip_strings:
                    while i < token_end:
                        _append_lean_padding(out, src[i])
                        i += 1
                else:
                    out.extend(src[token_start:token_end])
                    i = token_end
                continue
            while i < quote_index:
                if strip_strings:
                    _append_lean_padding(out, src[i])
                else:
                    out.append(src[i])
                i += 1
            i = _consume_lean_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
                preserve_interpolations=preserve_interpolations,
            )
            continue

        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        quoted_end = _lean_quoted_identifier_end(src, i)
        if quoted_end > i:
            out.extend(src[i:quoted_end])
            i = quoted_end
            continue

        char_end = _lean_char_literal_end(src, i)
        if char_end > i:
            while i < char_end:
                if strip_strings:
                    _append_lean_padding(out, src[i])
                else:
                    out.append(src[i])
                i += 1
            continue

        if ch == '"':
            i = _consume_lean_string(
                src,
                i,
                out,
                strip_strings=strip_strings,
                preserve_interpolations=preserve_interpolations,
            )
            continue

        if ch == "-" and nxt == "-":
            comment_start = i + 2
            i += 2
            out.extend("  ")
            while i < n and src[i] not in "\r\n":
                _append_lean_padding(out, src[i])
                i += 1
            comments.append(src[comment_start:i])
            continue

        if ch == "/" and nxt == "-":
            body: List[str] = []
            depth = 0
            while i < n:
                ch = src[i]
                nxt = src[i + 1] if i + 1 < n else ""
                if ch == "/" and nxt == "-":
                    if depth > 0:
                        body.extend("  ")
                    depth += 1
                    out.extend("  ")
                    i += 2
                    continue
                if ch == "-" and nxt == "/" and depth > 0:
                    depth -= 1
                    if depth > 0:
                        body.extend("  ")
                    out.extend("  ")
                    i += 2
                    if depth == 0:
                        break
                    continue
                body.append(ch)
                _append_lean_padding(out, ch)
                i += 1
            comments.append("".join(body))
            continue

        out.append(ch)
        i += 1
    return "".join(out), comments


def _strip_lean_comments(src: str) -> str:
    """Best-effort removal of Lean comments while preserving string literals."""
    stripped, _comments = _scan_lean_comments(src, strip_strings=False)
    return stripped


def _strip_lean_comments_and_strings(
    src: str,
    *,
    preserve_interpolations: bool = False,
) -> str:
    """Blank non-code strings/comments before syntactic policy scans."""
    stripped, _comments = _scan_lean_comments(
        src,
        strip_strings=True,
        preserve_interpolations=preserve_interpolations,
    )
    return stripped


def _lean_comment_text(src: str) -> str:
    """Best-effort extraction of Lean line/block comments for policy checks."""
    _stripped, comments = _scan_lean_comments(src, strip_strings=False)
    return "\n".join(comments)


def _non_code_response_text(text: str) -> str:
    """Return assistant prose outside fenced code blocks for policy scans."""

    raw = str(text or "")
    if "```" not in raw:
        return raw
    out: List[str] = []
    i = 0
    n = len(raw)
    while i < n:
        start = raw.find("```", i)
        if start < 0:
            out.append(raw[i:])
            break
        out.append(raw[i:start])
        fence_len = 3
        while start + fence_len < n and raw[start + fence_len] == "`":
            fence_len += 1
        fence = "`" * fence_len
        end = raw.find(fence, start + fence_len)
        if end < 0:
            break
        i = end + fence_len
    return "\n".join(part for part in out if part)


def _bracketed_tactic_uses_non_placeholder_identifier(compact: str) -> bool:
    match = _BRACKETED_STITCHING_TACTIC_RE.fullmatch(compact)
    if not match:
        return False
    args = str(match.group(1) or "")
    identifiers = [
        ident
        for ident in _LEAN_IDENTIFIER_RE.findall(args)
        if ident.lower() not in _LEAN_TACTIC_ARG_WORDS
    ]
    if not identifiers:
        return False
    return all(
        _SOLUTION_PLACEHOLDER_IDENTIFIER_RE.fullmatch(ident) is None
        for ident in identifiers
    )


def _is_noop_root_proof(proof: Optional[str]) -> bool:
    code = _strip_lean_comments(str(proof or "")).strip()
    if not code:
        return False
    compact = " ".join(line.strip() for line in code.splitlines() if line.strip())
    if _bracketed_tactic_uses_non_placeholder_identifier(compact):
        return False
    if _NOOP_ROOT_PROOF_RE.fullmatch(compact):
        return True
    if not compact.startswith("by"):
        return False
    if not re.search(r"\b(?:simpa|simp|rfl|trivial|aesop)\b", compact):
        return False
    if re.search(
        r"\b(?:have|suffices|calc|constructor|refine|apply|exact\s+\w|"
        r"induction|obtain|rcases|cases|let|set|choose|use|existsi|"
        r"funext|ext)\b",
        compact,
    ):
        return False
    if len(compact) <= 180:
        return True
    if _SOLUTION_PLACEHOLDER_IDENTIFIER_RE.search(compact):
        return True
    return bool(re.search(r"\b(?:intro|intros|rintro|classical|subst|unfold)\b", compact))


def _durable_subgoal_helper_names(helpers: Sequence[str]) -> List[str]:
    names: List[str] = []
    for helper in helpers:
        text = str(helper or "").strip()
        if not text:
            continue
        decl_match = re.search(
            r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
            r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b",
            text,
        )
        if not decl_match:
            continue
        name = decl_match.group(1)
        if re.fullmatch(r"putnam_\d{4}_[ab]\d+(?:_solution)?", name):
            continue
        if name.endswith("_solution"):
            continue
        names.append(name)
    return names


def _has_durable_subgoal_helper(
    helpers: Sequence[str],
    proof: Optional[str],
) -> bool:
    names = _durable_subgoal_helper_names(helpers)
    if not names:
        return False
    if proof is None:
        return True
    proof_code = _strip_lean_comments(str(proof or ""))
    for name in names:
        pattern = (
            r"(?<![A-Za-z0-9_'.])"
            + re.escape(name)
            + r"(?![A-Za-z0-9_'.])"
        )
        if re.search(pattern, proof_code):
            return True
    return False


def _detect_known_answer_no_construction_collapse(
    llm_output: str,
    helpers: Sequence[str],
    proof: Optional[str],
    *,
    goal_statement: str = "",
) -> Optional[Dict[str, str]]:
    """Detect defeat commentary plus no durable construction/no-op root proof."""

    if _has_durable_subgoal_helper(helpers, proof):
        return None
    response_match = _CONSTRUCTION_COLLAPSE_RE.search(
        _non_code_response_text(str(llm_output or ""))
    )
    proof_code = _strip_lean_comments(str(proof or ""))
    solution_placeholder_match = re.search(
        r"\bputnam_\d{4}_[ab]\d+_solution\b",
        proof_code,
    )
    collapse_match = response_match
    if proof is None:
        collapse_match = response_match
        if collapse_match is None:
            return None
        return {
            "reason": "known-answer/no-construction collapse: defeat commentary without a Lean proof",
            "match": collapse_match.group(0),
        }
    if not _is_noop_root_proof(proof):
        return None
    if collapse_match is None and solution_placeholder_match is None:
        return None
    match_text = (
        collapse_match.group(0)
        if collapse_match is not None
        else solution_placeholder_match.group(0)
    )
    goal_size = len(str(goal_statement or ""))
    return {
        "reason": (
            "known-answer/no-construction collapse: no helper lemmas and a "
            f"no-op root proof for a {goal_size}-character goal"
        ),
        "match": match_text,
    }


def _helper_decl_name(helper: str) -> Optional[str]:
    """Extract the declared name from a top-level helper declaration."""
    return helper_decl_name((helper or "").strip())


def _helper_referenced_names(
    src: str,
    names: Sequence[str],
    *,
    skip: Optional[str] = None,
) -> Set[str]:
    scan_src = _strip_lean_comments_and_strings(
        src,
        preserve_interpolations=True,
    )
    return lean_referenced_helper_names(
        scan_src,
        names,
        skip=skip,
        allow_arbitrary_dot_methods=True,
    )


def _helpers_referenced_by_proof(helpers: List[str], proof: str) -> List[str]:
    """Keep only cross-fence helpers whose declared names the proof mentions."""
    if not helpers or not proof:
        return []
    names_in_order: List[str] = []
    latest_helper_by_name: Dict[str, str] = {}
    for helper in helpers:
        name = _helper_decl_name(helper)
        if not name:
            continue
        names_in_order.append(name)
        latest_helper_by_name[name] = helper
    if not names_in_order:
        return []

    # Duplicate helper names across fences otherwise produce duplicate Lean
    # declarations. Use the last definition the model wrote, but dependency-sort
    # the selected helper set before returning so a later correction of ``h_a``
    # does not move ``h_a`` after a helper body that references it.
    seen: set[str] = set()
    unique_names: List[str] = []
    for name in names_in_order:
        if name in seen:
            continue
        seen.add(name)
        unique_names.append(name)

    def referenced_names(src: str, *, skip: Optional[str] = None) -> set[str]:
        return _helper_referenced_names(src, unique_names, skip=skip)

    selected = referenced_names(proof)
    changed = True
    while changed:
        changed = False
        for name in unique_names:
            if name not in selected:
                continue
            helper = latest_helper_by_name[name]
            deps = referenced_names(helper, skip=name)
            new_deps = deps - selected
            if new_deps:
                selected.update(new_deps)
                changed = True

    out: List[str] = []
    for name in unique_names:
        if name in selected:
            out.append(latest_helper_by_name[name])
    return _dedupe_helpers_by_name_last_wins(out)


def _dedupe_helpers_by_name_last_wins(helpers: List[str]) -> List[str]:
    return dedupe_helpers_by_name_last_wins(helpers)


# Strip leading block comments at the start of a line (no indent), so a
# top-level forbidden command hidden behind ``/- harmless -/ #eval`` is
# still detected before the forbidden-command scan. Indented body lines keep
# their indent so the local ``open ... in`` exception can distinguish them.
_LEADING_BLOCK_COMMENT_RE = re.compile(r"(?m)^(?:/-[\s\S]*?-/\s*)+")


def _find_forbidden_lean_command(helpers: List[str], proof: str) -> Optional[str]:
    """Reject top-level commands that can inspect/leak the concrete Lean env."""
    src = "\n\n".join([*helpers, proof])
    # Pre-strip ONLY block comments that begin at column 0 of a line. This
    # lets the column-0 anchor in ``_FORBIDDEN_LEAN_COMMAND_RE`` catch
    # ``/- comment -/ #eval ...`` (originally top-level, hidden behind a
    # comment) without false-firing on indented body lines such as
    # ``  open Real in <expr>`` (legitimate Lean 4 term-level open).
    src = _LEADING_BLOCK_COMMENT_RE.sub("", src)
    stripped = _strip_lean_comments_and_strings(src)
    for match in _FORBIDDEN_LEAN_COMMAND_RE.finditer(stripped):
        command = match.group(1)
        if command == "open" and _is_local_open_scoped_proof(
            stripped[match.start(1) :]
        ):
            continue
        leading = stripped[match.start() : match.start(1)]
        line_end = stripped.find("\n", match.end())
        if line_end < 0:
            line_end = len(stripped)
        tail = stripped[match.end() : line_end]
        in_match = re.search(r"\bin\b", tail)
        dangerous_open_body = bool(
            in_match
            and _FORBIDDEN_LEAN_COMMAND_RE.match(tail[in_match.end() :])
        )
        if command == "open" and in_match and not dangerous_open_body:
            operand = (
                tail[in_match.end() :]
                + "\n"
                + stripped[line_end + 1 :]
            ).lstrip()
            safe_scoped_operand = bool(
                leading
                or _is_local_open_scoped_proof(
                    stripped[match.start(1) :]
                )
                or _is_local_open_scoped_helper(
                    stripped[match.start(1) :]
                )
                or re.match(
                    r"^(?:@\[[^\]]*\]\s*)*"
                    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
                    r"(?:theorem|lemma|def|abbrev|instance)\b",
                    operand,
                )
            )
            if safe_scoped_operand:
                continue
        return command
    return None


def _is_main_proof_chunk(chunk: str) -> bool:
    """Return whether a top-level chunk is the submitted main proof."""
    s = (chunk or "").strip()
    if not s:
        return False
    if _extract_example_body(s) is not None:
        return True
    return s.startswith("by") and _is_plausible_main_proof(s)


def _find_post_main_helper_declarations(chunks: List[str]) -> List[str]:
    """Return helper names that appear after a main proof chunk.

    The extractor contract is helpers first, final proof last. When the model
    violates that ordering inside one fenced block, the older splitter treated
    the earlier proof as a helper and returned ``proof=None``. Detecting this
    shape lets the retry prompt name the ordering problem directly.
    """
    saw_main = False
    out: List[str] = []
    for chunk in chunks:
        s = (chunk or "").strip()
        if not s:
            continue
        if _is_main_proof_chunk(s):
            saw_main = True
            continue
        if not saw_main:
            continue
        name = _helper_decl_name(s)
        if name:
            out.append(name)
    return out


def _find_extra_main_proof_chunks(chunks: List[str]) -> List[str]:
    """Return non-final main-proof-shaped chunks that the parser silently
    demotes to anonymous helpers.

    The extractor uses the LAST main-proof-shaped chunk (``example : ... :=
    <body>`` or bare ``by ...``) as the submitted proof; every chunk before
    it goes into the ``lemma_block`` so Lean compiles them as anonymous
    declarations. ``_find_post_main_helper_declarations`` flags only
    *named* helpers after the main proof — so a reply containing two
    ``example`` blocks (or two bare ``by`` blocks) routes around it: both
    chunks are main-proof-shaped but anonymous.

    This detector returns first-line excerpts of the demoted chunks so the
    run loop can issue a targeted "you submitted multiple main proofs"
    nudge instead of letting Lean see a pair of competing examples.
    """
    main_indexes = [
        i
        for i, c in enumerate(chunks)
        if _is_main_proof_chunk((c or "").strip())
    ]
    if len(main_indexes) <= 1:
        return []
    extras: List[str] = []
    for i in main_indexes[:-1]:
        s = (chunks[i] or "").strip()
        if not s:
            continue
        first_line = s.splitlines()[0].strip()
        if not first_line:
            continue
        extras.append(first_line[:120])
    return extras


def _salvage_small_multiple_main_submission(
    helpers: Sequence[str],
    proof: Optional[str],
    chunks: Sequence[str],
    *,
    max_extra_mains: int = 2,
) -> tuple[List[str], Optional[str], int]:
    """Normalize a small multiple-main reply to its final main proof.

    The public extraction contract is last-main-wins, but replies containing
    multiple fences can cause the legacy extractor to return the first proof
    while the ambiguity detector observes all fences.  Normalize from the
    already-tokenized chunks so both callers execute the same documented
    candidate.  Earlier ``example``/bare-``by`` chunks are anonymous and
    therefore cannot be referenced by the final proof; dropping them cannot
    remove a usable declaration.

    Returns ``(helpers, proof, dropped_count)``.  Zero means no salvage was
    performed (including the deliberately hard-rejected thrashing case).
    """

    normalized_chunks = [str(chunk or "").strip() for chunk in chunks]
    main_indexes = [
        index
        for index, chunk in enumerate(normalized_chunks)
        if _is_main_proof_chunk(chunk)
    ]
    extra_count = max(0, len(main_indexes) - 1)
    if extra_count <= 0 or extra_count > max(0, int(max_extra_mains)):
        return list(helpers), proof, 0

    final_index = main_indexes[-1]
    final_chunk = normalized_chunks[final_index]
    final_proof = _extract_example_body(final_chunk)
    if final_proof is None and final_chunk.startswith("by"):
        final_proof = final_chunk
    if not final_proof or not _is_plausible_main_proof(final_proof):
        return list(helpers), proof, 0

    # Preserve policy-bearing non-main inputs already surfaced by extraction,
    # then recover every named declaration that precedes the selected final
    # main across all fences.  Never carry anonymous earlier main chunks.
    kept_helpers = [
        str(helper or "").strip()
        for helper in helpers
        if str(helper or "").strip()
        and not _is_main_proof_chunk(str(helper or "").strip())
    ]
    for chunk in normalized_chunks[:final_index]:
        if _is_main_proof_chunk(chunk):
            continue
        if helper_decl_name(chunk) and helper_decl_body(chunk):
            kept_helpers.append(chunk)
    return _dedupe_helpers_by_name_last_wins(kept_helpers), final_proof, extra_count


_LEAN_UNQUOTED_NAME_SEGMENT_PATTERN = r"(?:[^\W\d]|_)[\w']*"
_LEAN_NAME_SEGMENT_PATTERN = (
    rf"(?:«[^»]*»|{_LEAN_UNQUOTED_NAME_SEGMENT_PATTERN})"
)
_LEAN_QUALIFIED_NAME_PATTERN = (
    rf"{_LEAN_NAME_SEGMENT_PATTERN}(?:\.{_LEAN_NAME_SEGMENT_PATTERN})*"
)
_LEAN_QUALIFIED_NAME_RE = re.compile(_LEAN_QUALIFIED_NAME_PATTERN)
_LEAN_SCOPE_ARGUMENT_PATTERN = (
    rf"{_LEAN_QUALIFIED_NAME_PATTERN}"
    rf"(?:[ \t]+{_LEAN_QUALIFIED_NAME_PATTERN})*"
)

_PREAMBLE_DECL_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "opaque",
    "constant",
    "instance",
    "structure",
    "inductive",
    "class",
    "axiom",
}
_PREAMBLE_DECL_MODIFIERS = {
    "public",
    "private",
    "protected",
    "local",
    "noncomputable",
    "unsafe",
    "partial",
}


class _StructuralDeclarationMatch:
    """Small re.Match-compatible declaration header produced structurally."""

    def __init__(
        self,
        *,
        source: str,
        start: int,
        token_start: int,
        end: int,
        name: str,
        kind: str,
        has_attributes: bool,
        modifiers: Tuple[str, ...],
    ) -> None:
        self._source = source
        self._start = start
        self.token_start = token_start
        self._end = end
        self.name = name
        self.kind = kind
        self.has_attributes = has_attributes
        self.modifiers = modifiers

    def start(self) -> int:
        return self._start

    def end(self) -> int:
        return self._end

    def group(self, index: int = 0) -> str:
        if index == 0:
            return self._source[self._start : self._end]
        if index == 1:
            return self.name
        if index == 2:
            return self.kind
        raise IndexError(index)


def _balanced_attribute_end(source: str, start: int) -> int:
    """Return the end of a balanced ``@[...]`` prefix, or ``-1``."""

    if not source.startswith("@[", start):
        return -1
    depth = 0
    cursor = start + 1
    while cursor < len(source):
        if source[cursor] == "«":
            quoted_end = _lean_quoted_identifier_end(source, cursor)
            if quoted_end > cursor:
                cursor = quoted_end
                continue
        char = source[cursor]
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return cursor + 1
        cursor += 1
    return -1


def _structural_preamble_declaration_matches(
    source: str,
) -> List[_StructuralDeclarationMatch]:
    """Scan declaration headers with balanced attributes and Lean names."""

    scan = str(source or "")
    matches: List[_StructuralDeclarationMatch] = []
    seen_name_starts: Set[int] = set()
    for line_match in re.finditer(r"(?m)^[ \t]*", scan):
        line_start = line_match.start()
        cursor = line_match.end()
        token_start = cursor
        has_attributes = False
        while scan.startswith("@[", cursor):
            attribute_end = _balanced_attribute_end(scan, cursor)
            if attribute_end < 0:
                cursor = -1
                break
            has_attributes = True
            cursor = attribute_end
            while cursor < len(scan) and scan[cursor].isspace():
                cursor += 1
        if cursor < 0 or cursor >= len(scan):
            continue
        modifiers: List[str] = []
        while True:
            modifier_match = re.match(
                rf"({_LEAN_UNQUOTED_NAME_SEGMENT_PATTERN})\b",
                scan[cursor:],
            )
            if (
                modifier_match is None
                or modifier_match.group(1) not in _PREAMBLE_DECL_MODIFIERS
            ):
                break
            modifiers.append(modifier_match.group(1))
            cursor += modifier_match.end()
            while cursor < len(scan) and scan[cursor].isspace():
                cursor += 1
        kind_match = re.match(
            rf"({_LEAN_UNQUOTED_NAME_SEGMENT_PATTERN})\b",
            scan[cursor:],
        )
        if (
            kind_match is None
            or kind_match.group(1) not in _PREAMBLE_DECL_KINDS
        ):
            continue
        kind = kind_match.group(1)
        cursor += kind_match.end()
        if cursor >= len(scan) or not scan[cursor].isspace():
            continue
        while cursor < len(scan) and scan[cursor].isspace():
            cursor += 1
        name_match = _LEAN_QUALIFIED_NAME_RE.match(scan, cursor)
        if name_match is None:
            continue
        if name_match.start() in seen_name_starts:
            continue
        seen_name_starts.add(name_match.start())
        matches.append(
            _StructuralDeclarationMatch(
                source=scan,
                start=line_start,
                token_start=token_start,
                end=name_match.end(),
                name=name_match.group(0),
                kind=kind,
                has_attributes=has_attributes,
                modifiers=tuple(modifiers),
            )
        )
    return matches


def _first_preamble_declaration_header(
    source: str,
) -> Optional[_StructuralDeclarationMatch]:
    matches = _structural_preamble_declaration_matches(str(source or ""))
    return matches[0] if matches else None
_LEAN_SCOPE_COMMAND_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|noncomputable)\s+)*"
    r"(namespace|section|end|open|mutual)\b"
    rf"[ \t]*({_LEAN_SCOPE_ARGUMENT_PATTERN})?"
)
_LEAN_CONTEXT_COMMAND_PREFIX_PATTERN = (
    r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:local|scoped(?:\[[^\]\r\n]*\])?)[ \t]+)?"
    r"(?:notation|infixl?|infixr|prefix|postfix|syntax|macro(?:_rules)?|"
    r"elab(?:_rules)?|declare_syntax_cat|alias|deriving|"
    r"attribute|export|variable|variables|universe|universes|"
    r"grind_pattern|unif_hint|(?:d?simproc)|builtin_(?:d?simproc)|"
    r"set_option|initialize|builtin_initialize|register_[A-Za-z0-9_]+)\b"
)
_LEAN_CONTEXT_COMMAND_RE = re.compile(
    rf"(?m)^[ \t]*{_LEAN_CONTEXT_COMMAND_PREFIX_PATTERN}"
)
_LEAN_CONTEXT_COMMAND_PREFIX_RE = re.compile(
    _LEAN_CONTEXT_COMMAND_PREFIX_PATTERN
)
_LEAN_INSTANCE_COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:public|private|protected|local|noncomputable|unsafe|partial)[ \t]+)*"
    r"instance\b"
)
_LEAN_PASSIVE_COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:example\b|#[A-Za-z_][A-Za-z0-9_]*\b|run_cmd\b)"
)


def _top_level_elaboration_context_issues(
    source: str,
) -> Tuple[Tuple[int, str], ...]:
    """Return lexical commands whose elaboration effects are not self-contained.

    The prompt-visible answer renderer can reproduce ordinary declarations and
    namespace opens structurally.  Notations, macros, attributes, options, and
    restricted/renaming opens alter elaboration without appearing as identifier
    dependencies in declaration source.  Until the registry is backed by
    elaborated ``Expr`` dependencies, their presence before an answer
    declaration must make completeness fail closed rather than silently
    promising an executable closure.

    Positions refer to the original source because the scan shadow is
    length-preserving.
    """

    scan = _strip_lean_comments_and_strings(str(source or ""))
    issues: List[Tuple[int, str]] = []
    declaration_starts = {
        match.start() + len(match.group(0)) - len(match.group(0).lstrip())
        for match in _structural_preamble_declaration_matches(scan)
    }
    for match in _LEAN_CONTEXT_COMMAND_RE.finditer(scan):
        start = match.start() + len(match.group(0)) - len(match.group(0).lstrip())
        token = match.group(0).strip().split(None, 1)[0]
        issues.append((start, f"context:{token or 'command'}"))
    for match in _LEAN_INSTANCE_COMMAND_RE.finditer(scan):
        start = match.start() + len(match.group(0)) - len(match.group(0).lstrip())
        if start not in declaration_starts:
            issues.append((start, "context:anonymous_instance"))
    for match in _LEAN_SCOPE_COMMAND_RE.finditer(scan):
        command = str(match.group(1) or "")
        if command == "mutual":
            issues.append((match.start(), "context:mutual"))
            continue
        if command != "open":
            continue
        line_end = scan.find("\n", match.start())
        if line_end < 0:
            line_end = len(scan)
        argument_tokens = {
            name_match.group(0)
            for name_match in _LEAN_QUALIFIED_NAME_RE.finditer(
                str(match.group(2) or "")
            )
        }
        unparsed_suffix = scan[match.end() : line_end].strip()
        if argument_tokens & {"scoped", "renaming", "hiding", "in"} or (
            unparsed_suffix
        ):
            issues.append((match.start(), "context:restricted_open"))
    return tuple(sorted(set(issues)))


def _split_lean_qualified_name(name: str) -> List[str]:
    """Split a Lean name at dots outside ``«quoted components»``."""

    source = str(name or "").strip()
    if not source:
        return []
    parts: List[str] = []
    start = 0
    index = 0
    while index < len(source):
        if source[index] == "«":
            end = source.find("»", index + 1)
            if end < 0:
                return []
            index = end + 1
            continue
        if source[index] == ".":
            part = source[start:index].strip()
            if not part:
                return []
            parts.append(part)
            start = index + 1
        index += 1
    tail = source[start:].strip()
    if not tail:
        return []
    parts.append(tail)
    return parts


def _normalized_decl_text_for_redeclaration_comparison(text: str) -> str:
    """Collapse cosmetic spelling so a faithful restatement compares equal."""

    stripped = _strip_lean_comments(str(text or ""))
    return " ".join(
        stripped.replace("=>", "↦").replace("->", "→").split()
    )


def _top_level_declaration_registry_with_opens(
    source: str,
) -> Tuple[
    Dict[str, str],
    Set[str],
    Dict[str, Tuple[str, ...]],
    Dict[str, int],
]:
    """Comment/string-aware map of top-level declaration name → source block.

    Returns ``(blocks, ambiguous_names, opens_by_name, positions_by_name)`` where
    ``opens_by_name`` snapshots the lexical ``open`` targets in effect at
    each declaration (for dependency resolution). Header scanning runs on the
    length-preserving comment- and string-blanked shadow of the source, so
    declaration-looking text inside block comments (nested included), line
    comments, string literals, and interpolations never registers (Sol audit
    2026-07-29 F1: a commented-out fake ``*_solution`` definition replaced the
    real value shown to the planner). Spans are then sliced from the ORIGINAL
    source, preserving exact text. A name genuinely declared more than once at
    top level is AMBIGUOUS: it is excluded from ``blocks`` so every consumer
    fails closed instead of guessing which copy is authoritative.
    """

    src = str(source or "")
    if not src:
        return {}, set(), {}, {}
    scan = _strip_lean_comments_and_strings(src)

    def token_text_start(match: "re.Match[str]") -> int:
        # ``^\s*`` can greedily span a blanked comment region in the scan
        # shadow; anchor spans at the first real token character.
        matched = match.group(0)
        return match.start() + (len(matched) - len(matched.lstrip()))

    # Namespace/section tracking (Sol audit 2026-07-29 R2): declarations are
    # registered under their FULLY QUALIFIED names, scope commands form block
    # boundaries (an intervening ``end``/``open`` never attaches to the
    # previous declaration), and same-named declarations in different
    # namespaces are distinct rather than falsely ambiguous.
    declaration_matches = _structural_preamble_declaration_matches(scan)
    tokens: List[Tuple[int, str, "re.Match[str]"]] = [
        (match.start(), "decl", match) for match in declaration_matches
    ]
    context_matches = list(_LEAN_CONTEXT_COMMAND_RE.finditer(scan))
    declaration_token_starts = {
        token_text_start(match) for match in declaration_matches
    }
    anonymous_instance_matches = [
        match
        for match in _LEAN_INSTANCE_COMMAND_RE.finditer(scan)
        if token_text_start(match) not in declaration_token_starts
    ]
    passive_command_matches = list(_LEAN_PASSIVE_COMMAND_RE.finditer(scan))

    def command_name_tokens(argument: str) -> Optional[List[str]]:
        raw = str(argument or "")
        matches = list(_LEAN_QUALIFIED_NAME_RE.finditer(raw))
        if not matches:
            return []
        names: List[str] = []
        cursor = 0
        for name_match in matches:
            if raw[cursor : name_match.start()].strip():
                return None
            names.append(name_match.group(0))
            cursor = name_match.end()
        if raw[cursor:].strip():
            return None
        return names

    scope_matches = list(_LEAN_SCOPE_COMMAND_RE.finditer(scan))

    def skip_space(cursor: int) -> int:
        while cursor < len(scan) and scan[cursor].isspace():
            cursor += 1
        return cursor

    def scoped_open_operand_start(cursor: int) -> Optional[int]:
        open_match = re.match(r"open\b", scan[cursor:])
        if open_match is None:
            return None
        cursor += open_match.end()
        while cursor < len(scan):
            cursor = skip_space(cursor)
            name_match = _LEAN_QUALIFIED_NAME_RE.match(scan, cursor)
            if name_match is None:
                return None
            if name_match.group(0) == "in":
                return name_match.end()
            cursor = name_match.end()
        return None

    def set_option_operand_start(cursor: int) -> Optional[int]:
        match = re.match(r"set_option\b[^\n]*?\bin\b", scan[cursor:])
        return None if match is None else cursor + match.end()

    def scoped_operand_wraps_following_command(
        initial_operand: Optional[int],
    ) -> bool:
        if initial_operand is None:
            return False
        cursor = skip_space(initial_operand)
        # Follow nested dual-use scoped terms to their terminal operand.
        # ``open A in open B in 7`` and
        # ``open A in set_option pp.universes true in 7`` are expressions,
        # while the same chains ending in a declaration are command wrappers.
        while cursor < len(scan):
            nested_operand = scoped_open_operand_start(cursor)
            if nested_operand is not None:
                cursor = skip_space(nested_operand)
                continue
            nested_operand = set_option_operand_start(cursor)
            if nested_operand is not None:
                cursor = skip_space(nested_operand)
                continue
            break
        if cursor >= len(scan):
            return False
        terminal_headers = _structural_preamble_declaration_matches(
            scan[cursor:]
        )
        if terminal_headers and terminal_headers[0].token_start == 0:
            return True
        for candidate in (*declaration_matches, *scope_matches):
            if candidate is match or (
                candidate in scope_matches
                and str(candidate.group(1) or "") == "open"
                and "in"
                in (
                    command_name_tokens(str(candidate.group(2) or ""))
                    or []
                )
            ):
                continue
            if token_text_start(candidate) == cursor:
                return True
        return bool(
            re.match(r"#\w+", scan[cursor:])
            or _LEAN_CONTEXT_COMMAND_PREFIX_RE.match(scan[cursor:])
        )

    def scoped_open_wraps_following_command(
        match: "re.Match[str]",
    ) -> bool:
        return scoped_operand_wraps_following_command(
            scoped_open_operand_start(token_text_start(match))
        )

    for match in context_matches:
        start = token_text_start(match)
        if (
            re.match(r"set_option\b", scan[start:])
            and set_option_operand_start(start) is not None
            and not scoped_operand_wraps_following_command(
                set_option_operand_start(start)
            )
        ):
            continue
        tokens.append((match.start(), "boundary", match))
    tokens.extend(
        (match.start(), "boundary", match)
        for match in (*anonymous_instance_matches, *passive_command_matches)
    )

    for match in scope_matches:
        command = str(match.group(1) or "")
        argument = str(match.group(2) or "")
        argument_names = command_name_tokens(argument)
        scoped_open = bool(argument_names and "in" in argument_names)
        # ``open Foo in`` is either a term expression furnishing the current
        # declaration's RHS or a scoped command wrapping the next command.
        # Indentation is not semantic in Lean, so classify it by the operand:
        # a following declaration/command means wrapper; any other expression
        # remains inside the current declaration block.
        if (
            command == "open"
            and scoped_open
            and not scoped_open_wraps_following_command(match)
        ):
            continue
        tokens.append((match.start(), "scope", match))
    tokens.sort(key=lambda item: item[0])

    # ("namespace"|"section"|"mutual", name, opens-declared-at-this-level)
    scope_stack: List[Tuple[str, str, List[str]]] = []
    root_opens: List[str] = []
    blocks: Dict[str, str] = {}
    ambiguous: Set[str] = set()
    opens_by_name: Dict[str, Tuple[str, ...]] = {}
    positions_by_name: Dict[str, int] = {}

    def current_namespace_prefix() -> str:
        return ".".join(
            entry[1]
            for entry in scope_stack
            if entry[0] == "namespace" and entry[1]
        )

    def registry_has_namespace(name: str) -> bool:
        prefix = f"{name}."
        return any(
            known == name or known.startswith(prefix)
            for known in (*blocks.keys(), *ambiguous)
        )

    def canonical_open_target(target: str) -> str:
        clean = str(target or "").strip()
        if clean.startswith("_root_."):
            # Rootedness is semantic when the declaration is later replayed
            # inside its namespace: `open A` may resolve `Outer.A`, whereas
            # `open _root_.A` must not.
            return clean
        prefix = current_namespace_prefix()
        while prefix:
            candidate = f"{prefix}.{clean}"
            if registry_has_namespace(candidate):
                return f"_root_.{candidate}"
            prefix = prefix.rsplit(".", 1)[0] if "." in prefix else ""
        return f"_root_.{clean}"

    def simple_open_targets(argument: str) -> List[str]:
        """Conservatively parse persistent, unrestricted namespace opens."""

        names = command_name_tokens(argument)
        if not names or "scoped" in names or "in" in names:
            return []
        targets: List[str] = []
        for target in names:
            targets.append(canonical_open_target(target))
        return targets

    for index, (_start, kind, match) in enumerate(tokens):
        if kind == "boundary":
            continue
        if kind == "scope":
            command = str(match.group(1) or "")
            argument = str(match.group(2) or "").strip()
            if command == "namespace" and argument:
                namespace_match = _LEAN_QUALIFIED_NAME_RE.match(argument)
                if namespace_match is not None:
                    for component in _split_lean_qualified_name(
                        namespace_match.group(0)
                    ):
                        scope_stack.append(("namespace", component, []))
            elif command == "section":
                scope_stack.append(("section", argument, []))
            elif command == "mutual":
                # ``mutual ... end`` owns its own ``end``. Without this frame,
                # that end incorrectly pops an enclosing namespace.
                scope_stack.append(("mutual", "", []))
            elif command == "end":
                end_match = _LEAN_QUALIFIED_NAME_RE.match(argument)
                end_parts = (
                    _split_lean_qualified_name(end_match.group(0))
                    if end_match is not None
                    else []
                )
                namespace_parts = [
                    frame[1]
                    for frame in scope_stack
                    if frame[0] == "namespace"
                ]
                if (
                    end_parts
                    and len(end_parts) <= len(namespace_parts)
                    and namespace_parts[-len(end_parts) :] == end_parts
                ):
                    remaining = len(end_parts)
                    while scope_stack and remaining:
                        frame = scope_stack.pop()
                        if frame[0] == "namespace":
                            remaining -= 1
                elif (
                    end_parts
                    and scope_stack
                    and scope_stack[-1][1] == ".".join(end_parts)
                ):
                    scope_stack.pop()
                elif scope_stack:
                    scope_stack.pop()
            elif command == "open" and argument:
                line_end = scan.find("\n", match.start())
                if line_end < 0:
                    line_end = len(scan)
                has_unparsed_suffix = bool(
                    scan[match.end() : line_end].strip()
                )
                targets = (
                    []
                    if has_unparsed_suffix
                    else simple_open_targets(argument)
                )
                if scope_stack:
                    scope_stack[-1][2].extend(targets)
                else:
                    root_opens.extend(targets)
            continue
        name = str(match.group(1) or "").strip()
        if not name:
            continue
        prefix = current_namespace_prefix()
        if name.startswith("_root_."):
            qualified = name[len("_root_.") :]
        else:
            qualified = f"{prefix}.{name}" if prefix else name
        end = (
            token_text_start(tokens[index + 1][2])
            if index + 1 < len(tokens)
            else len(src)
        )
        if qualified in ambiguous:
            continue
        if qualified in blocks:
            ambiguous.add(qualified)
            blocks.pop(qualified, None)
            opens_by_name.pop(qualified, None)
            positions_by_name.pop(qualified, None)
            continue
        declaration_start = token_text_start(match)
        blocks[qualified] = src[declaration_start:end].strip()
        positions_by_name[qualified] = declaration_start
        opens_by_name[qualified] = tuple(
            [*root_opens, *(o for entry in scope_stack for o in entry[2])]
        )
    return blocks, ambiguous, opens_by_name, positions_by_name


def _top_level_declaration_registry(
    source: str,
) -> Tuple[Dict[str, str], Set[str]]:
    """Unambiguous qualified declaration blocks plus ambiguous names."""

    blocks, ambiguous, _opens, _positions = (
        _top_level_declaration_registry_with_opens(source)
    )
    return blocks, ambiguous


def _preamble_declaration_blocks(preamble: str) -> Dict[str, str]:
    """Unambiguous top-level preamble declaration blocks by name."""

    blocks, _ambiguous = _top_level_declaration_registry(preamble)
    return blocks


def _partition_preamble_redeclarations(
    helpers: Sequence[str],
    preamble: str,
) -> Tuple[List[str], List[str], List[str]]:
    """Enforce the immutable-preamble compilation boundary on reply helpers.

    Returns ``(kept, redundant_names, conflicting_names)``. A helper that
    redeclares a preamble name with equivalent text (whitespace/arrow spelling
    ignored, comments stripped) is REDUNDANT: the preamble copy is
    authoritative and compiling the duplicate produces Lean "already declared"
    failures that poison otherwise valid proof bodies. A helper that
    redeclares a preamble name
    with different content is a CONFLICT: it must be rejected instead of
    silently shadowing the verification environment. Both are removed from
    the compiled helper list.
    """

    helper_list = [
        str(helper or "").strip()
        for helper in helpers
        if str(helper or "").strip()
    ]
    preamble_blocks, ambiguous_names = _top_level_declaration_registry(preamble)
    if not preamble_blocks and not ambiguous_names:
        return helper_list, [], []
    kept: List[str] = []
    redundant: List[str] = []
    conflicts: List[str] = []
    for block in helper_list:
        name = str(helper_decl_name(block) or "").strip()
        if name and name in ambiguous_names:
            # The preamble itself declares this name more than once; no
            # single copy is authoritative, so a model redeclaration cannot
            # be verified as redundant. Fail closed.
            if name not in conflicts:
                conflicts.append(name)
            continue
        if not name or name not in preamble_blocks:
            kept.append(block)
            continue
        if _normalized_decl_text_for_redeclaration_comparison(
            block
        ) == _normalized_decl_text_for_redeclaration_comparison(
            preamble_blocks[name]
        ):
            if name not in redundant:
                redundant.append(name)
        else:
            if name not in conflicts:
                conflicts.append(name)
    return kept, redundant, conflicts


def _find_helpers_after_final_main(chunks: Sequence[str]) -> List[str]:
    """Return named declarations after the selected final main proof."""

    normalized_chunks = [str(chunk or "").strip() for chunk in chunks]
    main_indexes = [
        index
        for index, chunk in enumerate(normalized_chunks)
        if _is_main_proof_chunk(chunk)
    ]
    if not main_indexes:
        return []
    out: List[str] = []
    for chunk in normalized_chunks[main_indexes[-1] + 1 :]:
        name = helper_decl_name(chunk)
        if name:
            out.append(name)
    return out


def _split_top_level_chunks(src: str) -> Tuple[str, List[str]]:
    """Split one Lean fence into leading text plus top-level declaration chunks."""
    scan_src = _strip_lean_comments_and_strings(src)
    matches: List[re.Match[str]] = []
    for match in _TOP_LEVEL_HEADER_RE.finditer(scan_src):
        kind = str(match.group(1) or "")
        previous = matches[-1] if matches else None
        if (
            kind == "by"
            and previous is not None
            and str(previous.group(1) or "") in _DECLARATION_BODY_HEADER_KINDS
        ):
            # ``theorem h : T :=\nby ...`` and ``example : T :=\nby ...`` are
            # one declaration, not a header-only declaration followed by a
            # bare root proof. Only suppress the ``by`` match when the text
            # between the previous header and this ``by`` contains a top-level
            # body separator whose body is still empty.
            prefix = scan_src[previous.start() : match.start()]
            sep_end = _find_top_level_assign(prefix)
            if sep_end >= 0 and not prefix[sep_end:].strip():
                continue
        matches.append(match)
    if not matches:
        return src.strip(), []
    leading = src[: matches[0].start()].strip()
    chunks: List[str] = []
    for i, match in enumerate(matches):
        start = match.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(src)
        chunks.append(src[start:end].strip())
    return leading, chunks


def _top_level_chunks_from_reply(llm_output: str) -> List[str]:
    """Best-effort top-level proof/helper chunks across all Lean fences."""
    chunks: List[str] = []
    for raw_src in extract_code_fences(llm_output or ""):
        src = normalize_nat_factorial_notation(
            _strip_redundant_preamble_commands(raw_src.strip())
        )
        if not src:
            continue
        _leading, structured_chunks = _split_top_level_chunks(src)
        if structured_chunks:
            chunks.extend(structured_chunks)
            continue
        candidates = extract_proof_candidates(src)
        for candidate in candidates:
            if _is_plausible_main_proof(candidate):
                chunks.append(candidate)
                break
    return chunks


def _find_top_level_assign(src: str) -> int:
    """Position AFTER the example's body separator ``:=``.

    The hard cases here are ``:=`` tokens that appear *inside the type* —
    `let x := 1; x = 1 := by ...`, `let x := 1\\n  x = 1 := by ...`
    (layout-let), `(a : Nat := 0) → ...` (default arg), etc.

    Strategy: walk paren-depth-aware (so `:=` inside `(...)` or `[...]` or
    `{...}` are skipped). Prefer the first top-level ``:=`` that's followed
    by ``by`` — our prompt tells the model to write tactic proofs starting
    with `by`, and `let x := <value>` bindings have a value (number, name,
    expr) after `:=`, not the keyword `by`. Fall back to the first top-level
    ``:=`` overall so term-mode proofs (`:= rfl`, `:= True.intro`) on a
    plain `example` still work.

    This is a heuristic, not a real Lean parser. It wins on the cases the
    PutnamBench parser tests cover (inline let, layout let, split-line let)
    without having to model Lean's full layout rules. The only contrived
    miss is `let x := by <tac>` *in the type*, where the let value itself
    starts with `by` — extremely rare.
    """
    # The comment/string masker is length-preserving, so positions found in
    # ``scan_src`` remain valid in ``src`` while non-code ``:=`` tokens cannot
    # masquerade as the declaration body separator.
    scan_src = _strip_lean_comments_and_strings(src)
    i = 0
    n = len(scan_src)
    depth = 0          # paren/bracket/brace nesting
    fallback = -1      # first top-level `:=` we see (term-mode safety net)
    while i < n:
        quoted_end = _lean_quoted_identifier_end(scan_src, i)
        if quoted_end > i:
            i = quoted_end
            continue
        c = scan_src[i]
        if c in "([{":
            depth += 1
            i += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
            i += 1
        elif depth == 0 and scan_src.startswith(":=", i):
            stripped = scan_src[i + 2 :].lstrip()
            # Word-boundary check for `by` (so `byName` and `byzantine`
            # don't accidentally match).
            if stripped.startswith("by") and (
                len(stripped) == 2
                or not (stripped[2].isalnum() or stripped[2] == "_")
            ):
                return i + 2
            if fallback < 0:
                fallback = i + 2
            i += 2
        else:
            i += 1
    return fallback


def _take_leading_example_binder_group(
    text: str,
) -> Optional[tuple[str, str, str]]:
    """Consume one balanced leading example binder group.

    The masked view keeps offsets stable but hides delimiters inside Lean
    comments, strings, and character literals.  A small delimiter stack is
    sufficient here because the caller only needs to isolate the binder, not
    parse its type.
    """

    source = str(text or "")
    masked = _strip_lean_comments_and_strings(source)
    start = len(masked) - len(masked.lstrip())
    if start >= len(masked) or masked[start] not in "({[":
        return None
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    opener = masked[start]
    stack = [pairs[opener]]
    i = start + 1
    while i < len(masked):
        quoted_end = _lean_quoted_identifier_end(masked, i)
        if quoted_end > i:
            i = quoted_end
            continue
        token = masked[i]
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or stack.pop() != token:
                return None
            if not stack:
                return opener, source[start + 1 : i], source[i + 1 :]
        i += 1
    return None


def _example_binder_name_tokens(text: str) -> Optional[list[str]]:
    """Parse a complete whitespace/comma-separated Lean binder-name prefix."""

    source = str(text or "").strip()
    if not source:
        return None
    names: list[str] = []
    index = 0
    while index < len(source):
        while index < len(source) and (
            source[index].isspace() or source[index] == ","
        ):
            index += 1
        if index >= len(source):
            break
        quoted_end = _lean_quoted_identifier_end(source, index)
        if quoted_end > index:
            names.append(source[index:quoted_end])
            index = quoted_end
            continue
        match = re.match(_PLAUSIBLE_LEAN_IDENT, source[index:])
        if match is None:
            return None
        name = match.group(0)
        if name in _EXAMPLE_BINDER_RESERVED_NAMES:
            return None
        names.append(name)
        index += len(name)
        if index < len(source) and not (
            source[index].isspace() or source[index] == ","
        ):
            return None
    return names or None


def _example_header_without_assign(after_example: str, sep_end: int) -> str:
    header = after_example[: max(0, sep_end - 2)].strip()
    if header.endswith(":"):
        header = header[:-1].rstrip()
    return header


def _binder_names_from_example_header(header: str) -> tuple[list[str], str]:
    """Return explicit leading binder names and the remaining target header."""

    rest = str(header or "").strip()
    names: list[str] = []
    while rest:
        group = _take_leading_example_binder_group(rest)
        if group is None:
            break
        opener, inside, remainder = group
        masked_inside = _strip_lean_comments_and_strings(inside)
        if (
            ":=" in masked_inside
            or "⟨" in masked_inside
            or "=>" in masked_inside
        ):
            return [], str(header or "").strip()
        colon_index = masked_inside.find(":")
        before_colon = (
            inside[:colon_index] if colon_index >= 0 else inside
        ).strip()
        name_tokens = _example_binder_name_tokens(before_colon)
        if opener == "[" and (colon_index < 0 or name_tokens is None):
            suffix = 1
            synthetic_name = f"_inst_{suffix}"
            while synthetic_name in names:
                suffix += 1
                synthetic_name = f"_inst_{suffix}"
            names.append(synthetic_name)
            rest = remainder.strip()
            continue
        if name_tokens is None:
            return [], str(header or "").strip()
        names.extend(name_tokens)
        rest = remainder.strip()
    return names, rest


def _prepend_intro_to_example_body(body: str, names: Sequence[str]) -> str:
    intro_names = " ".join(
        str(name or "").strip() for name in names if str(name or "").strip()
    )
    proof = str(body or "").strip()
    if not intro_names or not proof:
        return proof
    if proof.startswith("by"):
        tail = proof[2:].strip()
        if not tail:
            return f"by\n  intro {intro_names}"
        indented_tail = "\n".join(
            "  " + line if line.strip() else line for line in tail.splitlines()
        )
        return f"by\n  intro {intro_names}\n{indented_tail}"
    return f"by\n  intro {intro_names}\n  exact {proof}"


def _extract_example_body(chunk: str) -> Optional[str]:
    """Pull the body out of an ``[noncomputable] example ... := <body>`` chunk.

    Returns ``None`` if the chunk doesn't look like an example declaration or
    if no top-level ``:=`` separator can be located. Tolerates optional
    ``noncomputable`` prefix. Binder-style examples are converted into a proof
    body by introducing their explicit leading binders, so natural model output
    such as ``example (h : P) : Q := by exact h`` can satisfy a goal like
    ``P → Q`` instead of being silently discarded.
    """
    s = chunk.strip()
    if s.startswith("noncomputable"):
        s = s[len("noncomputable") :].lstrip()
    if not s.startswith("example"):
        return None
    # Skip past the keyword and look for the body separator anywhere
    # in the rest of the declaration. ``_find_top_level_assign`` handles
    # binders in parens, lets in the type, and any other nesting.
    after = s[len("example") :]
    sep_end = _find_top_level_assign(after)
    if sep_end < 0:
        return None
    header = _example_header_without_assign(after, sep_end)
    if header and not header.startswith(":"):
        binder_names, rest = _binder_names_from_example_header(header)
        if not binder_names or not _strip_lean_comments(rest).lstrip().startswith(":"):
            return None
        body = after[sep_end:].strip()
        return _prepend_intro_to_example_body(body, binder_names) or None
    body = after[sep_end:].strip()
    return body or None


def _extract_single_decl_body(chunk: str) -> Optional[str]:
    """Pull the proof body from a single theorem/lemma declaration chunk.

    Recursive helper subgoals often trigger this shape because the model
    restates the helper theorem it was asked to prove, sometimes after
    auxiliary declarations. Returning the body lets Lean check it against the
    actual current goal, so a mismatched declaration still fails normally
    instead of being trusted.
    """

    s = (chunk or "").strip()
    if not re.match(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma)\b",
        s,
    ):
        return None
    body = helper_decl_body(s)
    if not body:
        return None
    if not _is_plausible_main_proof(body):
        return None
    return body


def _normalize_statement_for_contract(text: object) -> str:
    compact = " ".join(str(text or "").split())
    if not compact:
        return ""
    try:
        from ensemble_prover.proof_state import (
            canonicalize_lean_statement_for_identity,
        )

        return canonicalize_lean_statement_for_identity(compact)
    except Exception:
        return compact


def _decl_matches_main_target(
    decl: str,
    *,
    theorem_name: str = "",
    goal_statement: str = "",
    allow_anonymous: bool = False,
) -> bool:
    """Whether a named declaration can be interpreted as the current proof."""

    expected_statement = _normalize_statement_for_contract(goal_statement)
    decl_statement = _normalize_statement_for_contract(helper_decl_statement(decl))
    if expected_statement and decl_statement:
        return decl_statement == expected_statement
    name = helper_decl_name(decl) or ""
    expected_name = str(theorem_name or "").strip()
    if expected_name and name == expected_name:
        return True
    if expected_statement:
        return False
    return bool(allow_anonymous)


def _extract_helpers_and_main(
    llm_output: str,
    *,
    theorem_name: str = "",
    goal_statement: str = "",
    allow_decl_main: bool = True,
) -> Tuple[List[str], Optional[str]]:
    """Split the LLM's lean fenced block into (helpers, main_proof_body).

    Helpers are top-level ``theorem``/``lemma``/``def``/``abbrev``/``instance``
    declarations. ``main_proof_body`` is the proof attached to the final
    ``example : ... := <body>`` block, or a bare ``by ...`` block at the end.
    Returns ``(helpers, None)`` when no main-proof candidate is present (e.g.
    the model emitted only helpers — caller treats this as a failed turn).

    ``theorem_name`` is the target theorem name (e.g. a benchmark root
    theorem or recursive helper name). When supplied, a final declaration
    whose name matches ``theorem_name`` is allowed to act as the main proof
    (its body is extracted as ``main_proof_body``). When ``goal_statement``
    is supplied, an exact same-statement declaration may also act as the
    proof body; this catches recursive helper replies that redeclare the
    helper under a fresh local name. ``allow_decl_main=False`` disables both
    paths for root-only phases that forbid command-shaped submissions.
    """
    blocks = extract_code_fences(llm_output or "")
    if not blocks:
        # No code fence at all. Be conservative: only accept output that
        # clearly looks like a proof (starts with `by` or `example`). The
        # legacy ``extract_proof_candidates`` falls through to returning
        # whatever text it can find, which means natural-language replies
        # like "Please paste the current goal..." get treated as proofs
        # and spliced into the synthesized Lean file as the body of
        # ``example : <stmt> := <NL_text>`` — Lean then chokes on the
        # English words, producing parser errors like ``unexpected token
        # 'local'`` (because the NL contained "local hypotheses"). We
        # don't want that. If the model didn't emit a code fence,
        # treat it as no proof extracted and let the loop nudge it.
        text = normalize_nat_factorial_notation((llm_output or "").strip())
        if _find_forbidden_lean_command([], text) is not None:
            return [], None
        if text.startswith("example"):
            return [], _extract_example_body(text)
        if _is_plausible_main_proof(text):
            return [], text
        return [], None

    helper_only_chunks: List[str] = []
    policy_chunks: List[str] = []
    lone_decl_body_candidate: Optional[str] = None
    lone_decl_open_commands: List[str] = []
    for raw_src in blocks:
        stripped_src, leading_open_commands = (
            _partition_redundant_preamble_commands(raw_src.strip())
        )
        src = normalize_nat_factorial_notation(stripped_src)
        if not src:
            continue
        if _is_local_open_scoped_proof(src):
            helpers = _helpers_referenced_by_proof(helper_only_chunks, src)
            if policy_chunks:
                helpers = policy_chunks + helpers
            return helpers, src
        if _find_forbidden_lean_command([src], "") and src not in policy_chunks:
            policy_chunks.append(src)

        leading, chunks = _split_top_level_chunks(src)
        if not chunks:
            # No structured declarations. Only accept a legacy-extracted fence
            # if the candidate itself looks like an executable proof expression.
            # This blocks explanatory Lean snippets such as a bare goal
            # proposition from being spliced in as ``example : goal := <prop>``.
            candidates = extract_proof_candidates(src)
            for candidate in candidates:
                if _is_plausible_main_proof(candidate):
                    helpers = _helpers_referenced_by_proof(helper_only_chunks, candidate)
                    if policy_chunks:
                        helpers = policy_chunks + helpers
                    return helpers, _scope_proof_with_open_commands(
                        candidate, leading_open_commands
                    )
            continue

        if not chunks:
            continue

        # The LAST chunk is the main-proof candidate (if it's an ``example`` or
        # a bare ``by`` block). Everything before it is a helper.
        last = chunks[-1]
        scoped_chunks = [
            _scope_helper_with_open_commands(chunk, leading_open_commands)
            if helper_decl_kind(chunk)
            else chunk
            for chunk in chunks
        ]
        helpers = list(scoped_chunks[:-1])
        if leading and (
            helper_decl_kind(leading)
            or _find_forbidden_lean_command([leading], "")
        ):
            helpers.insert(0, leading)
        main_proof: Optional[str] = None
        from_example = False

        example_body = _extract_example_body(last)
        if example_body is not None:
            # Locate the example's body via a bracket-and-let-aware walker so we
            # don't get fooled by `:=` inside the body (have/let), inside the
            # type (`example : let x := 1; ...`), or inside binder defaults.
            main_proof = example_body
            from_example = True
        elif last.startswith("example") or last.startswith("noncomputable example"):
            continue
        elif last.startswith("by"):
            main_proof = last
        else:
            decl_body = _extract_single_decl_body(last)
            if decl_body is not None:
                if (
                    len(chunks) == 1
                    and not helper_only_chunks
                    and not _lean_body_is_sorry_stub(decl_body)
                    and allow_decl_main
                    and _decl_matches_main_target(
                        last,
                        theorem_name=theorem_name,
                        goal_statement=goal_statement,
                        allow_anonymous=not bool(theorem_name or goal_statement),
                    )
                ):
                    # Single-chunk case: a lone named non-sorry decl may
                    # serve as the root proof only when its name matches
                    # the benchmark (or no name was supplied). Without
                    # this guard, an LLM that emits a single helper-named
                    # theorem with a non-root body would have that body
                    # submitted against the root goal (A4-symmetric fix
                    # for the single-chunk path; mirrors the multi-chunk
                    # branch below).
                    lone_decl_body_candidate = decl_body
                    lone_decl_open_commands = list(leading_open_commands)
                elif (
                    allow_decl_main
                    and _decl_matches_main_target(
                        last,
                        theorem_name=theorem_name,
                        goal_statement=goal_statement,
                    )
                    and not _lean_body_is_sorry_stub(decl_body)
                ):
                    # Multi-chunk case: only demote the last decl to main_proof
                    # when its name matches the benchmark root theorem name.
                    # Sorry-stub root declarations are decomposition/policy
                    # artifacts, not checked root proofs.
                    # Otherwise we'd submit a helper's body against the wrong
                    # goal (A4 structural fix, 2026-05-08).
                    main_proof = decl_body
            if main_proof is None:
                # The last chunk was a helper, not a main proof. Keep helper-only
                # blocks available for a later proof fence, but only the helpers
                # whose names appear in proof code (comments ignored) will be
                # carried forward.
                helper_only_chunks.extend(scoped_chunks)
                continue

        if from_example or _is_plausible_main_proof(main_proof):
            carry_helpers = _helpers_referenced_by_proof(helper_only_chunks, main_proof)
            if policy_chunks:
                carry_helpers = policy_chunks + carry_helpers
            return _dedupe_helpers_by_name_last_wins(
                carry_helpers + helpers
            ), _scope_proof_with_open_commands(
                main_proof, leading_open_commands
            )
        if helpers:
            helper_only_chunks.extend(helpers)

    if lone_decl_body_candidate is not None and len(helper_only_chunks) == 1:
        return list(policy_chunks), _scope_proof_with_open_commands(
            lone_decl_body_candidate, lone_decl_open_commands
        )
    return order_helpers_for_incremental_validation(helper_only_chunks), None


def _extract_lemma_dag_helper_declarations(
    llm_output: str,
    *,
    theorem_name: str = "",
    suppress_solution_placeholders: bool = True,
) -> List[str]:
    helpers: List[str] = []
    seen: set[str] = set()
    for raw_src in extract_code_fences(llm_output or ""):
        stripped_src, leading_open_commands = (
            _partition_redundant_preamble_commands(raw_src.strip())
        )
        src = normalize_nat_factorial_notation(stripped_src)
        if not src:
            continue
        _leading, chunks = _split_top_level_chunks(src)
        for chunk in chunks:
            raw_text = str(chunk or "").strip()
            if not re.match(
                r"^\s*(?:@\[[^\]]*\]\s*)*"
                r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
                r"(?:theorem|lemma)\b",
                raw_text,
            ):
                continue
            text = _scope_helper_with_open_commands(
                raw_text,
                leading_open_commands,
            )
            name = helper_decl_name(text) or ""
            if (
                not name
                or name == theorem_name
                or (suppress_solution_placeholders and name.endswith("_solution"))
            ):
                continue
            if not helper_decl_body(text):
                continue
            if name in seen:
                continue
            seen.add(name)
            helpers.append(text)
    return helpers


def _lean_body_is_sorry_stub(body: Any) -> bool:
    """Return True for bodies that contain no proof beyond a sorry/admit stub."""

    text = str(body or "")
    text = re.sub(r"/-[\s\S]*?-/", "", text)
    text = re.sub(r"--[^\n]*", "", text)
    norm = " ".join(text.split()).lower()

    def _strip_outer_container(expr: str) -> str:
        pairs = {"(": ")", "{": "}", "⟨": "⟩"}
        expr = expr.strip()
        for _ in range(8):
            if len(expr) >= 2 and pairs.get(expr[0]) == expr[-1]:
                expr = expr[1:-1].strip()
                continue
            break
        return expr

    def _is_stub_expr(expr: str, depth: int = 0) -> bool:
        if depth > 8:
            return False
        expr = _strip_outer_container(expr.strip())
        if expr in {"by sorry", "by admit", "sorry", "admit"}:
            return True
        if re.fullmatch(r"(?:by\s+)?(?:sorry|admit)(?:\s*:\s*[\s\S]+?)?", expr):
            return True
        show = re.fullmatch(r"(?:by\s+)?show\s+[\s\S]+?\s+from\s+([\s\S]+)", expr)
        if show and _is_stub_expr(show.group(1), depth + 1):
            return True
        if re.fullmatch(r"by\s+(?:skip\s*;\s*)+(?:sorry|admit)", expr):
            return True
        grouped = re.fullmatch(r"(?:by\s+)?\{\s*([\s\S]+?)\s*\}", expr)
        if grouped and _is_stub_expr(grouped.group(1), depth + 1):
            return True
        wrapped = re.fullmatch(r"by\s+(?:exact|refine|apply)\s+([\s\S]+)", expr)
        if wrapped and _is_stub_expr(wrapped.group(1), depth + 1):
            return True
        ascribed = re.fullmatch(r"([\s\S]+?)\s*:\s*[\s\S]+", expr)
        if ascribed and _is_stub_expr(ascribed.group(1), depth + 1):
            return True
        return False

    return _is_stub_expr(norm)


def _helper_is_sorry_stub(block: str) -> bool:
    return _lean_body_is_sorry_stub(helper_decl_body(block) or "")


def _sorry_stub_helper_names(blocks: Sequence[str]) -> List[str]:
    names: List[str] = []
    for block in blocks or []:
        if _helper_is_sorry_stub(str(block or "")):
            name = helper_decl_name(str(block or "")) or "<anonymous helper>"
            if name not in names:
                names.append(name)
    return names


def _helper_statement_root_equivalent(
    helper_block: str,
    *,
    goal_statement: str = "",
) -> bool:
    statement = helper_decl_statement(str(helper_block or ""))
    if not statement or not str(goal_statement or "").strip():
        return False
    try:
        from ensemble_prover.proof_state import (
            canonicalize_lean_statement_for_identity,
        )

        return (
            canonicalize_lean_statement_for_identity(statement)
            == canonicalize_lean_statement_for_identity(goal_statement)
        )
    except Exception:
        return " ".join(statement.split()) == " ".join(str(goal_statement).split())


def _root_equivalent_helper_names_from_blocks(
    blocks: Sequence[str],
    *,
    goal_statement: str = "",
) -> List[str]:
    names: List[str] = []
    for block in blocks or []:
        if _helper_statement_root_equivalent(
            str(block or ""),
            goal_statement=goal_statement,
        ):
            name = helper_decl_name(str(block or "")) or "<anonymous helper>"
            if name not in names:
                names.append(name)
    return names


def _root_equivalent_sorry_stub_helper_names_from_blocks(
    blocks: Sequence[str],
    *,
    goal_statement: str = "",
) -> List[str]:
    names: List[str] = []
    for block in blocks or []:
        text = str(block or "")
        if not _helper_is_sorry_stub(text):
            continue
        if _helper_statement_root_equivalent(text, goal_statement=goal_statement):
            name = helper_decl_name(text) or "<anonymous helper>"
            if name not in names:
                names.append(name)
    return names
