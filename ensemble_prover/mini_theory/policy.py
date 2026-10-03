"""Static safety policy for generated Mini theory modules.

Lean compilation and axiom inspection remain authoritative.  This early gate
rejects commands that could expand the trusted boundary or execute arbitrary
code before a candidate is ever passed to Lean.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable

from .model import THEORY_POLICY_VERSION
from .promotion_context import LEAN_IDENTIFIER_CONTINUATION, _mask_lean_noncode


_FORBIDDEN_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_'])\b(?:sorry|admit)\b")
_EXECUTABLE_META_RE = re.compile(
    r"(?<![A-Za-z0-9_'])\b(?:run_tac|run_term_elab|elabTermEnsuringType)\b"
)
_DIRECTIVE_RE = re.compile(r"(?<![A-Za-z0-9_'])#[A-Za-z_][A-Za-z0-9_']*")
_TOKEN_START = rf"(?<![{LEAN_IDENTIFIER_CONTINUATION}.`])"
_TOKEN_END = rf"(?![{LEAN_IDENTIFIER_CONTINUATION}.])"
_HIDDEN_DECLARATION_RE = re.compile(
    _TOKEN_START + r"(?:private|local)\s+"
    r"(?:noncomputable\s+)?(?:def|abbrev|structure|class|inductive|instance|theorem|lemma)"
    + _TOKEN_END
)
_ANONYMOUS_INSTANCE_RE = re.compile(
    _TOKEN_START + r"instance\s*[:{(\[]"
)
_SOLUTION_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])putnam_[A-Za-z0-9_']*_solution[A-Za-z0-9_']*",
    re.IGNORECASE,
)
_COMMAND_PREFIX = (
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial)\s+)*"
)
_FORBIDDEN_COMMAND_WORDS = (
    r"axiom|run_cmd|initialize|builtin_initialize|"
    r"elab|elab_rules|macro_rules|macro|syntax|declare_syntax_cat|register_option|"
    r"register_simp_attr|opaque"
)
_FORBIDDEN_COMMAND_RE = re.compile(
    _TOKEN_START + rf"(?:{_FORBIDDEN_COMMAND_WORDS})" + _TOKEN_END
)
# `constant` is an ordinary Lean 4 identifier. Preserve the legacy line-head
# gate without applying it to mathematical terms such as `for x in constant`.
_LEGACY_CONSTANT_COMMAND_RE = re.compile(_COMMAND_PREFIX + r"constant\b")
_PARTIAL_DECLARATION_RE = re.compile(
    _TOKEN_START + r"partial\s+(?:def|abbrev|theorem|lemma)" + _TOKEN_END
)
_UNSAFE_DECLARATION_RE = re.compile(
    _TOKEN_START + r"unsafe\s+(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(?:def|abbrev|instance|theorem|lemma|example|opaque|axiom|irreducible_def)"
    + _TOKEN_END
)
_IMPORT_RE = re.compile(r"(?m)^\s*import\s+([^\s]+)\s*$")
_QUOTED_IDENTIFIER_RE = re.compile(r"«[^»\r\n]+»")


def _strip_comments_and_strings(source: str) -> str:
    return _mask_lean_noncode(source)


@dataclass(frozen=True)
class TheoryPolicyVerdict:
    accepted: bool
    reasons: tuple[str, ...] = ()
    imports: tuple[str, ...] = ()
    policy_version: int = THEORY_POLICY_VERSION


class TheoryPolicy:
    """Fail-closed pre-compilation policy for generated theory source."""

    def __init__(
        self,
        *,
        allowed_import_prefixes: Iterable[str] = ("Mathlib", "MiniTheory"),
    ) -> None:
        self.allowed_import_prefixes = tuple(
            dict.fromkeys(str(item or "").strip() for item in allowed_import_prefixes if str(item or "").strip())
        )

    def evaluate(self, source: str, *, declared_imports: Iterable[str] = ()) -> TheoryPolicyVerdict:
        raw = str(source or "")
        lexical = _strip_comments_and_strings(raw)
        clean = _QUOTED_IDENTIFIER_RE.sub(" q ", lexical)
        # Reserved command heads can follow arbitrary same-line commands, not
        # just `in` wrappers. Syntax quotations are command data; meta execution
        # checks still inspect `clean`, including quotation antiquotations.
        commands = _mask_lean_noncode(clean, mask_syntax_quotations=True)
        reasons: list[str] = []
        if not clean.strip():
            reasons.append("empty_source")
        if _FORBIDDEN_TOKEN_RE.search(clean):
            reasons.append("proof_placeholder")
        if (
            _FORBIDDEN_COMMAND_RE.search(commands)
            or _LEGACY_CONSTANT_COMMAND_RE.search(clean)
            or _PARTIAL_DECLARATION_RE.search(commands)
            or _UNSAFE_DECLARATION_RE.search(commands)
        ):
            reasons.append("forbidden_command")
        if _EXECUTABLE_META_RE.search(clean) or _DIRECTIVE_RE.search(clean):
            reasons.append("executable_meta_command")
        if _HIDDEN_DECLARATION_RE.search(commands):
            reasons.append("hidden_declaration")
        if _ANONYMOUS_INSTANCE_RE.search(commands):
            reasons.append("anonymous_instance_not_auditable")
        if _SOLUTION_TOKEN_RE.search(lexical):
            reasons.append("answer_placeholder_reference")
        imports = tuple(dict.fromkeys(match.group(1).strip() for match in _IMPORT_RE.finditer(lexical)))
        declared = tuple(
            dict.fromkeys(str(item or "").strip() for item in declared_imports if str(item or "").strip())
        )
        if set(imports) != set(declared):
            reasons.append("declared_import_mismatch")
        for module in imports:
            if not any(
                module == prefix or module.startswith(f"{prefix}.")
                for prefix in self.allowed_import_prefixes
            ):
                reasons.append(f"import_not_allowed:{module}")
        return TheoryPolicyVerdict(
            accepted=not reasons,
            reasons=tuple(dict.fromkeys(reasons)),
            imports=imports,
        )
