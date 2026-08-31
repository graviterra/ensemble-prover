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


_FORBIDDEN_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_'])\b(?:sorry|admit)\b")
_EXECUTABLE_META_RE = re.compile(
    r"(?<![A-Za-z0-9_'])\b(?:run_tac|run_term_elab|elabTermEnsuringType)\b"
)
_DIRECTIVE_RE = re.compile(r"(?<![A-Za-z0-9_'])#[A-Za-z_][A-Za-z0-9_']*")
_HIDDEN_DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:private|local)\s+"
    r"(?:noncomputable\s+)?(?:def|abbrev|structure|class|inductive|instance|theorem|lemma)\b"
)
_ANONYMOUS_INSTANCE_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?instance\s*[:{(\[]"
)
_SOLUTION_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])putnam_[A-Za-z0-9_']*_solution[A-Za-z0-9_']*",
    re.IGNORECASE,
)
_FORBIDDEN_COMMAND_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(?:axiom|constant|unsafe|run_cmd|initialize|builtin_initialize|"
    r"elab|elab_rules|macro|syntax|declare_syntax_cat|register_option|"
    r"register_simp_attr|opaque)\b"
)
_PARTIAL_DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
    r"partial\s+(?:def|abbrev|theorem|lemma)\b"
)
_IMPORT_RE = re.compile(r"(?m)^\s*import\s+([^\s]+)\s*$")


def _strip_comments_and_strings(source: str) -> str:
    text = str(source or "")
    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                index += 2
                continue
            if text.startswith("-/", index):
                block_depth -= 1
                index += 2
                continue
            out.append("\n" if text[index] == "\n" else " ")
            index += 1
            continue
        if in_string:
            char = text[index]
            out.append("\n" if char == "\n" else " ")
            if char == "\\" and index + 1 < len(text):
                out.append(" ")
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                out.extend(" " for _ in text[index:])
                break
            out.extend(" " for _ in text[index:newline])
            out.append("\n")
            index = newline + 1
            continue
        if text.startswith("/-", index):
            block_depth = 1
            out.extend((" ", " "))
            index += 2
            continue
        if text[index] == '"':
            in_string = True
            out.append(" ")
            index += 1
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


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
        clean = _strip_comments_and_strings(raw)
        reasons: list[str] = []
        if not clean.strip():
            reasons.append("empty_source")
        if _FORBIDDEN_TOKEN_RE.search(clean):
            reasons.append("proof_placeholder")
        if _FORBIDDEN_COMMAND_RE.search(clean) or _PARTIAL_DECLARATION_RE.search(clean):
            reasons.append("forbidden_command")
        if _EXECUTABLE_META_RE.search(clean) or _DIRECTIVE_RE.search(clean):
            reasons.append("executable_meta_command")
        if _HIDDEN_DECLARATION_RE.search(clean):
            reasons.append("hidden_declaration")
        if _ANONYMOUS_INSTANCE_RE.search(clean):
            reasons.append("anonymous_instance_not_auditable")
        if _SOLUTION_TOKEN_RE.search(clean):
            reasons.append("answer_placeholder_reference")
        imports = tuple(dict.fromkeys(match.group(1).strip() for match in _IMPORT_RE.finditer(clean)))
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
