"""Apply structural source-policy gates to a typed turn extraction.

The gates reject forbidden commands, construction collapse, helper stubs,
preamble redeclarations, declarations after the main proof, and ambiguous main
proof chunks. The result is a typed verdict with matched-source context for Lean
dispatch or rejection feedback.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional, Sequence

from .extract import TurnExtraction


class PolicyVerdictKind(str, Enum):
    """Classification of the policy gate's decision."""

    ACCEPT = "accept"
    REJECT_FORBIDDEN_CMD = "reject_forbidden_cmd"
    REJECT_CONSTRUCTION_COLLAPSE = "reject_construction_collapse"
    REJECT_POST_MAIN = "reject_post_main"
    REJECT_EXTRA_MAIN = "reject_extra_main"
    REJECT_HELPER_STUB_WITH_MAIN = "reject_helper_stub_with_main"
    REJECT_PREAMBLE_REDECLARATION = "reject_preamble_redeclaration"


@dataclass(frozen=True)
class PolicyVerdict:
    """Verdict + payload returned by ``apply_policy_gates``."""

    kind: PolicyVerdictKind
    match: str = ""  # The matched phrase / declaration name / chunk preview
    detail: str = ""  # Optional supplementary explanation

    @property
    def accept(self) -> bool:
        return self.kind is PolicyVerdictKind.ACCEPT


def _legacy_imports():
    from ensemble_prover.helper_salvage import merge_context_helpers
    from ensemble_prover.mini_prover import (
        _detect_known_answer_no_construction_collapse,
        _find_forbidden_lean_command,
    )

    return {
        "detect_construction_collapse": _detect_known_answer_no_construction_collapse,
        "find_forbidden_lean_command": _find_forbidden_lean_command,
        "merge_context_helpers": merge_context_helpers,
    }


def apply_policy_gates(
    extraction: TurnExtraction,
    *,
    conv: Any,
    content: str = "",
    context_helpers: Optional[Sequence[str]] = None,
) -> PolicyVerdict:
    """Run the per-turn policy gates in order; return the FIRST rejection.

    Structural gate order is:
    forbidden → extra-main/post-main ordering → construction collapse.
    The pre-extraction post-main and extra-main checks remain at their original
    site; this gate also runs them so direct pipeline callers get the same
    coverage.

    Preserves:
    - A3: forbidden-cmd anchor uses column-0 only via
      ``_find_forbidden_lean_command``.
    - Construction collapse: only fires under ``opaque_mode`` (the
      legacy gate at mini_prover.py:3704 has the same opacity guard).
    """

    primitives = _legacy_imports()
    helpers = list(extraction.helpers or [])
    policy_helper_candidates = list(
        dict.fromkeys([*helpers, *list(extraction.lemma_dag_candidates or [])])
    )
    proof = extraction.proof if isinstance(extraction.proof, str) else None
    context_helpers_list: list = list(context_helpers or [])

    # 1. Forbidden Lean command.
    forbidden = primitives["find_forbidden_lean_command"](
        helpers, proof or ""
    )
    if forbidden is not None:
        return PolicyVerdict(
            kind=PolicyVerdictKind.REJECT_FORBIDDEN_CMD,
            match=str(forbidden),
        )

    if proof is not None:
        try:
            from ensemble_prover.mini_prover import _sorry_stub_helper_names

            sorry_stub_names = _sorry_stub_helper_names(policy_helper_candidates)
        except Exception:
            sorry_stub_names = []
        if sorry_stub_names:
            return PolicyVerdict(
                kind=PolicyVerdictKind.REJECT_HELPER_STUB_WITH_MAIN,
                match=", ".join(sorry_stub_names[:4]),
                detail=(
                    "sorry-stub helpers are not proof code; they cannot appear "
                    "in the same reply as a main proof"
                ),
            )

    # 1b. Conflicting redefinition of an immutable preamble declaration.
    #     Silently shadowing the verification environment is never allowed;
    #     equivalent restatements were already dropped at extraction.
    if getattr(extraction, "preamble_redeclaration_conflicts", None):
        return PolicyVerdict(
            kind=PolicyVerdictKind.REJECT_PREAMBLE_REDECLARATION,
            match=", ".join(extraction.preamble_redeclaration_conflicts[:4]),
            detail=(
                "reply redefines immutable preamble declaration(s) with "
                "different content"
            ),
        )

    # 2. Extra main chunks (ambiguity). Order: this fires before
    #    construction-collapse because if there are multiple main proofs
    #    we don't have a single proof to gate on.
    if extraction.extra_main_chunks:
        first = extraction.extra_main_chunks[0]
        return PolicyVerdict(
            kind=PolicyVerdictKind.REJECT_EXTRA_MAIN,
            match=str(first)[:160],
        )

    # 3. Post-main declarations (ordering violation).
    if extraction.post_main_declarations:
        return PolicyVerdict(
            kind=PolicyVerdictKind.REJECT_POST_MAIN,
            match=", ".join(extraction.post_main_declarations[:4]),
        )

    # 4. Construction-collapse (opaque mode only). The legacy gate
    #    feeds it ``check_lemmas`` (merged context+fresh) when proof
    #    is present, and ``helpers`` (fresh-only) when proof is None
    #    (mini_prover.py:3992 vs 4135). Mirror that here.
    opaque_mode = bool(getattr(conv, "opaque_mode", True))
    benchmark_answer_policy = bool(
        getattr(conv, "suppress_solution_placeholders", True)
    )
    if opaque_mode and benchmark_answer_policy:
        goal_statement = str(getattr(conv, "goal_statement", "") or "")
        collapse_helpers = (
            primitives["merge_context_helpers"](context_helpers_list, helpers)
            if proof is not None
            else helpers
        )
        collapse = primitives["detect_construction_collapse"](
            content, collapse_helpers, proof, goal_statement=goal_statement
        )
        if collapse is not None:
            reason = str(collapse.get("reason") or "").strip()
            match = str(collapse.get("match") or "").strip()
            return PolicyVerdict(
                kind=PolicyVerdictKind.REJECT_CONSTRUCTION_COLLAPSE,
                match=match,
                detail=reason,
            )

    return PolicyVerdict(kind=PolicyVerdictKind.ACCEPT)
