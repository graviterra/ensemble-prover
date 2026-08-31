"""Target-bound counterexample admission through Mini's authority boundary."""

from __future__ import annotations

import re
from typing import Any, Callable, Dict, Optional, Sequence

from .mini_deadline_transaction import DeadlineMutationTransaction
from .mini_session.child_goal_falsification import (
    counterexample_negation_proof_from_declaration,
    record_authoritative_negation_artifact,
)
from .utils import has_sorry_or_admit, strip_lean_noncode_for_token_checks


CERTIFY_COUNTEREXAMPLE_TOOL: Dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "certify_counterexample",
        "description": (
            "Certify that the current Lean target is false. The target is fixed "
            "by the active proof task and cannot be supplied or changed here. "
            "Pass either a complete `by ...` proof of its negation, or exactly "
            "one complete top-level `example : <concrete counterexample> := by "
            "...`. The system synthesizes a proof of the full negation when "
            "possible, independently replays it, audits its axioms, and only "
            "then records an authoritative disproof."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": (
                        "A `by ...` proof of ¬current_target, or one complete "
                        "counterexample `example` declaration."
                    ),
                },
                "purpose": {
                    "type": "string",
                    "description": "Short explanation of the suspected defect.",
                },
            },
            "required": ["code"],
        },
    },
}


_TOP_LEVEL_EXAMPLE_RE = re.compile(r"^\s*example(?=\s|[:({\[])")
_FORBIDDEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(?:sorry|admit|native_decide|axiom|constant|unsafe|run_tac|run_cmd|"
    r"set_option|import|theorem|lemma)"
    r"(?![A-Za-z0-9_'])",
    flags=re.IGNORECASE,
)


def _strip_fence(code: str) -> str:
    text = str(code or "").strip()
    match = re.fullmatch(
        r"```(?:lean4?)?[ \t]*\r?\n([\s\S]*?)\r?\n```", text
    )
    return str(match.group(1) if match else text).strip()


def _direct_negation_body(code: str) -> str:
    clean = str(code or "").strip()
    if not clean or _TOP_LEVEL_EXAMPLE_RE.match(clean):
        return ""
    if clean.lstrip().startswith("by"):
        return clean
    return ""


async def _run_certify_counterexample_tool_impl(
    lean: Any,
    *,
    goal_statement: str,
    preamble: str,
    feedback_preamble: Optional[str] = None,
    args: Dict[str, Any],
    dossier: Any,
    proof_state: Any = None,
    parent_session: Any = None,
    context_lemmas: Optional[Sequence[str]] = None,
    feedback_context_lemmas: Optional[Sequence[str]] = None,
    publication_guard: Optional[Callable[[], None]] = None,
) -> str:
    code = _strip_fence(args.get("code", ""))
    statement = str(goal_statement or "").strip()
    if not statement:
        return "certify_counterexample rejected. Active target is empty."
    if not code:
        return "certify_counterexample rejected. Empty `code`."
    executable_code = strip_lean_noncode_for_token_checks(code)
    if has_sorry_or_admit(code) or _FORBIDDEN_RE.search(executable_code):
        return (
            "certify_counterexample rejected. Proof contains a forbidden "
            "trust-boundary construct."
        )

    direct_proof = _direct_negation_body(code)
    declarations: tuple[str, ...] = ()
    if not direct_proof:
        synthesized = counterexample_negation_proof_from_declaration(code, statement)
        if not synthesized:
            return (
                "certify_counterexample rejected. Code is neither a `by ...` "
                "proof of the active target's negation nor a recognized exact "
                "counterexample declaration."
            )
        declarations = (code,)

    visible_preamble = (
        None if feedback_preamble is None else str(feedback_preamble or "")
    )
    acceptance_preamble = str(preamble or "")

    session = parent_session
    if session is None:

        class _ToolSession:
            pass

        session = _ToolSession()
        session.lean = lean
        session.proof_state = proof_state
        session.iteration = 0
    certification_results: list[Any] = []
    (
        authoritative,
        certificate_hash,
        terminalized,
    ) = await record_authoritative_negation_artifact(
        parent_session=session,
        dossier=dossier,
        target_statement=statement,
        negation_proofs=((direct_proof,) if direct_proof else ()),
        negation_declarations=declarations,
        preamble=acceptance_preamble,
        helper_blocks=tuple(context_lemmas or ()),
        feedback_preamble=visible_preamble,
        feedback_helper_blocks=tuple(
            (
                context_lemmas
                if feedback_context_lemmas is None
                else feedback_context_lemmas
            )
            or ()
        ),
        certification_results=certification_results,
        engine="certify_counterexample_tool",
        reason=str(args.get("purpose") or "dedicated counterexample tool"),
        publication_guard=publication_guard,
    )
    if not authoritative:
        if (
            certificate_hash
            and str(getattr(dossier, "session_failure_kind", "") or "").strip()
            == "proof_disproof_conflict"
        ):
            return (
                "certify_counterexample conflict. Independent Lean replay and "
                "axiom audit established a disproof, but an authoritative root "
                f"proof is already installed. certificate={certificate_hash}"
            )
        retryable_result = next(
            (result for result in certification_results if result.retryable),
            None,
        )
        if retryable_result is not None:
            return (
                "certify_counterexample infrastructure error: "
                "independent Lean replay was temporarily unavailable"
            )
        return (
            "certify_counterexample rejected. Full negation did not pass "
            "independent Lean replay and axiom audit."
        )
    return (
        "certify_counterexample accepted. The active target is authoritatively "
        f"refuted. certificate={certificate_hash}; "
        f"terminalized_aliases={len(terminalized)}"
    )


async def run_certify_counterexample_tool(
    *args: Any,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
    **kwargs: Any,
) -> str:
    """Certify atomically so an elapsed turn cannot commit a late disproof."""

    transaction = DeadlineMutationTransaction(
        deadline_exhausted=deadline_exhausted,
        dossier=kwargs.get("dossier"),
        proof_state=kwargs.get("proof_state"),
        label="certify_counterexample_tool",
    )
    with transaction:
        if not transaction.can_mutate():
            return (
                "certify_counterexample cancelled: "
                "llm_turn_elapsed_budget_exhausted before certification."
            )
        result = await _run_certify_counterexample_tool_impl(*args, **kwargs)
        if not transaction.can_mutate():
            return (
                "certify_counterexample cancelled: "
                "llm_turn_elapsed_budget_exhausted before commit."
            )
    if transaction.enabled and not transaction.committed:
        return "certify_counterexample cancelled: deadline mutation commit failed."
    return result
