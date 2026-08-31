"""Obtain a typed Lean verdict for one extracted proof candidate.

``verify_with_lean`` performs the primary check and any required answer-safe
recheck under the caller's deadline. It does not mutate the dossier or proof
state; the session action decides how verified evidence changes state.
"""

from __future__ import annotations

import asyncio
import re
import time
from dataclasses import dataclass
from typing import Any, Callable, List, Mapping, Optional, Sequence

from types import SimpleNamespace

from ...deadline_guard import (
    await_with_strict_deadline,
    create_result_only_deadline_task,
    outer_guard_timeout_s,
)
from ...runtime_context import mark_runtime_owned_callback
from ...proof_dossier import active_root_target_statement
from ...mini_lean_repairs import (
    rejection_supports_single_line_layout_repair,
    repair_single_line_by_tactic_block,
)


class AnswerSafeRecheckInfrastructureError(RuntimeError):
    """The prompt-visible acceptance recheck could not produce a verdict."""

    def __init__(self, message: str, *, primary_result: Any) -> None:
        super().__init__(message)
        self.primary_result = primary_result
        self.primary_accepted = bool(getattr(primary_result, "ok", False))


class LeanVerificationDeadline(asyncio.TimeoutError):
    """The enclosing verifier action yielded before another check launched."""


@dataclass(frozen=True)
class LeanVerdict:
    """Typed bundle returned by ``verify_with_lean``.

    Fields:
    - ``accepted``: True iff the proof should be accepted as a final
      solve. Mirrors the legacy result.ok-after-gating value.
    - ``primary_result``: the result object returned by the first
      ``lean.check`` call (against ``conv.lean_preamble``). Always
      present.
    - ``safe_result``: the result of the answer-safe recheck, if it
      was run; None otherwise.
    - ``feedback_result``: the result-shaped object the orchestrator
      should use to render Lean failure feedback to the LLM. Mirrors
      the legacy ``feedback_result`` selection logic at
      mini_prover.py:4468-4479.
    - ``feedback_source``: tag for telemetry — one of
      ``"primary_check"``, ``"active_root_target_check"``,
      ``"active_root_lift_check"``,
      ``"active_root_lift_answer_safe_check"``,
      ``"answer_safe_check"``, ``"primary_check_with_answer_safe_pass"``,
      ``"answer_safe_check_failed"``.
    - ``primary_elapsed_s`` / ``safe_elapsed_s``: wall-clock spent.
    - ``lean_feedback_error``: exception text if the recheck threw.
    - ``accepted_proof``: proof text that Lean accepted. This can differ
      from the submitted proof when an active-root proof is lifted back to
      the displayed root theorem.
    - ``primary_source``: ``"submitted"``, ``"active_root_target"``, or
      ``"active_root_lift"``.
    - ``active_root_statement`` / ``active_root_result``: populated when
      the submitted proof was first checked against the Lean-derived active
      target before root-shell stitching.
    """

    accepted: bool
    primary_result: Any
    safe_result: Optional[Any] = None
    feedback_result: Optional[Any] = None
    feedback_source: str = "primary_check"
    primary_elapsed_s: float = 0.0
    safe_elapsed_s: Optional[float] = None
    lean_feedback_error: Optional[str] = None
    accepted_proof: Optional[str] = None
    primary_source: str = "submitted"
    active_root_statement: str = ""
    active_root_result: Optional[Any] = None


_SOLUTION_NAME_RE = re.compile(
    r"(?:«[^»]*_solution[^»]*»|[A-Za-z_][A-Za-z0-9_'.]*_solution[A-Za-z0-9_'.]*)"
)


def _solution_names_in_statement(statement: str) -> List[str]:
    seen: set[str] = set()
    names: List[str] = []
    for match in _SOLUTION_NAME_RE.finditer(str(statement or "")):
        name = str(match.group(0) or "").strip()
        if name and name not in seen:
            seen.add(name)
            names.append(name)
    return names


def _indent(text: str, spaces: int) -> str:
    prefix = " " * max(0, int(spaces or 0))
    lines = str(text or "").splitlines()
    return "\n".join((prefix + line if line.strip() else "") for line in lines)


def _dedent_nonempty(lines: Sequence[str]) -> List[str]:
    nonempty = [line for line in lines if str(line).strip()]
    if not nonempty:
        return [str(line) for line in lines]
    margin = min(len(line) - len(line.lstrip(" ")) for line in nonempty)
    return [str(line)[margin:] if len(str(line)) >= margin else "" for line in lines]


def _proof_body_for_have(proof: str) -> str:
    text = str(proof or "").strip()
    if not text:
        return "by\n    exact False.elim (by contradiction)"
    if text == "by":
        return "by\n    exact False.elim (by contradiction)"
    if text.startswith("by "):
        return "by\n" + _indent(text[3:].strip(), 4)
    lines = text.splitlines()
    if lines and lines[0].strip() == "by":
        body = "\n".join(_dedent_nonempty(lines[1:])).strip()
        if not body:
            return "by\n    exact False.elim (by contradiction)"
        return "by\n" + _indent(body, 4)
    return text


def _active_root_lifted_proofs(
    *,
    root_statement: str,
    proof: str,
    active_root_targets: Sequence[Mapping[str, Any]],
) -> List[str]:
    """Build root-theorem proofs from submitted active-target proofs.

    Visible-answer runs may simplify ``P ↔ putnam_x_solution`` to an active
    target ``P`` (or ``¬P``). Prompting the model with ``P`` is useful only if
    the verifier can stitch a proof of ``P`` back into the original root
    theorem. Otherwise honest active-target proofs are checked against the
    unsimplified equivalence and fail with a misleading binder-arity error.
    """

    target_items = [
        item
        for item in list(active_root_targets or ())
        if isinstance(item, Mapping)
        and str(item.get("working_target") or item.get("target") or "").strip()
    ]
    target = active_root_target_statement(
        target_items,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    if not target:
        return []
    names = _solution_names_in_statement(root_statement)
    if not names:
        return []
    simp_names = ", ".join(names)
    target_block = _indent(target, 4)
    have_proof = _proof_body_for_have(proof)
    if have_proof.startswith("by\n"):
        have_rhs = have_proof
    else:
        have_rhs = have_proof
    return [
        "\n".join(
            [
                "by",
                "  have h_active :",
                target_block + " :=",
                _indent(have_rhs, 4),
                f"  simpa [{simp_names}] using h_active",
            ]
        )
    ]


def _active_root_check_statement(
    *,
    root_statement: str,
    active_root_targets: Sequence[Mapping[str, Any]],
) -> str:
    """Return the closed active-root target that prompt/tools ask to prove.

    The verifier must first check the proof against this target before trying
    to stitch it back into the original root theorem.  Otherwise a rejected
    lift can surface a synthetic ``h_active`` shell obligation even when the
    model was told to submit a direct proof of the active target.
    """

    if not _solution_names_in_statement(root_statement):
        return ""
    target_items = [
        item
        for item in list(active_root_targets or ())
        if isinstance(item, Mapping)
        and str(item.get("working_target") or item.get("target") or "").strip()
    ]
    if len(target_items) != 1:
        return ""
    return active_root_target_statement(
        target_items,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )


def _synthetic_check_failure(output: str) -> Any:
    return SimpleNamespace(
        ok=False,
        output=str(output or ""),
        returncode=1,
        parsed=None,
    )


def _legacy_imports():
    from ensemble_prover.mini_prover import (
        _feedback_lemmas_for_answer_safe_recheck,
        _needs_answer_safe_feedback_check,
    )
    from ensemble_prover.proof_dossier import helper_decl_name

    return {
        "needs_recheck": _needs_answer_safe_feedback_check,
        "feedback_lemmas": _feedback_lemmas_for_answer_safe_recheck,
        "helper_decl_name": helper_decl_name,
    }


def _answer_safe_recheck_lemmas(
    *,
    context_helpers: Sequence[str],
    helpers: Sequence[str],
    conv: Any,
    primitives: Mapping[str, Any],
) -> List[str]:
    """Build answer-safe lemmas with signature-aware helper replacement.

    Same-name helpers with a different statement are model self-corrections
    and must replace the stale context entry. Name-only skipping would keep
    the axiomatized stale statement and drop the correction.
    """

    from ensemble_prover.helper_salvage import (
        _helper_statement_signature,
        merge_context_helpers,
    )

    helper_decl_name = primitives["helper_decl_name"]
    merged = merge_context_helpers(list(context_helpers), list(helpers))
    fresh_by_key: dict[tuple[str, str], str] = {}
    unnamed_fresh: List[str] = []
    for block in helpers:
        source = str(block or "")
        name = helper_decl_name(source) or ""
        if not name:
            if source.strip():
                unnamed_fresh.append(source)
            continue
        fresh_by_key[(name, _helper_statement_signature(source))] = source
    context_for_feedback: List[str] = []
    fresh_for_feedback: List[str] = list(unnamed_fresh)
    for block in merged:
        source = str(block or "")
        name = helper_decl_name(source) or ""
        key = (name, _helper_statement_signature(source))
        if name and key in fresh_by_key:
            fresh_for_feedback.append(fresh_by_key[key])
        else:
            context_for_feedback.append(source)
    return [
        *primitives["feedback_lemmas"](context_for_feedback, conv),
        *fresh_for_feedback,
    ]


async def verify_with_lean(
    *,
    conv: Any,
    lean: Any,
    proof: str,
    helpers: Sequence[str],
    context_helpers: Sequence[str],
    check_lemmas: Sequence[str],
    goal_statement_override: Optional[str] = None,
    active_root_targets: Sequence[Mapping[str, Any]] = (),
    deadline_monotonic: float = 0.0,
    verifier_timeout_override_s: Optional[float] = None,
    deadline_exhausted: Optional[Callable[[], bool]] = None,
) -> LeanVerdict:
    """Run primary Lean check + (optionally) answer-safe recheck.

    Mirrors the sequence at mini_prover.py:4254 (primary check) +
    4330-4405 (answer-safe recheck + acceptance gating). Returns a
    typed verdict; does not mutate dossier/proof_state.

    When the checker preamble differs from the prompt-visible preamble,
    the prompt-visible recheck gates acceptance so a proof cannot be accepted
    merely because it relied on hidden filled answer values.
    """

    primitives = _legacy_imports()

    def deadline_elapsed() -> bool:
        try:
            return bool(
                (deadline_exhausted and deadline_exhausted())
                or (
                    float(deadline_monotonic or 0.0) > 0.0
                    and time.monotonic() >= float(deadline_monotonic)
                )
            )
        except Exception:
            return True

    async def checked(*args: Any, **kwargs: Any) -> Any:
        from ...mini_formal_state_search import (
            _mark_lean_late_tail,
            _once_only_lock_release,
            _safe_release_lean_lock,
            acquire_prepared_lean_lock,
            bind_owned_lean_lock,
            reset_owned_lean_lock,
        )

        if deadline_elapsed():
            raise LeanVerificationDeadline(
                "Lean verification deferred at enclosing action deadline"
            )
        if (
            verifier_timeout_override_s is not None
            and "timeout_s" not in kwargs
        ):
            kwargs["timeout_s"] = max(
                0.0,
                float(verifier_timeout_override_s),
            )
        acquired = False
        lock = None
        live = None
        awaitable = None
        # Soft policy has no enclosing deadline. Wait for a live Lean owner.
        # A discarded formal-state tail must not park this forever: recycle
        # or release that leaked lease, then check the submitted proof.
        lock_admission_timeout_s = None

        async def acquire_lock() -> None:
            nonlocal acquired, lock, live
            try:
                live, lock = await acquire_prepared_lean_lock(
                    lean,
                    admission_timeout_s=lock_admission_timeout_s,
                    deadline_elapsed=deadline_elapsed,
                    deadline_monotonic=float(deadline_monotonic or 0.0),
                    release_unrecyclable_tail=True,
                )
            except asyncio.TimeoutError as exc:
                raise LeanVerificationDeadline(
                    "Lean verification deferred while waiting for "
                    "the shared Lean lock"
                ) from exc
            acquired = True
            if deadline_elapsed():
                raise LeanVerificationDeadline(
                    "Lean verification deferred after shared-lock wait"
                )

        try:
            await await_with_strict_deadline(
                acquire_lock(),
                timeout_s=lock_admission_timeout_s,
                deadline_monotonic=float(deadline_monotonic or 0.0),
                operation_label="mini_turn_lean_check:lean_lock",
                # Lock admission does not mutate session state. A cancelled
                # or timed-out wait must not recycle the finished proof
                # waiting behind a late Lean tail.
                operation_ownership="result_only",
            )
        except asyncio.TimeoutError as exc:
            if acquired and lock is not None:
                _safe_release_lean_lock(lock)
            raise LeanVerificationDeadline(
                "Lean verification deferred at shared-lock deadline"
            ) from exc
        except BaseException:
            if acquired and lock is not None:
                _safe_release_lean_lock(lock)
            raise

        if deadline_elapsed():
            if lock is not None:
                _safe_release_lean_lock(lock)
            acquired = False
            raise LeanVerificationDeadline(
                "Lean verification deferred after shared-lock wait"
            )

        if live is None or lock is None:
            raise LeanVerificationDeadline(
                "Lean verification deferred after shared-lock wait"
            )
        awaitable = live.check(*args, **kwargs)
        release_owned_lock_once = _once_only_lock_release(lock)

        async def run_with_owned_lock() -> Any:
            token = bind_owned_lean_lock(lock)
            try:
                if deadline_elapsed():
                    # Safe to close here: the coroutine has not been awaited
                    # yet, so nothing is suspended inside it.
                    close = getattr(awaitable, "close", None)
                    if callable(close):
                        close()
                    raise LeanVerificationDeadline(
                        "Lean verification deferred before checker launch"
                    )
                return await awaitable
            finally:
                reset_owned_lean_lock(token)
                release_owned_lock_once()

        # Honor an explicit checker timeout or enclosing deadline only.
        # Soft policy must not invent a shorter proof-check cap: a late
        # successful verify is a solved goal, and LeanVerificationDeadline
        # on the primary path is not a run-terminator we can fire casually.
        # The same value is handed to the checker itself, and only the
        # checker's copy can actually reclaim: it runs killpg + reap. Arming
        # this outer guard at the identical number made the two race, and when
        # the guard won it discarded a verdict that was about to land and
        # detached from a Lean child still holding the runner lock -- the
        # exact "late successful verify is a solved goal" case this block says
        # it is protecting. Give the checker's own deadline room to fire,
        # kill, and reap first; this guard is only here for a checker that
        # never returns at all.
        owned_lock_timeout_s = None
        try:
            requested_check_timeout = kwargs.get("timeout_s")
            if requested_check_timeout is not None:
                owned_lock_timeout_s = outer_guard_timeout_s(
                    max(0.05, float(requested_check_timeout))
                )
        except (TypeError, ValueError):
            owned_lock_timeout_s = None

        operation_task = create_result_only_deadline_task(run_with_owned_lock())
        operation_task.add_done_callback(
            mark_runtime_owned_callback(release_owned_lock_once)
        )
        try:
            return await await_with_strict_deadline(
                operation_task,
                timeout_s=owned_lock_timeout_s,
                deadline_monotonic=float(deadline_monotonic or 0.0),
                operation_label="mini_turn_lean_check",
                operation_ownership="result_only",
            )
        except asyncio.TimeoutError as exc:
            # Do NOT close ``awaitable`` here. The abandoned task is suspended
            # *inside* it, and closing a coroutine out from under its awaiting
            # task stops that task from ever completing -- which skips
            # ``run_with_owned_lock``'s ``finally``, the only path that
            # releases the Lean lock. Measured: with the close, the task stays
            # pending forever and the lock is held forever; without it, the
            # tail finishes and releases. That turned a recoverable
            # abandonment into a permanent lock leak invisible to the late-tail
            # recycler, starving every later consumer of the runner.
            #
            # An outer guard cannot reclaim a Lean check anyway: only the
            # checker's own timeout runs killpg + reap. Let the tail land.
            if not operation_task.done():
                _mark_lean_late_tail(
                    lock,
                    operation_task,
                    operation_label="mini_turn_lean_check",
                    release_lock=release_owned_lock_once,
                )
            if isinstance(exc, LeanVerificationDeadline):
                raise
            raise LeanVerificationDeadline(
                "Lean verification deferred at checker deadline"
            ) from exc
        except asyncio.CancelledError:
            if not operation_task.done():
                _mark_lean_late_tail(
                    lock,
                    operation_task,
                    operation_label="mini_turn_lean_check",
                    release_lock=release_owned_lock_once,
                )
            raise

    async def checked_with_layout_repair(
        statement: str,
        candidate: str,
        **kwargs: Any,
    ) -> tuple[Any, str]:
        result = await checked(statement, candidate, **kwargs)
        repaired = repair_single_line_by_tactic_block(candidate)
        if not repaired or not rejection_supports_single_line_layout_repair(result):
            return result, candidate
        repaired_result = await checked(statement, repaired, **kwargs)
        if bool(getattr(repaired_result, "ok", False)):
            return repaired_result, repaired
        return result, candidate

    # ---- 1. Primary check against conv.lean_preamble. ----
    primary_started = time.monotonic()
    goal_statement = str(
        goal_statement_override
        if goal_statement_override is not None
        else getattr(conv, "goal_statement", "")
    )

    proof_for_checks = str(proof or "")
    safe_goal_statement = goal_statement
    primary_source = "submitted"
    active_lift_feedback_result: Optional[Any] = None
    active_root_statement = (
        ""
        if goal_statement_override is not None
        or not bool(getattr(conv, "suppress_solution_placeholders", False))
        else _active_root_check_statement(
            root_statement=goal_statement,
            active_root_targets=active_root_targets,
        )
    )
    active_root_result: Optional[Any] = None

    if active_root_statement:
        active_root_result, proof_for_checks = await checked_with_layout_repair(
            active_root_statement,
            proof,
            lemmas=list(check_lemmas),
            preamble_override=getattr(conv, "lean_preamble", "") or "",
            check_kind="full",
        )
        primary_result = active_root_result
        primary_source = "active_root_target"
        safe_goal_statement = active_root_statement
        if bool(getattr(active_root_result, "ok", False)):
            lifted_candidates = _active_root_lifted_proofs(
                root_statement=goal_statement,
                proof=proof_for_checks,
                active_root_targets=active_root_targets,
            )
            if not lifted_candidates:
                primary_result = _synthetic_check_failure(
                    "active-root proof checked, but no root-shell lift could be "
                    "constructed for final verification"
                )
                active_lift_feedback_result = primary_result
                primary_source = "active_root_lift"
            for lifted_proof in lifted_candidates:
                try:
                    lifted_result, lifted_proof = await checked_with_layout_repair(
                        goal_statement,
                        lifted_proof,
                        lemmas=list(check_lemmas),
                        preamble_override=(
                            getattr(conv, "lean_preamble", "") or ""
                        ),
                        check_kind="full",
                    )
                except LeanVerificationDeadline as exc:
                    # The submitted active-target proof already passed. Keep
                    # that paid result eligible for the same verifier-only
                    # recovery lane used by an interrupted answer-safe check;
                    # only the deterministic root-shell lift remains.
                    raise AnswerSafeRecheckInfrastructureError(
                        "active-root lift deferred at the enclosing deadline",
                        primary_result=active_root_result,
                    ) from exc
                active_lift_feedback_result = lifted_result
                proof_for_checks = lifted_proof
                safe_goal_statement = goal_statement
                primary_result = lifted_result
                primary_source = "active_root_lift"
                if bool(getattr(lifted_result, "ok", False)):
                    break
    else:
        primary_result, proof_for_checks = await checked_with_layout_repair(
            goal_statement,
            proof,
            lemmas=list(check_lemmas),
            preamble_override=getattr(conv, "lean_preamble", "") or "",
            check_kind="full",
        )
    primary_elapsed_s = round(time.monotonic() - primary_started, 3)

    # ---- 2. Answer-safe recheck (when needed AND not skipped). ----
    answer_safe_recheck_needed = primitives["needs_recheck"](conv)

    safe_result: Optional[Any] = None
    safe_elapsed_s: Optional[float] = None
    lean_feedback_error: Optional[str] = None

    if answer_safe_recheck_needed:
        feedback_started = time.monotonic()
        try:
            feedback_lemmas = _answer_safe_recheck_lemmas(
                context_helpers=context_helpers,
                helpers=helpers,
                conv=conv,
                primitives=primitives,
            )
            safe_result = await checked(
                safe_goal_statement,
                proof_for_checks,
                lemmas=feedback_lemmas,
                preamble_override=getattr(conv, "preamble", "") or "",
                check_kind="full",
            )
        except LeanVerificationDeadline as exc:
            # Preserve the already accepted primary result for callers that
            # own a verifier-only answer-safe replay.  Root-tool callers can
            # still distinguish the deadline through ``__cause__`` and defer
            # their durable closure frame without classifying the proof.
            raise AnswerSafeRecheckInfrastructureError(
                "answer-safe Lean recheck deferred at the enclosing deadline",
                primary_result=primary_result,
            ) from exc
        except Exception as exc:
            raise AnswerSafeRecheckInfrastructureError(
                "answer-safe Lean recheck infrastructure failed: "
                f"{type(exc).__name__}: {exc}",
                primary_result=primary_result,
            ) from exc
        safe_elapsed_s = round(time.monotonic() - feedback_started, 3)

    # ---- 3. Acceptance gating (mirrors mini_prover.py:4381-4405). ----
    accepted = bool(primary_result.ok)
    decision_result: Any = primary_result

    if primary_result.ok and answer_safe_recheck_needed:
        if safe_result is not None and safe_result.ok:
            decision_result = safe_result
            accepted = True
        else:
            # Hidden-answer leak class: do NOT accept a proof that only
            # works with the non-visible checker preamble.
            decision_result = safe_result
            accepted = False
            if decision_result is None:
                decision_result = SimpleNamespace(
                    ok=False,
                    output=(
                        "answer-safe Lean recheck failed; non-visible checker "
                        "preamble acceptance was ignored"
                    ),
                    returncode=1,
                    parsed=None,
                )

    # ---- 4. Feedback selection (mirrors mini_prover.py:4468-4479). ----
    feedback_result: Optional[Any] = decision_result if not accepted else None
    feedback_source = "primary_check"
    if not accepted and primary_source == "active_root_target":
        feedback_source = "active_root_target_check"
    if (
        not accepted
        and active_lift_feedback_result is not None
        and primary_source == "active_root_lift"
    ):
        feedback_result = active_lift_feedback_result
        feedback_source = "active_root_lift_check"

    if not accepted and answer_safe_recheck_needed:
        if (
            primary_source == "active_root_lift"
            and active_lift_feedback_result is not None
            and not bool(getattr(primary_result, "ok", False))
        ):
            if safe_result is not None and not safe_result.ok:
                feedback_result = safe_result
                feedback_source = "active_root_lift_answer_safe_check"
            else:
                feedback_result = active_lift_feedback_result
                feedback_source = "active_root_lift_check"
        elif safe_result is not None and not safe_result.ok:
            feedback_result = safe_result
            feedback_source = (
                "active_root_lift_answer_safe_check"
                if primary_source == "active_root_lift"
                else "answer_safe_check"
            )
        elif safe_result is not None and safe_result.ok:
            feedback_result = primary_result
            feedback_source = "primary_check_with_answer_safe_pass"
        else:
            feedback_result = None
            feedback_source = "answer_safe_check_failed"

    return LeanVerdict(
        accepted=accepted,
        primary_result=primary_result,
        safe_result=safe_result,
        feedback_result=feedback_result,
        feedback_source=feedback_source,
        primary_elapsed_s=primary_elapsed_s,
        safe_elapsed_s=safe_elapsed_s,
        lean_feedback_error=lean_feedback_error,
        accepted_proof=proof_for_checks if accepted else None,
        primary_source=primary_source,
        active_root_statement=active_root_statement,
        active_root_result=active_root_result,
    )
