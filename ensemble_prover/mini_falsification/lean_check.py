"""Lean checks shared by heuristic engines and the certificate boundary."""

from __future__ import annotations

import inspect
import textwrap
import time
from typing import Any, Sequence

from ..deadline_guard import invoke_with_strict_deadline, outer_guard_timeout_s


def instance_probe_is_miss(error_kind: str) -> bool:
    """Whether a concrete-negation error is a bounded miss, not infrastructure.

    A tactic watchdog expiry means this witness is not a cheap counterexample.
    Retrying it as a backend crash re-taxes proving and never spends the
    prove-mode skip latch.
    """

    return str(error_kind or "") == "timeout"


def instance_probe_is_unconsumed(error_kind: str) -> bool:
    """Whether the engine must retry this witness with a full allowance."""

    return str(error_kind or "") in {"partial_timeout", "probe_deadline"}


def _deadline_bounded_probe_timeout_s(
    requested_timeout_s: float,
    deadline_monotonic: float,
) -> float:
    """Fit a Lean probe and its cleanup guard inside one engine deadline.

    A reduced allowance is an opportunity for a fast proof, not a completed
    coverage lease: callers must keep the cursor on a reduced-timeout expiry.
    """

    requested = max(0.0, float(requested_timeout_s or 0.0))
    deadline = float(deadline_monotonic or 0.0)
    if deadline <= 0.0:
        return requested
    remaining = max(0.0, deadline - time.monotonic())
    if remaining <= 0.0:
        return 0.0
    reserve = min(0.1, remaining * 0.1)
    safe_window = max(0.0, remaining - reserve)
    candidate = min(requested, safe_window)
    guard = float(outer_guard_timeout_s(candidate) or 0.0)
    if guard > safe_window and guard > 0.0:
        candidate *= (safe_window / guard) * 0.99
    return candidate if candidate >= 0.001 else 0.0


def safe_helper_sources(helpers: Sequence[Any]) -> list[str]:
    from ..finite_claim_check import _safe_helper_blocks

    return _safe_helper_blocks(helpers)


async def check_concrete_negation(
    lean: Any,
    *,
    concrete_statement: str,
    preamble: str,
    helpers: Sequence[Any],
    timeout_s: float,
    deadline_monotonic: float = 0.0,
    extra_tactics: Sequence[str] = (),
) -> tuple[bool, str, str]:
    """Return ``(proved, output, error_kind)`` for a concrete negation.

    ``native_decide`` is intentionally excluded: generated-code evaluation is
    useful as a hint but is outside Mini's durable proof trust boundary.
    """

    check = getattr(lean, "check", None)
    if check is None:
        return False, "lean object has no check method", "infrastructure"
    requested_timeout_s = max(0.0, float(timeout_s or 0.0))
    effective_timeout_s = requested_timeout_s
    check_self_bounded = True
    try:
        tactic_branches = [
            str(item or "").strip() for item in extra_tactics if str(item or "").strip()
        ]
        rendered_branches = []
        for branch in tactic_branches:
            lines = textwrap.dedent(branch).splitlines()
            rendered_branches.append(
                "  | " + lines[0] + "".join(f"\n    {line}" for line in lines[1:])
            )
        proof = "\n".join(
            (
                "by",
                "  first",
                *rendered_branches,
                "  | decide +kernel",
                "  | norm_num",
                "  | simp",
            )
        )
        helper_sources = safe_helper_sources(helpers)
        kwargs = {
            "preamble_override": str(preamble or ""),
            "timeout_s": requested_timeout_s,
            "fast_fail_timeout_s": min(
                requested_timeout_s,
                max(1.0, requested_timeout_s / 3.0),
            ),
            "check_kind": "mini_falsification_instance",
        }
        try:
            signature = inspect.signature(check)
            if not any(
                item.kind == inspect.Parameter.VAR_KEYWORD
                for item in signature.parameters.values()
            ):
                kwargs = {
                    key: value
                    for key, value in kwargs.items()
                    if key in signature.parameters
                }
        except (TypeError, ValueError):
            pass
        # Price the nested self-timeout after every synchronous preparation
        # step. The remaining margin must still exist when the guarded Lean
        # operation is actually dispatched, not merely when helper rendering
        # began.
        effective_timeout_s = _deadline_bounded_probe_timeout_s(
            requested_timeout_s,
            deadline_monotonic,
        )
        if deadline_monotonic > 0.0 and effective_timeout_s <= 0.0:
            return False, "engine deadline left no safe Lean probe window", "probe_deadline"
        check_self_bounded = "timeout_s" in kwargs
        if "timeout_s" in kwargs:
            kwargs["timeout_s"] = effective_timeout_s
        if "fast_fail_timeout_s" in kwargs:
            kwargs["fast_fail_timeout_s"] = min(
                effective_timeout_s,
                max(1.0, effective_timeout_s / 3.0),
            )
        result = await invoke_with_strict_deadline(
            check,
            f"¬ ({concrete_statement})",
            proof,
            helper_sources,
            # The check self-bounds at this same ``timeout_s`` (passed in
            # kwargs above), so arming the guard with it verbatim made the two
            # race. Losing that race is worse than losing a result here:
            # TimeoutError becomes error_kind="timeout", which
            # instance_probe_is_miss() scores as a MISS -- recording a real
            # counterexample as absent and spending the skip latch.
            guard_timeout_s=outer_guard_timeout_s(effective_timeout_s),
            guard_deadline_monotonic=float(deadline_monotonic or 0.0),
            operation_ownership="result_only",
            **kwargs,
        )
    except TimeoutError:
        error_kind = (
            "partial_timeout"
            if not check_self_bounded
            or effective_timeout_s + 1e-9 < requested_timeout_s
            else "timeout"
        )
        return False, "Lean instance-check watchdog expired", error_kind
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}", "infrastructure"
    output = str(getattr(result, "output", "") or "")
    parsed = getattr(result, "parsed", None)
    if bool(getattr(parsed, "infra_failure", False)):
        return False, output, "infrastructure"
    return bool(getattr(result, "ok", False)), output, ""
