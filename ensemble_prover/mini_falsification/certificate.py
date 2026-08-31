"""Authoritative Lean replay and axiom audit for counterexamples."""

from __future__ import annotations

import inspect
import hashlib
import re
from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping, Sequence

from ..deadline_guard import await_with_strict_deadline, invoke_with_strict_deadline
from ..falsification_cursor_identity import (
    RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES,
)
from ..lean_parser import canonical_error_type
from ..utils import strip_lean_noncode_for_token_checks
from .lean_check import safe_helper_sources
from .model import (
    CounterexampleCandidate,
    LeanCounterexampleCertificate,
    TrustLevel,
    authoritative_certificate_record_is_valid,
    content_hash,
)
from .policy import FalsificationPolicy


_DEPENDS_RE = re.compile(r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]")
_NONE_RE = re.compile(r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms")

# Process-local admission receipts. Serialized certificate fields are
# deliberately forgeable data; only this module adds a content identity after
# the corresponding proof has passed both fresh Lean replay and the trusted
# axiom audit. The set is intentionally not serialized, so process resume must
# replay pending certificates before they regain authority.
_AUTHORITATIVE_CERTIFICATE_RECEIPTS: set[tuple[str, str]] = set()


class CertificationStatus(str, Enum):
    """Outcome of replaying one full-negation proof at the trust boundary."""

    AUTHORITATIVE = "authoritative"
    DEFINITIVE_REJECTION = "definitive_rejection"
    RETRYABLE_INFRASTRUCTURE = "retryable_infrastructure"


@dataclass(frozen=True)
class CertificationResult:
    status: CertificationStatus
    certificate: LeanCounterexampleCertificate | None = None
    reason: str = ""

    @property
    def authoritative(self) -> bool:
        return bool(
            self.status is CertificationStatus.AUTHORITATIVE
            and self.certificate is not None
            and self.certificate.authoritative
        )

    @property
    def retryable(self) -> bool:
        return self.status is CertificationStatus.RETRYABLE_INFRASTRUCTURE


def authoritative_certificate_has_process_receipt(
    certificate: Any,
    *,
    target_environment_hash: str,
) -> bool:
    """Return whether this exact certificate content was minted this process."""

    if certificate is None or not bool(getattr(certificate, "authoritative", False)):
        return False
    try:
        certificate_hash = str(
            certificate.to_record().get("certificate_hash", "") or ""
        )
    except Exception:
        return False
    return (
        certificate_hash,
        str(target_environment_hash or "").strip(),
    ) in _AUTHORITATIVE_CERTIFICATE_RECEIPTS


def authoritative_certificate_record_has_process_receipt(
    certificate_record: Mapping[str, Any],
    *,
    target_environment_hash: str,
) -> bool:
    """Check a single materialized certificate record against minted receipts."""

    record = dict(certificate_record or {})
    if not authoritative_certificate_record_is_valid(record):
        return False
    certificate_hash = str(record.get("certificate_hash") or "")
    return (
        certificate_hash,
        str(target_environment_hash or "").strip(),
    ) in _AUTHORITATIVE_CERTIFICATE_RECEIPTS


def _record_authoritative_certificate_receipt(
    certificate: LeanCounterexampleCertificate,
    *,
    target_environment_hash: str,
) -> None:
    certificate_hash = str(
        certificate.to_record().get("certificate_hash", "") or ""
    )
    environment_hash = str(target_environment_hash or "").strip()
    if certificate_hash and environment_hash:
        _AUTHORITATIVE_CERTIFICATE_RECEIPTS.add(
            (certificate_hash, environment_hash)
        )


def _safe_graph_observation_term(term: str, vertex_type: str) -> bool:
    """Accept only the closed vertex literals emitted by graph generators."""

    value = str(term or "").strip()
    carrier = str(vertex_type or "").strip()
    if value in {"false", "true"}:
        return True
    typed = re.fullmatch(
        r"\(\s*(false|true|[0-9]+)\s*:\s*(.*?)\s*\)",
        value,
    )
    if typed is None or typed.group(2) != carrier:
        return False
    literal = typed.group(1)
    if literal.isdigit():
        return True
    # Typed Bool literals are generated only for a closed transparent carrier
    # alias such as ``abbrev V := Bool``.  Restrict the annotation to the same
    # already-validated identifier grammar; no arbitrary Lean term or type
    # syntax crosses into the generated proof.
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", carrier))


def _function_negation_proof(candidate: CounterexampleCandidate) -> str:
    """Reconstruct the one audited function-spine proof recipe."""

    metadata = dict(candidate.metadata)
    if (
        candidate.engine != "function"
        or metadata.get("function_spine_replay") is not True
        or len(candidate.concrete_statement) > 20_000
    ):
        return ""
    raw_arguments = metadata.get("function_application_arguments")
    raw_hypotheses = metadata.get("function_hypothesis_names")
    if not isinstance(raw_arguments, (list, tuple)) or not isinstance(
        raw_hypotheses, (list, tuple)
    ):
        return ""
    arguments = tuple(str(item or "").strip() for item in raw_arguments)
    hypotheses = tuple(str(item or "").strip() for item in raw_hypotheses)
    if (
        not arguments
        or len(arguments) > 32
        or len(hypotheses) > 24
        or any(not item or len(item) > 512 for item in arguments)
        or any(
            re.fullmatch(r"h_mini_function_probe_[0-9]+", item) is None
            for item in hypotheses
        )
        or any(item not in arguments for item in hypotheses)
    ):
        return ""
    application = " ".join(f"({argument})" for argument in arguments)
    proof_lines = [
        "by",
        "  intro h_mini_function_claim",
        f"  have h_mini_concrete : ({candidate.concrete_statement}) := by",
    ]
    if hypotheses:
        proof_lines.append(f"    intro {' '.join(hypotheses)}")
    proof_lines.extend(
        (
            f"    exact h_mini_function_claim {application}",
            f"  have h_mini_neg : ¬ ({candidate.concrete_statement}) := by",
            "    norm_num [StrictMonoOn] <;> aesop",
            "  exact h_mini_neg h_mini_concrete",
        )
    )
    return "\n".join(proof_lines)


def _right_pi_negation_proof(candidate: CounterexampleCandidate) -> str:
    """Reconstruct a mixed data/proof Pi specialization sequentially.

    Sequential application is intentional: later binder types may depend on
    earlier witnesses or proof slots, and a flattened application assembled by
    surface substitution can move those terms outside their valid scope.
    """

    metadata = dict(candidate.metadata)
    if (
        candidate.engine != "function"
        or metadata.get("right_pi_replay") is not True
        or len(candidate.concrete_statement) > 20_000
    ):
        return ""
    raw_arguments = metadata.get("right_pi_application_arguments")
    raw_hypotheses = metadata.get("right_pi_hypothesis_names")
    raw_proof_aliases = metadata.get("right_pi_proof_aliases")
    plan_hash = str(metadata.get("right_pi_plan_hash") or "").strip()
    candidate_index = metadata.get("right_pi_candidate_index")
    if (
        not isinstance(raw_arguments, (list, tuple))
        or not isinstance(raw_hypotheses, (list, tuple))
        or not isinstance(raw_proof_aliases, (list, tuple))
    ):
        return ""
    arguments = tuple(str(item or "").strip() for item in raw_arguments)
    hypotheses = tuple(str(item or "").strip() for item in raw_hypotheses)
    proof_aliases = tuple(str(item or "").strip() for item in raw_proof_aliases)
    if (
        not arguments
        or len(arguments) > 64
        or len(hypotheses) > 32
        or any(not item for item in arguments)
        or sum(len(item) for item in arguments)
        > RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES
        or any(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", item) is None
            for item in hypotheses
        )
        or any(item not in arguments for item in hypotheses)
        or proof_aliases != hypotheses
        or re.fullmatch(r"[0-9a-f]{64}", plan_hash) is None
        or not isinstance(candidate_index, int)
        or isinstance(candidate_index, bool)
        or candidate_index < 0
    ):
        return ""
    proof_lines = [
        "by",
        "  intro h_mini_right_pi_claim",
        f"  have h_mini_concrete : ({candidate.concrete_statement}) := by",
    ]
    if hypotheses:
        proof_lines.append(f"    intro {' '.join(hypotheses)}")
    proof_lines.append("    have h_mini_right_pi_step_0 := h_mini_right_pi_claim")
    for index, argument in enumerate(arguments):
        proof_lines.append(
            f"    have h_mini_right_pi_step_{index + 1} := "
            f"h_mini_right_pi_step_{index} ({argument})"
        )
    proof_lines.extend(
        (
            f"    exact h_mini_right_pi_step_{len(arguments)}",
            f"  have h_mini_neg : ¬ ({candidate.concrete_statement}) := by",
            "    norm_num [StrictMonoOn] <;> simp_all <;> omega",
            "  exact h_mini_neg h_mini_concrete",
        )
    )
    return "\n".join(proof_lines)


def _exact_exp_square_derivative_negation_proof(
    candidate: CounterexampleCandidate,
) -> str:
    """Replay the exp-square contradiction through the candidate's typed Pi."""

    metadata = dict(candidate.metadata)
    if metadata.get("exact_exp_square_derivative_refutation") is not True:
        return ""
    # The generic builder is also the bounded structural validator for these
    # application arguments and proof aliases.  The specialized tail below
    # replaces only its arithmetic tactic, not its typed telescope replay.
    if not _right_pi_negation_proof(candidate):
        return ""
    raw_arguments = metadata.get("right_pi_application_arguments")
    raw_hypotheses = metadata.get("right_pi_hypothesis_names")
    if not isinstance(raw_arguments, (list, tuple)) or not isinstance(
        raw_hypotheses, (list, tuple)
    ):
        return ""
    arguments = tuple(str(item or "").strip() for item in raw_arguments)
    hypotheses = tuple(str(item or "").strip() for item in raw_hypotheses)
    lines = [
        "by",
        "  intro H",
        f"  have h_mini_concrete : ({candidate.concrete_statement}) := by",
    ]
    if hypotheses:
        lines.append(f"    intro {' '.join(hypotheses)}")
    lines.append("    have h_mini_right_pi_step_0 := H")
    for index, argument in enumerate(arguments):
        lines.append(
            f"    have h_mini_right_pi_step_{index + 1} := "
            f"h_mini_right_pi_step_{index} ({argument})"
        )
    lines.append(f"    exact h_mini_right_pi_step_{len(arguments)}")
    proof_arguments = " ".join("(by simp)" for _ in hypotheses)
    lines.extend(
        (
            f"  have bad := h_mini_concrete {proof_arguments}".rstrip(),
            "  have hdf : deriv (fun x : ℝ => Real.exp (x ^ 2)) 1 = "
            "2 * Real.exp 1 := by",
            "    convert ((hasDerivAt_pow 2 (1 : ℝ)).exp.deriv) using 1 "
            "<;> norm_num <;> ring",
            "  have hdg : deriv (fun x : ℝ => Real.exp (-(x ^ 2))) 1 = "
            "-2 * Real.exp (-1) := by",
            "    convert ((hasDerivAt_pow 2 (1 : ℝ)).neg.exp.deriv) using 1 "
            "<;> norm_num <;> ring",
            "  dsimp at bad",
            "  rw [hdf, hdg] at bad",
            "  norm_num at bad",
            "  have he : Real.exp 1 * Real.exp (-1) = 1 := by",
            "    rw [← Real.exp_add]",
            "    norm_num",
            "  nlinarith",
        )
    )
    return "\n".join(lines)


def _exact_polynomial_integral_negation_proof(
    candidate: CounterexampleCandidate,
) -> str:
    """Build the bounded FTC replay emitted by the exact integral parser."""

    metadata = dict(candidate.metadata)
    if (
        candidate.engine != "function"
        or metadata.get("function_spine_replay") is not True
        or metadata.get("exact_polynomial_integral_probe") is not True
        or len(candidate.concrete_statement) > 20_000
    ):
        return ""
    raw_arguments = metadata.get("function_application_arguments")
    raw_hypotheses = metadata.get("function_hypothesis_names")
    raw_steps = metadata.get("exact_integral_certification_steps")
    raw_hypothesis_proofs = metadata.get("exact_identity_hypothesis_proofs")
    raw_top_level_integral_names = metadata.get("exact_top_level_integral_names")
    if (
        not isinstance(raw_arguments, (list, tuple))
        or not isinstance(raw_hypotheses, (list, tuple))
        or not isinstance(raw_steps, (list, tuple))
        or not isinstance(raw_hypothesis_proofs, (list, tuple))
        or not isinstance(raw_top_level_integral_names, (list, tuple))
    ):
        return ""
    arguments = tuple(str(item or "").strip() for item in raw_arguments)
    hypotheses = tuple(str(item or "").strip() for item in raw_hypotheses)
    steps = tuple(str(item or "") for item in raw_steps)
    hypothesis_proofs = tuple(str(item or "").strip() for item in raw_hypothesis_proofs)
    top_level_integral_names = tuple(
        str(item or "").strip() for item in raw_top_level_integral_names
    )
    safe_hypothesis_proof = re.compile(
        r"(?:\(by fun_prop\)|"
        r"\(by exact strictMono_id\.strictMonoOn\)|"
        r"\(by intro [A-Za-z_][A-Za-z0-9_']* hmem; "
        r"exact le_trans \(by norm_num : \(0 : ℝ\) ≤ -?[0-9]+\) hmem\.1\))"
    )
    if (
        not arguments
        or not steps
        or len(steps) > 1_024
        or sum(len(item) for item in steps) > 40_000
        or len(hypothesis_proofs) != len(hypotheses)
        or any("\n" in item or "\r" in item for item in steps)
        or any(
            re.search(
                r"(?<![A-Za-z0-9_'])"
                r"(?:sorry|admit|native_decide|axiom|constant|unsafe|"
                r"run_tac|run_cmd|set_option|import|theorem|lemma)"
                r"(?![A-Za-z0-9_'])",
                item,
            )
            for item in steps
        )
        or any(
            safe_hypothesis_proof.fullmatch(item) is None for item in hypothesis_proofs
        )
        or any(
            re.fullmatch(r"h_mini_function_probe_[0-9]+", item) is None
            for item in hypotheses
        )
        or any(item not in arguments for item in hypotheses)
        or not top_level_integral_names
        or any(
            re.fullmatch(r"h_mini_exact_integral_[0-9]+", item) is None
            for item in top_level_integral_names
        )
    ):
        return ""
    application = " ".join(f"({argument})" for argument in arguments)
    proof_lines = [
        "by",
        "  intro h_mini_function_claim",
        f"  have h_mini_concrete : ({candidate.concrete_statement}) := by",
    ]
    if hypotheses:
        proof_lines.append(f"    intro {' '.join(hypotheses)}")
    proof_lines.extend(
        (
            f"    exact h_mini_function_claim {application}",
            f"  have h_mini_neg : ¬ ({candidate.concrete_statement}) := by",
            "    intro h_mini_exact_claim",
            "    have h_mini_exact_contradiction := "
            + "h_mini_exact_claim "
            + " ".join(hypothesis_proofs),
        )
    )
    proof_lines.extend(f"    {line}" for line in steps)
    lemma_names = tuple(
        match.group(1)
        for line in steps
        for match in [re.fullmatch(r"have (h_mini_exact_integral_[0-9]+).*", line)]
        if match is not None
    )
    if not lemma_names:
        return ""
    if any(item not in lemma_names for item in top_level_integral_names):
        return ""
    proof_lines.extend(
        (
            "    dsimp only at h_mini_exact_contradiction",
            "    simp_rw ["
            + ", ".join(top_level_integral_names)
            + "] at h_mini_exact_contradiction",
            "    norm_num [integral_pow] at h_mini_exact_contradiction",
            "  exact h_mini_neg h_mini_concrete",
        )
    )
    return "\n".join(proof_lines)


def _proof_candidates(candidate: CounterexampleCandidate) -> tuple[str, ...]:
    witnesses = " ".join(candidate.witness_terms)
    metadata = dict(candidate.metadata)
    proofs: list[str] = []
    exact_exp_square_proof = _exact_exp_square_derivative_negation_proof(candidate)
    if exact_exp_square_proof:
        return (exact_exp_square_proof,)
    right_pi_proof = _right_pi_negation_proof(candidate)
    if right_pi_proof:
        # This recipe is derived from the same typed Pi plan used to create the
        # concrete proposition.  A rejection is an invariant/recipe failure;
        # generic witness interpolation must not silently consume the pending
        # candidate or multiply the certification watchdog sevenfold.
        return (right_pi_proof,)
    exact_integral_proof = _exact_polynomial_integral_negation_proof(candidate)
    if exact_integral_proof:
        proofs.append(exact_integral_proof)
    function_proof = _function_negation_proof(candidate)
    if function_proof:
        proofs.append(function_proof)
    if witnesses:
        if metadata.get("complex_exact_replay") is True:
            proofs.append(
                "by\n  intro h\n  have hbad := @h "
                + witnesses
                + "\n  norm_num [pow_succ] at hbad"
                + "\n  ring_nf at hbad"
                + "\n  norm_num [Complex.I_mul_I] at hbad"
            )
        vertex_type = str(metadata.get("graph_vertex_type") or "").strip()
        safe_vertex_type = bool(
            re.fullmatch(
                r"(?:Bool|Fin\s+[0-9]+|[A-Za-z_][A-Za-z0-9_']*)",
                vertex_type,
            )
        )
        observation_pairs = metadata.get("graph_observation_pairs")
        if safe_vertex_type and isinstance(observation_pairs, (list, tuple)):
            for pair in observation_pairs:
                if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                    continue
                left, right = (str(item or "").strip() for item in pair)
                if not _safe_graph_observation_term(
                    left, vertex_type
                ) or not _safe_graph_observation_term(right, vertex_type):
                    continue
                proofs.append(
                    "by\n  intro h\n  have heq := @h "
                    + witnesses
                    + "\n  have hbad := congrArg "
                    + f"(fun G : SimpleGraph ({vertex_type}) => G.Adj {left} {right}) heq"
                    + "\n  simp at hbad"
                )
        proofs.extend(
            (
                "by\n  intro h\n  have hbad := @h "
                + witnesses
                + "\n  norm_num at hbad",
                "by\n  intro h\n  have hbad := @h " + witnesses + "\n  simp at hbad",
                "by\n  intro h\n  have hbad := @h "
                + witnesses
                + "\n  decide +kernel at hbad",
            )
        )
    proofs.extend(("by\n  norm_num", "by\n  simp", "by\n  decide +kernel"))
    return tuple(dict.fromkeys(proofs))


async def _call_check(
    lean: Any,
    *,
    statement: str,
    proof: str,
    preamble: str,
    helpers: Sequence[Any],
    timeout_s: float,
    filter_authority_helpers: bool = True,
) -> tuple[bool, str, str]:
    check = getattr(lean, "check", None)
    if check is None:
        return False, "lean object has no check method", "infrastructure"
    kwargs = {
        "preamble_override": preamble,
        "timeout_s": timeout_s,
        "fast_fail_timeout_s": min(timeout_s, max(1.0, timeout_s / 3.0)),
        "check_kind": "mini_falsification_certificate",
    }
    try:
        signature = inspect.signature(check)
        if not any(
            parameter.kind == inspect.Parameter.VAR_KEYWORD
            for parameter in signature.parameters.values()
        ):
            kwargs = {
                key: value
                for key, value in kwargs.items()
                if key in signature.parameters
            }
    except (TypeError, ValueError):
        pass
    result = await invoke_with_strict_deadline(
        check,
        f"¬ ({statement})",
        proof,
        (
            safe_helper_sources(helpers)
            if filter_authority_helpers
            else [
                str(item or "").strip()
                for item in helpers
                if str(item or "").strip()
            ]
        ),
        guard_timeout_s=timeout_s,
        operation_ownership="result_only",
        **kwargs,
    )
    output = str(getattr(result, "output", "") or "")
    parsed = getattr(result, "parsed", None)
    ok = bool(getattr(result, "ok", False))
    if ok:
        return True, output, ""
    if bool(getattr(parsed, "infra_failure", False)):
        return False, output, "infrastructure"
    # A nonzero subprocess result is a definitive proof rejection only when
    # Lean actually emitted structured diagnostics/goals.  Lake/project setup,
    # toolchain, and subprocess failures commonly return ``ok=False`` with no
    # Lean diagnostic at all (for example a failed dependency checkout).
    # Conservatively keep those retryable; serialized disproof evidence must
    # not be discarded merely because the verifier never reached elaboration.
    lean_error = canonical_error_type(parsed) if parsed is not None else ""
    if lean_error == "timeout" or bool(getattr(parsed, "timeout", False)):
        # Heartbeat/time-limit exhaustion is a real Lean diagnostic, but it is
        # not evidence that the persisted proof is invalid.  A larger resource
        # budget or recovered backend may accept the identical proof.
        return False, output, "infrastructure"
    has_lean_diagnostic = bool(
        parsed is not None
        and (
            lean_error
            or getattr(parsed, "diagnostics", ())
            or getattr(parsed, "remaining_goals", ())
            or int(getattr(parsed, "unsolved_goal_count", 0) or 0) > 0
        )
    )
    return False, output, "" if has_lean_diagnostic else "infrastructure"


def _negation_proof_rejection_reason(proof: str) -> str:
    proof_text = str(proof or "")
    executable_proof = strip_lean_noncode_for_token_checks(proof_text)
    if re.search(
        r"(?<![A-Za-z0-9_'])"
        r"(?:sorry|admit|native_decide|axiom|constant|unsafe|run_tac)"
        r"(?![A-Za-z0-9_'])",
        executable_proof,
    ):
        return "proof contains a forbidden trust-boundary construct"
    if not proof_text.lstrip().startswith("by"):
        return "proof is not a Lean tactic proof"
    if re.search(
        r"(?m)^\s*(?:import|theorem|lemma|def|abbrev|instance|namespace|"
        r"section|end|set_option|#\w+)\b",
        executable_proof,
    ):
        return "proof contains a forbidden top-level command"
    return ""


async def check_negation_proof_in_feedback_world(
    lean: Any,
    *,
    statement: str,
    proof: str,
    preamble: str,
    helpers: Sequence[Any],
    timeout_s: float,
) -> tuple[bool, bool, str]:
    """Check prompt-visible validity without granting mathematical authority.

    Feedback helper signatures may deliberately be rendered as ``axiom``
    declarations to hide their proofs. They are allowed only in this
    non-authoritative replay; the independent authority replay below still
    filters them and performs the trusted axiom audit against verified bodies.
    """

    rejection_reason = _negation_proof_rejection_reason(proof)
    if rejection_reason:
        return False, False, rejection_reason
    try:
        ok, output, error_kind = await await_with_strict_deadline(
            _call_check(
                lean,
                statement=statement,
                proof=proof,
                preamble=preamble,
                helpers=helpers,
                timeout_s=timeout_s,
                filter_authority_helpers=False,
            ),
            timeout_s=timeout_s + 0.5,
            operation_ownership="result_only",
        )
    except Exception as exc:
        return (
            False,
            True,
            f"visible Lean replay infrastructure failed: {type(exc).__name__}: {exc}"[
                :500
            ],
        )
    if error_kind:
        return False, True, f"visible Lean replay infrastructure failed: {output}"[:500]
    return ok, False, ("" if ok else "Lean rejected the prompt-visible negation")


def _parse_axioms(output: str, theorem_name: str) -> tuple[str, ...] | None:
    for match in _DEPENDS_RE.finditer(str(output or "")):
        if match.group(1).strip() == theorem_name:
            return tuple(
                item.strip() for item in match.group(2).split(",") if item.strip()
            )
    for match in _NONE_RE.finditer(str(output or "")):
        if match.group(1).strip() == theorem_name:
            return ()
    return None


async def _axiom_audit(
    lean: Any,
    *,
    statement: str,
    proof: str,
    preamble: str,
    helpers: Sequence[Any],
    timeout_s: float,
) -> tuple[tuple[str, ...] | None, str]:
    custom = getattr(lean, "audit_proof_axioms", None)
    if (
        callable(custom)
        and getattr(lean, "_mini_falsification_trusted_audit", False) is True
    ):
        result = await invoke_with_strict_deadline(
            custom,
            statement,
            proof,
            safe_helper_sources(helpers),
            preamble=preamble,
            timeout_s=timeout_s,
            guard_timeout_s=timeout_s,
            operation_ownership="result_only",
        )
        if isinstance(result, tuple) and len(result) == 2:
            return tuple(result[0]) if result[0] is not None else None, str(
                result[1] or ""
            )
    execute = getattr(lean, "_execute_content", None)
    resolve_preamble = getattr(lean, "_resolve_preamble", None)
    if not callable(execute) or not callable(resolve_preamble):
        return None, "axiom audit backend unavailable"
    theorem_name = (
        "mini_falsification_cert_"
        + content_hash({"statement": statement, "proof": proof})[:16]
    )
    resolved_preamble = await invoke_with_strict_deadline(
        resolve_preamble,
        preamble,
        proof_code=proof,
        guard_timeout_s=timeout_s,
        operation_ownership="result_only",
    )
    helper_block = "\n".join(safe_helper_sources(helpers))
    content = (
        f"{resolved_preamble}\n\n{helper_block}\n\n"
        f"theorem {theorem_name} : ¬ ({statement}) := {proof}\n\n"
        f"#print axioms {theorem_name}\n"
    )
    execution, _path, _backend = await invoke_with_strict_deadline(
        execute,
        mode="mini_falsification_axiom_audit",
        goal_name=theorem_name,
        content=content,
        timeout_s=timeout_s,
        fast_fail_timeout_s=min(timeout_s, max(1.0, timeout_s / 3.0)),
        warning_as_error=False,
        guard_timeout_s=timeout_s,
        operation_ownership="result_only",
    )
    returncode, output = execution
    if int(returncode) != 0:
        return None, str(output or "")
    return _parse_axioms(str(output or ""), theorem_name), str(output or "")


async def certify_candidate(
    lean: Any,
    *,
    statement: str,
    candidate: CounterexampleCandidate,
    preamble: str,
    helpers: Sequence[Any],
    policy: FalsificationPolicy,
    environment_hash: str = "",
) -> LeanCounterexampleCertificate | None:
    """Compatibility wrapper returning the strongest certificate obtained."""

    result = await certify_candidate_result(
        lean,
        statement=statement,
        candidate=candidate,
        preamble=preamble,
        helpers=helpers,
        policy=policy,
        environment_hash=environment_hash,
    )
    return result.certificate


async def certify_candidate_result(
    lean: Any,
    *,
    statement: str,
    candidate: CounterexampleCandidate,
    preamble: str,
    helpers: Sequence[Any],
    policy: FalsificationPolicy,
    environment_hash: str = "",
) -> CertificationResult:
    """Classify full-negation certification across all proof recipes.

    An authoritative proof wins even if an earlier recipe hit infrastructure.
    If none succeeds, any retryable result wins over all-definitive rejection
    so callers do not permanently consume the candidate witness.
    """

    retryable: CertificationResult | None = None
    definitive: CertificationResult | None = None
    diagnostic_certificate: LeanCounterexampleCertificate | None = None
    for proof in _proof_candidates(candidate):
        result = await certify_negation_proof_result(
            lean,
            statement=statement,
            proof=proof,
            candidate=candidate,
            preamble=preamble,
            helpers=helpers,
            policy=policy,
            environment_hash=environment_hash,
        )
        if result.authoritative:
            return result
        if (
            result.certificate is not None
            and not result.certificate.authoritative
            and diagnostic_certificate is None
        ):
            diagnostic_certificate = result.certificate
        if result.retryable:
            if retryable is None or (
                retryable.certificate is None and result.certificate is not None
            ):
                retryable = result
            continue
        if definitive is None or (
            definitive.certificate is None and result.certificate is not None
        ):
            definitive = result
    if retryable is not None:
        return CertificationResult(
            retryable.status,
            certificate=retryable.certificate or diagnostic_certificate,
            reason=retryable.reason,
        )
    if definitive is not None:
        return CertificationResult(
            definitive.status,
            certificate=definitive.certificate or diagnostic_certificate,
            reason=definitive.reason,
        )
    return CertificationResult(
        CertificationStatus.DEFINITIVE_REJECTION,
        reason="no admissible full-negation proof recipe was available",
    )


async def certify_negation_proof(
    lean: Any,
    *,
    statement: str,
    proof: str,
    candidate: CounterexampleCandidate,
    preamble: str,
    helpers: Sequence[Any],
    policy: FalsificationPolicy,
    environment_hash: str = "",
) -> LeanCounterexampleCertificate | None:
    """Compatibility wrapper returning the strongest certificate obtained."""

    result = await certify_negation_proof_result(
        lean,
        statement=statement,
        proof=proof,
        candidate=candidate,
        preamble=preamble,
        helpers=helpers,
        policy=policy,
        environment_hash=environment_hash,
    )
    return result.certificate


async def certify_negation_proof_result(
    lean: Any,
    *,
    statement: str,
    proof: str,
    candidate: CounterexampleCandidate,
    preamble: str,
    helpers: Sequence[Any],
    policy: FalsificationPolicy,
    environment_hash: str = "",
) -> CertificationResult:
    """Replay and classify rejection separately from retryable infrastructure.

    A successfully Lean-checked proof is retained as a non-authoritative
    certificate when the independent axiom audit is temporarily unavailable.
    This preserves diagnostics without allowing infrastructure failure to
    acquire mathematical authority.
    """

    proof_text = str(proof or "")
    rejection_reason = _negation_proof_rejection_reason(proof_text)
    if rejection_reason:
        return CertificationResult(
            CertificationStatus.DEFINITIVE_REJECTION,
            reason=rejection_reason,
        )
    try:
        ok, output, check_error_kind = await await_with_strict_deadline(
            _call_check(
                lean,
                statement=statement,
                proof=proof,
                preamble=preamble,
                helpers=helpers,
                timeout_s=policy.operation_timeout_s,
            ),
            timeout_s=policy.operation_timeout_s + 0.5,
            operation_ownership="result_only",
        )
    except Exception as exc:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            reason=f"Lean replay infrastructure failed: {type(exc).__name__}: {exc}"[
                :500
            ],
        )
    if check_error_kind:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            reason=f"Lean replay infrastructure failed: {output}"[:500],
        )
    if not ok:
        return CertificationResult(
            CertificationStatus.DEFINITIVE_REJECTION,
            reason="Lean rejected the persisted full-negation proof",
        )
    environment_identity = str(environment_hash or "").strip() or content_hash(
        {"preamble": preamble, "helpers": safe_helper_sources(helpers)}
    )

    def build_certificate(
        *,
        trust: TrustLevel,
        axioms: tuple[str, ...] = (),
        audit_output: str = "",
    ) -> LeanCounterexampleCertificate:
        return LeanCounterexampleCertificate(
            statement=statement,
            negated_statement=f"¬ ({statement})",
            proof_code=proof,
            witness_terms=candidate.witness_terms,
            concrete_statement=candidate.concrete_statement,
            lean_output=(audit_output or output)[:2000],
            axioms=axioms,
            trust=trust,
            environment_hash=environment_identity,
        )

    audit_output = ""
    try:
        audited, audit_output = await await_with_strict_deadline(
            _axiom_audit(
                lean,
                statement=statement,
                proof=proof,
                preamble=preamble,
                helpers=helpers,
                timeout_s=policy.operation_timeout_s,
            ),
            timeout_s=policy.operation_timeout_s + 0.5,
            operation_ownership="result_only",
        )
    except Exception as exc:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            certificate=build_certificate(trust=TrustLevel.LEAN_NEGATION_CHECKED),
            reason=f"axiom-audit infrastructure failed: {type(exc).__name__}: {exc}"[
                :500
            ],
        )
    if audited is None:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            certificate=build_certificate(
                trust=TrustLevel.LEAN_NEGATION_CHECKED,
                audit_output=audit_output,
            ),
            reason="axiom-audit infrastructure was unavailable or inconclusive",
        )
    if not set(audited).issubset(set(policy.allowed_axioms)):
        return CertificationResult(
            CertificationStatus.DEFINITIVE_REJECTION,
            certificate=build_certificate(
                trust=TrustLevel.LEAN_NEGATION_CHECKED,
                audit_output=audit_output,
            ),
            reason="axiom audit found dependencies outside the allowed policy",
        )
    certificate = build_certificate(
        trust=TrustLevel.LEAN_AXIOM_AUDITED,
        axioms=audited,
        audit_output=audit_output,
    )
    _record_authoritative_certificate_receipt(
        certificate,
        target_environment_hash=hashlib.sha256(
            str(preamble or "").encode("utf-8")
        ).hexdigest()[:16],
    )
    return CertificationResult(
        CertificationStatus.AUTHORITATIVE,
        certificate=certificate,
        reason="full negation passed Lean replay and axiom audit",
    )
