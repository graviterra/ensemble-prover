"""Promote an authoritative child-goal negation proof to a falsified flag.

When a child session cannot prove a goal but produces a Lean-accepted proof of
its exact negation, this module certifies that evidence and stops the scheduler
from re-probing the impossible goal. The negation is replayed against the exact
target, forbidden trust constructs are rejected, and its printed axioms must be
within policy. Model prose and extraction heuristics can never mark a node
falsified without that certificate.
"""

from __future__ import annotations

import textwrap
import time
from typing import Any, Callable, Optional, Sequence, Tuple

from ensemble_prover.mini_falsification import (
    CounterexampleCandidate,
    FalsificationFinding,
    FalsificationOutcome,
    FalsificationPolicy,
    FalsificationReport,
    TargetKind,
)
from ensemble_prover.mini_falsification.certificate import (
    CertificationResult,
    CertificationStatus,
    check_negation_proof_in_feedback_world,
    certify_negation_proof_result,
)
from ensemble_prover.mini_falsification.lean_check import safe_helper_sources
from ensemble_prover.mini_falsification.service import falsification_environment_hash
from ensemble_prover.proof_dossier import (
    active_root_target_statement,
    active_root_targets_for_frame,
    text_hash,
)
from ensemble_prover.utils import _lean_lexical_skip_end
from ensemble_prover.deadline_guard import invoke_with_strict_deadline
from ensemble_prover.lean_parser import canonical_error_type

# Bounded replay window for the negation certificate. A ``¬statement`` replay may
# need omega/decide, so allow more than the 8s certifier default, but keep it
# capped so a pathological body cannot stall the (already-failed) prove path.
_CERTIFY_TIMEOUT_S = 30.0


def _original_target_parser(lean: Any, *, feedback: bool = False) -> Any:
    from ensemble_prover.lean_runner import LeanRunner
    from ensemble_prover.mini_session.recursive_helper_prover import (
        _RevocableRecursiveHelperCapability,
    )

    # Inspect only the known host fence for eligibility. Execute through the
    # original object so revocation before/after an await still takes effect.
    target = lean
    seen: set[int] = set()
    while type(target) is _RevocableRecursiveHelperCapability:
        if id(target) in seen:
            return None
        seen.add(id(target))
        target = _RevocableRecursiveHelperCapability._dispatch_capability_identity_token(target)
    if (
        not isinstance(target, LeanRunner)
        and getattr(target, "_mini_falsification_trusted_audit", False) is not True
    ):
        return None
    name = "check_feedback_proposition_type_raw" if feedback else "check_proposition_type_raw"
    parser = getattr(lean, name, None)
    if parser is None and feedback and not isinstance(target, LeanRunner):
        # Explicit trusted test adapters may retain the original parser API.
        parser = getattr(lean, "check_proposition_type_raw", None)
    return parser if callable(parser) else None


async def _admit_original_refutation_target(
    lean: Any,
    statement: str,
    preamble: str,
    helpers: Sequence[str],
    timeout_s: float,
    *,
    filter_authority_helpers: bool = True,
) -> Optional[CertificationResult]:
    """Parse the original Prop before adding any textual negation wrapper.

    Apostrophes are environment-dependent notation tokens as well as literal
    delimiters. The existing Lean preflight safely quotes the original source,
    parses it completely in the target scope, then checks its proposition type.
    This grants no disproof authority; independent replay and audit still follow.
    """
    try:
        parser = _original_target_parser(lean, feedback=not filter_authority_helpers) if "'" in statement else None
    except Exception as exc:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            reason=f"original target preflight unavailable: {type(exc).__name__}",
        )
    if parser is None:
        if "'" in statement:
            return CertificationResult(
                CertificationStatus.RETRYABLE_INFRASTRUCTURE,
                reason="original target requires unavailable Lean proposition preflight",
            )
        if _statement_is_interpolation_safe(statement):
            return None
        return CertificationResult(
            CertificationStatus.DEFINITIVE_REJECTION,
            reason="target contains unbalanced delimiters, comments, or an unterminated literal",
        )
    try:
        parsed, output, code = await invoke_with_strict_deadline(
            parser,
            statement,
            safe_helper_sources(helpers) if filter_authority_helpers else list(helpers),
            preamble_override=preamble,
            timeout_s=timeout_s,
            guard_timeout_s=timeout_s,
            operation_ownership="result_only",
        )
    except Exception as exc:
        return CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            reason=f"original target preflight infrastructure failed: {type(exc).__name__}",
        )
    if code == 0 and not getattr(parsed, "infra_failure", False):
        return None
    error_kind = canonical_error_type(parsed)
    infrastructure = (
        getattr(parsed, "infra_failure", False)
        or getattr(parsed, "timeout", False)
        or error_kind == "timeout"
        or not (error_kind or getattr(parsed, "diagnostics", ()))
    )
    return CertificationResult(
        (
            CertificationStatus.RETRYABLE_INFRASTRUCTURE
            if infrastructure
            else CertificationStatus.DEFINITIVE_REJECTION
        ),
        reason=(
            "original target preflight infrastructure failed: "
            if infrastructure
            else "Lean rejected the original proposition: "
        )
        + str(output)[:1000],
    )


def answer_safe_negation_feedback_context(
    conv: Any,
    *,
    acceptance_preamble: str,
    helpers: Sequence[str],
) -> Tuple[Optional[str], Tuple[str, ...]]:
    """Return the model-visible world that must also accept a negation.

    Older/restored conversations may not carry ``lean_preamble``.  Therefore
    the decision cannot rely only on the usual split-context detector: when
    solution placeholders are suppressed and the visible preamble differs
    from the supplied checker context, require the visible replay directly.
    """

    visible_preamble = str(getattr(conv, "preamble", "") or "")
    acceptance = str(acceptance_preamble or "")
    visible_differs = bool(
        visible_preamble.strip() != acceptance.strip()
        and bool(getattr(conv, "suppress_solution_placeholders", False))
    )
    try:
        from ensemble_prover.proof_state_executor import (
            _feedback_lemmas_for_answer_safe_recheck,
            _needs_answer_safe_feedback_check,
        )

        if not (visible_differs or _needs_answer_safe_feedback_check(conv)):
            return None, tuple(helpers or ())
        return (
            visible_preamble,
            tuple(_feedback_lemmas_for_answer_safe_recheck(helpers, conv)),
        )
    except Exception:
        if visible_differs:
            return visible_preamble, ()
        return None, tuple(helpers or ())


def _exact_statement_text(statement: Any) -> str:
    """Whitespace-only normalization used by the certificate linkage.

    Do not use a surface/canonical proposition key here.  A falsification
    certificate is authority for the exact Lean target that was replayed, not
    for a merely similar or profile-equivalent proposition.
    """

    # Preserve every interior byte. Collapsing whitespace changes Lean string
    # literals (for example ``"a  b"`` versus ``"a b"``) and can link a
    # certificate to a different proposition.
    return str(statement or "").strip()


def _active_root_negation_lift(
    *,
    dossier: Any,
    active_statement: str,
    active_negation_proof: str,
    preamble: str,
) -> Tuple[str, str]:
    """Build a candidate ``¬root`` proof from a certified ``¬active`` proof.

    The active target is accepted only when it belongs to the dossier's exact
    current answer-shell frame.  The returned proof is merely a candidate: it
    must cross the same independent Lean replay and axiom audit as every other
    root disproof before it can become durable authority.
    """

    root_statement = _exact_statement_text(
        getattr(dossier, "root_statement", "")
    )
    active = _exact_statement_text(active_statement)
    if not root_statement or not active or root_statement == active:
        return "", ""
    try:
        frame_helpers = tuple(dossier.verified_helper_blocks())
    except Exception:
        frame_helpers = ()
    framed_targets = active_root_targets_for_frame(
        dossier,
        root_statement=root_statement,
        preamble=str(preamble or ""),
        helper_blocks=frame_helpers,
        require_helper_context_hash_match=True,
    )
    framed_active = active_root_target_statement(
        framed_targets,
        require_single=True,
        require_no_hypotheses=False,
        include_hypotheses=True,
    )
    if _exact_statement_text(framed_active) != active:
        return "", ""
    try:
        from ensemble_prover.mini_session.turn.lean_check import (
            _solution_names_in_statement,
        )

        solution_names = _solution_names_in_statement(root_statement)
    except Exception:
        solution_names = []
    proof = str(active_negation_proof or "").strip()
    if not solution_names or not proof.startswith("by"):
        return "", ""
    simp_names = ", ".join(solution_names)
    lifted = "\n".join(
        [
            "by",
            "  intro h_mini_root_claim",
            f"  have h_mini_active_claim : ({active}) := by",
            f"    simpa [{simp_names}] using h_mini_root_claim",
            f"  have h_mini_not_active : ¬ ({active}) :=",
            textwrap.indent(proof, "    "),
            "  exact h_mini_not_active h_mini_active_claim",
        ]
    )
    return root_statement, lifted


def _direct_negation_proof_from_declaration(
    declaration: str,
    statement: str,
) -> str:
    """Extract the body of a declaration whose target is exactly ``¬statement``.

    The declaration itself must already have crossed a Lean acceptance
    boundary.  This parser is only an extraction convenience: the returned
    body is independently replayed and axiom-audited below before it can
    invalidate anything.
    """

    try:
        from ensemble_prover.mini_recursive import (
            _lean_compact_key,
            _negation_proof_body_for_statement,
        )
        from ensemble_prover.utils import strip_lean_comments

        statement_text = str(statement or "").strip()
        statement_key = _lean_compact_key(statement_text)
        if not statement_text or not statement_key:
            return ""
        return _negation_proof_body_for_statement(
            strip_lean_comments(str(declaration or "")).strip(),
            statement_text,
            statement_key,
        )
    except Exception:
        return ""


def counterexample_negation_proof_from_declaration(
    declaration: str,
    statement: str,
) -> str:
    """Lift one checked counterexample declaration into ``¬statement``.

    Direct negations use advisory spelling matches so ordinary grouping and
    packed syntax can reach the certifier. Counterexample synthesis uses the
    conservative relation matcher. The declaration itself is embedded as
    a local ``have`` and the original universal claim is introduced before
    ``aesop`` performs only the implication/conjunction/quantifier plumbing.
    This synthesized proof still has to pass fresh Lean replay and the axiom
    audit, so parsing can never mint authority by itself.
    """

    try:
        from ensemble_prover.mini_recursive import (
            _checked_evidence_code_has_ambient_context,
            _checked_evidence_code_has_proof_placeholder,
            _checked_evidence_target_refutes_statement,
            _contract_alpha_matches,
            _flatten_conjunction_formulas,
            _iter_checked_lean_target_headers,
            _lean_compact_key,
            _lean_counterexample_target_refutes_statement,
            _relations_are_equivalent,
            _split_top_level_conjunctions,
            _split_top_level_disjunctions,
            _statement_premises_and_conclusion,
            _strip_leading_exists_binder_analysis,
            _top_level_body_separator_index,
        )
        from ensemble_prover.utils import strip_lean_comments

        statement_text = str(statement or "").strip()
        cleaned = strip_lean_comments(str(declaration or "")).strip()
        if (
            not statement_text
            or not cleaned
            or _checked_evidence_code_has_ambient_context(cleaned)
            or _checked_evidence_code_has_proof_placeholder(cleaned)
        ):
            return ""
        direct = _direct_negation_proof_from_declaration(
            cleaned,
            statement_text,
        )
        if direct:
            return direct
        targets = _iter_checked_lean_target_headers(cleaned)
        if len(targets) != 1:
            return ""
        target = str(targets[0] or "").strip()
        if not target or not (
            _checked_evidence_target_refutes_statement(
                target,
                statement_text,
                _lean_compact_key(statement_text),
            )
            or _lean_counterexample_target_refutes_statement(
                target,
                statement_text,
                allow_inferred_relation_binders=True,
            )
        ):
            return ""
        separator = _top_level_body_separator_index(cleaned)
        if separator >= len(cleaned) or not cleaned.startswith(":=", separator):
            return ""
        body = cleaned[separator + 2 :].strip()
        if not body or not body.lstrip().startswith("by"):
            return ""
        (
            target_body,
            target_bound_names,
            target_premises,
            target_proof_binder_names,
        ) = (
            _strip_leading_exists_binder_analysis(target)
        )
        target_components = _flatten_conjunction_formulas(target_body)
        if not target_bound_names or not target_components:
            return ""
        witness_names = tuple(
            f"h_mini_witness_{index}"
            for index in range(len(target_bound_names))
        )
        component_names = tuple(
            f"h_mini_counterexample_fact_{index}"
            for index in range(len(target_components))
        )
        witness_pattern = ", ".join(
            (*witness_names, *component_names)
        )
        statement_premises, _conclusion, statement_bound_names = (
            _statement_premises_and_conclusion(statement_text)
        )
        premise_arguments: list[str] = []
        target_premise_witness_names = tuple(
            witness_names[target_bound_names.index(name)]
            for name in target_proof_binder_names
            if name in target_bound_names
        )
        available_facts = [
            *zip(target_components, component_names),
            *zip(target_premises, target_premise_witness_names),
        ]

        def proof_term_for_formula(formula: str) -> str:
            exact = next(
                (
                    name
                    for fact, name in available_facts
                    if _contract_alpha_matches(
                        fact,
                        formula,
                        left_bound_names=target_bound_names,
                        right_bound_names=statement_bound_names,
                    )
                    or _relations_are_equivalent(
                        fact,
                        formula,
                        left_bound_names=target_bound_names,
                        right_bound_names=statement_bound_names,
                    )
                ),
                "",
            )
            if exact:
                return exact
            conjunction = tuple(_split_top_level_conjunctions(formula))
            if len(conjunction) > 1:
                terms = tuple(proof_term_for_formula(part) for part in conjunction)
                return "⟨" + ", ".join(terms) + "⟩" if all(terms) else ""
            disjunction = tuple(_split_top_level_disjunctions(formula))
            if len(disjunction) > 1:
                for index, part in enumerate(disjunction):
                    term = proof_term_for_formula(part)
                    if not term:
                        continue
                    wrapped = (
                        f"Or.inl ({term})"
                        if index < len(disjunction) - 1
                        else term
                    )
                    for _ in range(index):
                        wrapped = f"Or.inr ({wrapped})"
                    return wrapped
            return ""

        for premise in statement_premises:
            target_premise_index = next(
                (
                    index
                    for index, target_premise in enumerate(target_premises)
                    if _contract_alpha_matches(
                        target_premise,
                        premise,
                        left_bound_names=target_bound_names,
                        right_bound_names=statement_bound_names,
                    )
                    or _relations_are_equivalent(
                        target_premise,
                        premise,
                        left_bound_names=target_bound_names,
                        right_bound_names=statement_bound_names,
                    )
                ),
                None,
            )
            if (
                target_premise_index is not None
                and target_premise_index < len(target_premise_witness_names)
            ):
                # This proof-valued forall binder is already one of the
                # explicit `@h_mini_claim` arguments unpacked from Exists.
                continue
            premise_term = proof_term_for_formula(premise)
            if not premise_term:
                return ""
            premise_arguments.append(f"({premise_term})")
        claim_arguments = " ".join((*witness_names, *premise_arguments))
        return (
            "by\n"
            "  intro h_mini_claim\n"
            f"  have h_mini_counterexample : {target} := (\n"
            f"{textwrap.indent(body, '    ')}\n"
            "  )\n"
            f"  rcases h_mini_counterexample with ⟨{witness_pattern}⟩\n"
            f"  have h_mini_claim_conclusion := @h_mini_claim {claim_arguments}\n"
            "  clear h_mini_claim\n"
            "  first | omega | aesop"
        )
    except Exception:
        return ""


def terminalize_exact_proof_state_aliases(
    *,
    parent_session: Any,
    dossier: Any,
    statement: str,
    certificate_hash: str,
    target_environment_hash: str,
    reason: str,
) -> tuple[str, ...]:
    """Suppress every exact child-goal alias backed by one certificate."""

    proof_state = getattr(parent_session, "proof_state", None)
    marker = getattr(proof_state, "mark_child_goal_falsified", None)
    if proof_state is None or not callable(marker):
        return ()
    expected = _exact_statement_text(statement)
    authority_environment_hash = str(target_environment_hash or "").strip()
    if not authority_environment_hash:
        return ()
    graph = getattr(dossier, "proof_graph", None)
    terminalized: list[str] = []
    for node in list(getattr(proof_state, "nodes", {}).values()):
        if (
            str(getattr(node, "kind", "") or "") != "child_goal"
            or _exact_statement_text(getattr(node, "target", "")) != expected
        ):
            continue
        node_environment_hash = str(
            getattr(node, "statement_environment_hash", "") or ""
        ).strip()
        if not node_environment_hash and graph is not None:
            projection = getattr(graph, "nodes", {}).get(
                f"proof_state:{str(getattr(node, 'node_id', '') or '').strip()}"
            )
            projection_metadata = dict(
                getattr(projection, "metadata", {}) or {}
            )
            node_environment_hash = str(
                projection_metadata.get("statement_environment_hash")
                or dict(projection_metadata.get("proof_state_node") or {}).get(
                    "statement_environment_hash"
                )
                or ""
            ).strip()
            if node_environment_hash:
                # Rehydrate the run-local alias only from its own durable
                # projection.  Do not stamp an actually legacy target from the
                # current dossier environment.
                node.statement_environment_hash = node_environment_hash
        if node_environment_hash != authority_environment_hash:
            continue
        if bool(getattr(node, "falsified", False)):
            if str(getattr(node, "falsification_certificate_hash", "") or "") == str(
                certificate_hash or ""
            ):
                terminalized.append(str(getattr(node, "node_id", "") or ""))
            continue
        if marker(
            str(getattr(node, "node_id", "") or ""),
            certificate_hash=certificate_hash,
            dossier=dossier,
            reason=reason,
            phase="authoritative_falsification",
            turn_index=int(getattr(parent_session, "iteration", 0) or 0),
        ):
            terminalized.append(str(getattr(node, "node_id", "") or ""))
    return tuple(item for item in terminalized if item)


async def record_authoritative_negation_artifact(
    *,
    parent_session: Any,
    dossier: Any,
    target_statement: str,
    negation_proofs: Sequence[str] = (),
    negation_declarations: Sequence[str] = (),
    preamble: str,
    helper_blocks: Optional[Sequence[str]] = None,
    feedback_preamble: Optional[str] = None,
    feedback_helper_blocks: Optional[Sequence[str]] = None,
    certification_results: Optional[list[CertificationResult]] = None,
    engine: str,
    reason: str,
    publication_guard: Optional[Callable[[], None]] = None,
) -> Tuple[bool, str, tuple[str, ...]]:
    """Promote an exact negation artifact through the sole authority boundary.

    Target-mismatching declarations remain unusable as positive proofs.  When
    such a declaration instead proves the *exact negation* of the selected
    target, preserve that mathematical artifact by replaying it through the
    falsification certifier.  Only a fresh authoritative certificate mutates
    the dossier, graph, or proof state.
    """

    statement = str(target_statement or "").strip()
    record_report = getattr(dossier, "record_falsification_report", None)
    target_environment_hash = str(
        getattr(dossier, "current_lean_environment_hash", "") or ""
    ).strip()
    acceptance_preamble = str(preamble or "")
    admission_failure = ""
    if dossier is None or not callable(record_report):
        admission_failure = "counterexample admission requires an active proof dossier"
    elif not statement:
        admission_failure = "counterexample admission requires a nonempty target"
    elif not target_environment_hash:
        admission_failure = "counterexample admission requires a bound Lean environment"
    if admission_failure:
        if certification_results is not None:
            certification_results.append(
                CertificationResult(
                    CertificationStatus.DEFINITIVE_REJECTION,
                    reason=admission_failure,
                )
            )
        return False, "", ()
    if text_hash(acceptance_preamble) != target_environment_hash:
        if certification_results is not None:
            certification_results.append(
                CertificationResult(
                    CertificationStatus.RETRYABLE_INFRASTRUCTURE,
                    reason="target Lean environment changed before certification",
                )
            )
        return False, "", ()
    proofs = [str(item or "").strip() for item in negation_proofs if str(item or "").strip()]
    for declaration in negation_declarations:
        body = counterexample_negation_proof_from_declaration(
            declaration,
            statement,
        )
        if body:
            proofs.append(body)
    proofs = list(dict.fromkeys(proofs))
    if not proofs:
        if certification_results is not None:
            certification_results.append(
                CertificationResult(
                    CertificationStatus.DEFINITIVE_REJECTION,
                    reason="no proof of the exact target's negation was supplied",
                )
            )
        return False, "", ()

    helpers = tuple(
        str(item or "").strip()
        for item in (
            helper_blocks
            if helper_blocks is not None
            else dossier.verified_helper_blocks()
            if hasattr(dossier, "verified_helper_blocks")
            else ()
        )
        if str(item or "").strip()
    )
    visible_preamble = (
        None if feedback_preamble is None else str(feedback_preamble or "")
    )
    visible_helpers = tuple(
        str(item or "").strip()
        for item in (
            feedback_helper_blocks
            if feedback_helper_blocks is not None
            else helpers
        )
        if str(item or "").strip()
    )
    visible_replay_required = bool(
        visible_preamble is not None
        and (
            visible_preamble != acceptance_preamble
            or tuple(safe_helper_sources(visible_helpers))
            != tuple(safe_helper_sources(helpers))
        )
    )
    lean = getattr(parent_session, "lean", None)
    admission_started = time.monotonic()
    admission = await _admit_original_refutation_target(
        lean, statement, acceptance_preamble, helpers, _CERTIFY_TIMEOUT_S,
    )
    remaining = _CERTIFY_TIMEOUT_S - (time.monotonic() - admission_started)
    if admission is None and visible_replay_required and remaining > 0:
        assert visible_preamble is not None
        admission = await _admit_original_refutation_target(
            lean, statement, visible_preamble, visible_helpers, remaining,
            filter_authority_helpers=False,
        )
        remaining = _CERTIFY_TIMEOUT_S - (time.monotonic() - admission_started)
    if admission is None and remaining <= 0:
        admission = CertificationResult(
            CertificationStatus.RETRYABLE_INFRASTRUCTURE,
            reason="original target preflight exhausted the certification allowance",
        )
    if admission is not None:
        if certification_results is not None:
            certification_results.append(admission)
        return False, "", ()
    policy = FalsificationPolicy(
        operation_timeout_s=remaining,
        engine_timeout_s=remaining,
    )
    environment_hash = falsification_environment_hash(
        preamble=acceptance_preamble,
        helpers=helpers,
        policy=policy,
        lean=lean,
    )

    def report_conflicted(certificate_hash: str) -> bool:
        receipts = getattr(
            dossier,
            "_mini_falsification_trust_boundary_conflict_certificate_hashes",
            None,
        )
        if not certificate_hash or not isinstance(receipts, set):
            return False
        if certificate_hash not in receipts:
            return False
        setattr(
            dossier,
            "session_failure_reason",
            "falsification_trust_boundary_conflict",
        )
        setattr(dossier, "session_failure_kind", "proof_disproof_conflict")
        return True

    for negation_proof in proofs:
        candidate = CounterexampleCandidate(
            engine=str(engine or "accepted_exact_negation"),
            explanation=str(reason or "accepted exact-negation artifact"),
        )
        if visible_replay_required:
            assert visible_preamble is not None
            visible_ok, visible_retryable, visible_reason = (
                await check_negation_proof_in_feedback_world(
                    lean,
                    statement=statement,
                    proof=negation_proof,
                    preamble=visible_preamble,
                    helpers=visible_helpers,
                    timeout_s=policy.operation_timeout_s,
                )
            )
            if not visible_ok and certification_results is not None:
                certification_results.append(
                    CertificationResult(
                        CertificationStatus.RETRYABLE_INFRASTRUCTURE
                        if visible_retryable
                        else CertificationStatus.DEFINITIVE_REJECTION,
                        reason=visible_reason,
                    )
                )
            if not visible_ok:
                continue
        certification_result = await certify_negation_proof_result(
            lean,
            statement=statement,
            proof=negation_proof,
            candidate=candidate,
            preamble=acceptance_preamble,
            helpers=helpers,
            policy=policy,
            environment_hash=environment_hash,
            include_lean_diagnostics=not visible_replay_required,
        )
        if certification_results is not None:
            certification_results.append(certification_result)
        certificate = certification_result.certificate
        if certificate is None or not certificate.authoritative:
            continue
        if (
            str(getattr(dossier, "current_lean_environment_hash", "") or "").strip()
            != target_environment_hash
            or text_hash(acceptance_preamble) != target_environment_hash
        ):
            if certification_results is not None:
                certification_results.append(
                    CertificationResult(
                        CertificationStatus.RETRYABLE_INFRASTRUCTURE,
                        reason="target Lean environment changed during certification",
                    )
                )
            return False, "", ()
        lifted_root, lifted_root_proof = _active_root_negation_lift(
            dossier=dossier,
            active_statement=statement,
            active_negation_proof=negation_proof,
            preamble=acceptance_preamble,
        )
        root_report: FalsificationReport | None = None
        root_certificate_hash = ""
        if lifted_root and lifted_root_proof:
            root_candidate = CounterexampleCandidate(
                engine="active_root_negation_lift",
                explanation=(
                    "certified active-target negation lifted through the exact "
                    "materialized answer shell"
                ),
            )
            visible_root_ok = True
            if visible_replay_required:
                assert visible_preamble is not None
                (
                    visible_root_ok,
                    visible_root_retryable,
                    visible_root_reason,
                ) = await check_negation_proof_in_feedback_world(
                    lean,
                    statement=lifted_root,
                    proof=lifted_root_proof,
                    preamble=visible_preamble,
                    helpers=visible_helpers,
                    timeout_s=policy.operation_timeout_s,
                )
                if visible_root_retryable:
                    retryable_result = CertificationResult(
                        CertificationStatus.RETRYABLE_INFRASTRUCTURE,
                        reason=visible_root_reason,
                    )
                    if certification_results is not None:
                        certification_results.append(retryable_result)
                    # Validate every deterministic lift before committing the
                    # active certificate. Otherwise a transient root replay
                    # consumes the only durable artifact needed to finish the
                    # exact answer shell.
                    return False, "", ()
            if visible_root_ok:
                root_certification_result = await certify_negation_proof_result(
                    lean,
                    statement=lifted_root,
                    proof=lifted_root_proof,
                    candidate=root_candidate,
                    preamble=acceptance_preamble,
                    helpers=helpers,
                    policy=policy,
                    environment_hash=environment_hash,
                )
                if certification_results is not None:
                    certification_results.append(root_certification_result)
                if root_certification_result.retryable:
                    return False, "", ()
                root_certificate = root_certification_result.certificate
                if root_certificate is not None and root_certificate.authoritative:
                    root_report = FalsificationReport(
                        statement=lifted_root,
                        target_kind=TargetKind.ROOT,
                        findings=(
                            FalsificationFinding(
                                engine="active_root_negation_lift",
                                outcome=FalsificationOutcome.REFUTED,
                                reason="active_root_negation_lift_certified",
                                candidates=(root_candidate,),
                                certificate=root_certificate,
                                checks_run=1,
                            ),
                        ),
                        policy_hash=policy.policy_hash,
                        environment_hash=environment_hash,
                    )
                    root_certificate_hash = str(
                        root_certificate.to_record().get("certificate_hash", "")
                        or ""
                    )
        if (
            str(getattr(dossier, "current_lean_environment_hash", "") or "").strip()
            != target_environment_hash
            or text_hash(acceptance_preamble) != target_environment_hash
        ):
            # Root-lift replay is asynchronous. Rebind the whole transaction
            # only if the exact environment captured before either replay is
            # still current at the synchronous admission boundary.
            if certification_results is not None:
                certification_results.append(
                    CertificationResult(
                        CertificationStatus.RETRYABLE_INFRASTRUCTURE,
                        reason="target Lean environment changed during root lift",
                    )
                )
            return False, "", ()
        report = FalsificationReport(
            statement=statement,
            target_kind=(
                TargetKind.ROOT
                if _exact_statement_text(getattr(dossier, "root_statement", ""))
                == _exact_statement_text(statement)
                else TargetKind.HELPER
            ),
            findings=(
                FalsificationFinding(
                    engine=str(engine or "accepted_exact_negation"),
                    outcome=FalsificationOutcome.REFUTED,
                    reason=str(reason or "accepted_exact_negation"),
                    candidates=(candidate,),
                    certificate=certificate,
                    checks_run=1,
                ),
            ),
            policy_hash=policy.policy_hash,
            environment_hash=environment_hash,
        )
        try:
            certificate_hash = str(
                certificate.to_record().get("certificate_hash", "") or ""
            )
        except Exception:
            certificate_hash = ""
        if publication_guard is not None:
            publication_guard()
        if not record_report(report):
            if report_conflicted(certificate_hash):
                return False, certificate_hash, ()
            if certification_results is not None:
                certification_results.append(
                    CertificationResult(
                        CertificationStatus.DEFINITIVE_REJECTION,
                        reason="verified negation could not be bound to the active target",
                    )
                )
            continue
        terminalized = terminalize_exact_proof_state_aliases(
            parent_session=parent_session,
            dossier=dossier,
            statement=statement,
            certificate_hash=certificate_hash,
            target_environment_hash=target_environment_hash,
            reason=(
                "Lean proved and axiom-audited ¬goal; exact target terminalized"
            ),
        )
        if root_report is not None:
            if record_report(root_report):
                certificate_hash = root_certificate_hash
                terminalized = tuple(dict.fromkeys((
                    *terminalized,
                    *terminalize_exact_proof_state_aliases(
                        parent_session=parent_session,
                        dossier=dossier,
                        statement=lifted_root,
                        certificate_hash=certificate_hash,
                        target_environment_hash=target_environment_hash,
                        reason=(
                            "Lean independently proved and axiom-audited "
                            "the active-target negation lift to the exact root"
                        ),
                    ),
                )))
            elif report_conflicted(root_certificate_hash):
                return False, root_certificate_hash, ()
        reconciler = getattr(parent_session, "_reconcile_repair_policy_narrowing", None)
        if callable(reconciler):
            try:
                reconciler(trigger="authoritative_falsification")
            except Exception:
                pass
        return True, certificate_hash, terminalized
    return False, "", ()


async def record_authoritative_negation_from_transcript(
    *,
    parent_session: Any,
    dossier: Any,
    target_statement: str,
    conv: Any,
    preamble: str,
    helper_blocks: Optional[Sequence[str]] = None,
    feedback_preamble: Optional[str] = None,
    feedback_helper_blocks: Optional[Sequence[str]] = None,
    negation_declarations: Sequence[str] = (),
    certification_results: Optional[list[CertificationResult]] = None,
    engine: str = "accepted_try_lean",
    reason: str = "accepted_exact_negation_artifact",
    publication_guard: Optional[Callable[[], None]] = None,
) -> Tuple[bool, str, tuple[str, ...]]:
    """Certify an exact negation accepted anywhere in a proof-turn transcript.

    Conversation turns and recursive-helper turns share the same ``try_lean``
    protocol, but historically only the recursive-helper failure path inspected
    accepted scratch artifacts.  A final answer can be extracted as a positive
    proof body even when its declaration (and an accepted scratch check in the
    same turn) proves ``¬target``.  Do the evidence extraction before positive
    submission policy can detach that artifact from its exact target.

    Transcript acceptance is only a candidate source.  The returned proof body
    still crosses :func:`record_authoritative_negation_artifact`, which replays
    ``¬target`` and performs the trusted axiom audit.  Thus stale conversation
    content, prose, rejected checks, and checks of a different proposition
    cannot invalidate graph work.
    """

    statement = str(target_statement or "").strip()
    if not statement or conv is None:
        return False, "", ()
    try:
        # Keep the runtime dependency one-way during module initialization.
        from ensemble_prover.mini_recursive import (
            _recursive_claim_negation_candidates_with_context,
        )

        transcript_candidates = _recursive_claim_negation_candidates_with_context(
            conv, statement,
        )
    except Exception:
        return False, "", ()
    declarations = tuple(
        str(item or "").strip()
        for item in negation_declarations
        if str(item or "").strip()
    )
    if not transcript_candidates and not declarations:
        return False, "", ()
    base_helpers = tuple(helper_blocks or ())
    visible_preamble = (
        None if feedback_preamble is None else str(feedback_preamble or "")
    )
    feedback_base_helpers = tuple(
        feedback_helper_blocks
        if feedback_helper_blocks is not None
        else base_helpers
    )
    if visible_preamble is None:
        visible_preamble, feedback_base_helpers = (
            answer_safe_negation_feedback_context(
                conv,
                acceptance_preamble=str(preamble or ""),
                helpers=base_helpers,
            )
        )
    for proof, local_dependencies in transcript_candidates:
        result = await record_authoritative_negation_artifact(
            parent_session=parent_session,
            dossier=dossier,
            target_statement=statement,
            negation_proofs=(proof,),
            preamble=str(preamble or ""),
            helper_blocks=tuple([*base_helpers, *local_dependencies]),
            feedback_preamble=visible_preamble,
            feedback_helper_blocks=tuple(
                [*feedback_base_helpers, *local_dependencies]
            ),
            certification_results=certification_results,
            engine=str(engine or "accepted_try_lean"),
            reason=str(reason or "accepted_exact_negation_artifact"),
            publication_guard=publication_guard,
        )
        if result[0] or result[1]:
            return result
    if declarations:
        return await record_authoritative_negation_artifact(
            parent_session=parent_session,
            dossier=dossier,
            target_statement=statement,
            negation_declarations=declarations,
            preamble=str(preamble or ""),
            helper_blocks=base_helpers,
            feedback_preamble=visible_preamble,
            feedback_helper_blocks=feedback_base_helpers,
            certification_results=certification_results,
            engine=str(engine or "accepted_try_lean"),
            reason=str(reason or "accepted_exact_negation_artifact"),
            publication_guard=publication_guard,
        )
    return False, "", ()


def _statement_is_interpolation_safe(statement: str) -> bool:
    """Reject statements that could break out of the ``¬ ({statement})`` wrapper.

    The certifier splices the goal into ``theorem … : ¬ ({statement}) := …`` by
    raw string interpolation. A false positive requires the goal to be provable
    under the scheduler's ``theorem … : {statement} := …`` wrapping yet flipped
    under the certifier's negation wrapping — any breakout that fools one wrapper
    also breaks the other, so this is defense-in-depth, not the primary gate. We
    still refuse comments, unterminated literals, and unbalanced brackets.
    Local ``let``/``have`` assignments are ordinary term syntax: ``:=`` cannot
    close the surrounding parenthesis, so rejecting it blocks valid targets.
    Apostrophe-bearing targets bypass this context-free check: their original
    proposition must first pass Lean's environment-aware parser.
    """

    text = str(statement or "")
    pairs = {")": "(", "]": "[", "}": "{"}
    openers = set(pairs.values())
    stack: list[str] = []
    index = 0
    while index < len(text):
        # Comments can obscure the generated wrapper. Identical tokens inside
        # literals are inert and skipped by the Lean-aware lexical scanner.
        if (
            text.startswith("--", index)
            or text.startswith("/-", index)
            or text.startswith("-/", index)
        ):
            return False
        skip_to = _lean_lexical_skip_end(text, index)
        if skip_to is not None:
            atom = text[index:skip_to]
            if text[index] == '"':
                # An escaped final quote is not a closing delimiter. The
                # scanner returns EOF for both closed and unfinished atoms.
                trailing_slashes = len(atom[:-1]) - len(atom[:-1].rstrip("\\"))
                if len(atom) < 2 or not atom.endswith('"') or trailing_slashes % 2:
                    return False
            if text[index] == "'" and not atom.endswith("'"):
                return False
            if text.startswith("«", index) and not atom.endswith("»"):
                return False
            if text[index] == "r":
                hash_index = index + 1
                while hash_index < len(text) and text[hash_index] == "#":
                    hash_index += 1
                if hash_index < len(text) and text[hash_index] == '"':
                    terminator = '"' + text[index + 1 : hash_index]
                    opener_length = hash_index - index + 1
                    if (
                        len(atom) < opener_length + len(terminator)
                        or not atom.endswith(terminator)
                    ):
                        return False
            index = skip_to
            continue
        ch = text[index]
        if ch == "'":
            previous = text[index - 1] if index else ""
            if not previous or not (previous.isalnum() or previous in "_'»"):
                return False  # An unfinished character literal was not skipped.
        if ch in openers:
            stack.append(ch)
        elif ch in pairs:
            if not stack or stack[-1] != pairs[ch]:
                return False
            stack.pop()
        index += 1
    return not stack


async def maybe_falsify_child_goal_from_child_transcript(
    *,
    parent_session: Any,
    dossier: Any,
    node_id: str,
    target_statement: str,
    child_conv: Any,
    preamble: str,
    publication_guard: Optional[Callable[[], None]] = None,
) -> Tuple[bool, str]:
    """Best-effort: durably mark ``node_id`` falsified if the child transcript
    holds an authoritatively-certifiable ``¬target_statement`` proof.

    Returns ``(falsified, certificate_hash)``. Never raises — any internal
    failure returns ``(False, "")``. The caller invokes this only after a FAILED
    prove pass, so a positive proof of the same goal can never race it.
    """

    proof_state = getattr(parent_session, "proof_state", None)
    node_id = str(node_id or "").strip()
    statement = str(target_statement or "").strip()
    node = (
        getattr(proof_state, "nodes", {}).get(node_id)
        if proof_state is not None and node_id
        else None
    )
    if (
        node is None
        or getattr(node, "kind", "") != "child_goal"
        or getattr(node, "falsified", False)
        or dossier is None
        or not statement
        # The central admission checks the original target with Lean before
        # wrapping it; a Python lexer must not preempt that authority.
    ):
        return False, ""

    marker = getattr(proof_state, "mark_child_goal_falsified", None)
    record_report = getattr(dossier, "record_falsification_report", None)
    if not callable(marker) or not callable(record_report):
        return False, ""

    try:
        base_helpers = tuple(
            dossier.verified_helper_blocks()
            if callable(getattr(dossier, "verified_helper_blocks", None))
            else ()
        )
        feedback_preamble, feedback_helpers = (
            answer_safe_negation_feedback_context(
                child_conv,
                acceptance_preamble=str(preamble or ""),
                helpers=base_helpers,
            )
        )

        authoritative, certificate_hash, terminalized = (
            await record_authoritative_negation_from_transcript(
                parent_session=parent_session,
                dossier=dossier,
                target_statement=statement,
                conv=child_conv,
                preamble=str(preamble or ""),
                helper_blocks=base_helpers,
                feedback_preamble=feedback_preamble,
                feedback_helper_blocks=feedback_helpers,
                engine="child_try_lean",
                reason="child_goal_lean_falsified",
                publication_guard=publication_guard,
            )
        )
        return bool(authoritative and node_id in terminalized), certificate_hash
    except Exception:
        # Best-effort scheduler optimisation on an already-failed prove path;
        # never let it break that path.
        return False, ""

    return False, ""
