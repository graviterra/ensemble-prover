"""Typed, JSON-safe records for Mini's falsification subsystem."""

from __future__ import annotations

import hashlib
import json
import math
import re
import time
from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any, Mapping

from ensemble_prover.falsification_cursor_identity import (
    counterexample_candidate_record_is_valid,
)
from ensemble_prover.utils import strip_lean_comments_and_string_literals


class TargetKind(str, Enum):
    ROOT = "root"
    HELPER = "helper"
    LOCAL_SEQUENT = "local_sequent"


class FalsificationOutcome(str, Enum):
    REFUTED = "refuted"
    VERIFIED_TRUE = "verified_true"
    INCONCLUSIVE = "inconclusive"
    UNSUPPORTED = "unsupported"
    TRANSIENT_FAILURE = "transient_failure"


class TrustLevel(str, Enum):
    HEURISTIC = "heuristic"
    LEAN_INSTANCE_CHECKED = "lean_instance_checked"
    LEAN_NEGATION_CHECKED = "lean_negation_checked"
    LEAN_AXIOM_AUDITED = "lean_axiom_audited"


def content_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class CounterexampleCandidate:
    engine: str
    witness_terms: tuple[str, ...] = ()
    concrete_statement: str = ""
    explanation: str = ""
    complete_domain: bool = False
    metadata: Mapping[str, Any] = field(default_factory=dict)

    def to_record(self) -> dict[str, Any]:
        record = asdict(self)
        record["metadata"] = dict(self.metadata)
        record["candidate_hash"] = content_hash(record)
        return record


@dataclass(frozen=True)
class LeanCounterexampleCertificate:
    statement: str
    negated_statement: str
    proof_code: str
    witness_terms: tuple[str, ...]
    concrete_statement: str
    lean_output: str = ""
    axioms: tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.HEURISTIC
    environment_hash: str = ""

    @property
    def authoritative(self) -> bool:
        return self.trust is TrustLevel.LEAN_AXIOM_AUDITED

    def to_record(self) -> dict[str, Any]:
        record = asdict(self)
        record["trust"] = self.trust.value
        record["authoritative"] = self.authoritative
        record["certificate_hash"] = content_hash(record)
        return record


@dataclass(frozen=True)
class FalsificationFinding:
    engine: str
    outcome: FalsificationOutcome
    reason: str = ""
    candidates: tuple[CounterexampleCandidate, ...] = ()
    certificate: LeanCounterexampleCertificate | None = None
    checks_run: int = 0
    elapsed_s: float = 0.0
    cursor: Mapping[str, Any] = field(default_factory=dict)
    error_kind: str = ""

    @property
    def authoritative_refutation(self) -> bool:
        return bool(
            self.outcome is FalsificationOutcome.REFUTED
            and self.certificate is not None
            and self.certificate.authoritative
        )

    @property
    def coverage_pending(self) -> bool:
        """Whether a finite, resumable search domain still has unchecked items.

        Open-ended property generation deliberately does not count as pending:
        it has no finite completion point and must not turn one falsification
        request into an unbounded loop.  Finite engines publish both
        ``next_index`` and ``domain_size``, which gives orchestration an
        engine-independent, progress-sensitive continuation contract.
        """

        if self.outcome is not FalsificationOutcome.INCONCLUSIVE:
            return False
        cursor = dict(self.cursor or {})
        next_index = cursor.get("next_index")
        domain_size = cursor.get("domain_size")
        if (
            not isinstance(next_index, int)
            or isinstance(next_index, bool)
            or not isinstance(domain_size, int)
            or isinstance(domain_size, bool)
        ):
            return False
        if (
            cursor.get("exhausted") is True
            or cursor.get("phase") == "exhausted"
        ) and next_index == domain_size:
            return False
        return 0 <= next_index < domain_size

    def to_record(self) -> dict[str, Any]:
        return {
            "engine": self.engine,
            "outcome": self.outcome.value,
            "reason": self.reason,
            "candidates": [candidate.to_record() for candidate in self.candidates],
            "certificate": self.certificate.to_record() if self.certificate else None,
            "checks_run": int(self.checks_run),
            "elapsed_s": float(self.elapsed_s),
            "cursor": dict(self.cursor),
            "error_kind": self.error_kind,
        }


@dataclass(frozen=True)
class FalsificationReport:
    statement: str
    target_kind: TargetKind
    findings: tuple[FalsificationFinding, ...]
    started_at: float = field(default_factory=time.time)
    policy_hash: str = ""
    environment_hash: str = ""

    @property
    def authoritative_refutation(self) -> LeanCounterexampleCertificate | None:
        for finding in self.findings:
            if finding.authoritative_refutation:
                return finding.certificate
        return None

    @property
    def outcome(self) -> FalsificationOutcome:
        """Return the authority-level aggregate used for mathematical control."""

        if self.authoritative_refutation is not None:
            return FalsificationOutcome.REFUTED
        outcomes = {finding.outcome for finding in self.findings}
        # Authority/control remains retry-safe: a partial infrastructure
        # failure is not erased by unrelated bounded evidence.  Callers that
        # need the mathematical/search view use ``evidence_outcome`` below,
        # which deliberately preserves that independent evidence.
        if FalsificationOutcome.TRANSIENT_FAILURE in outcomes:
            return FalsificationOutcome.TRANSIENT_FAILURE
        if (
            FalsificationOutcome.INCONCLUSIVE in outcomes
            or FalsificationOutcome.REFUTED in outcomes
        ):
            return FalsificationOutcome.INCONCLUSIVE
        if FalsificationOutcome.VERIFIED_TRUE in outcomes:
            return FalsificationOutcome.VERIFIED_TRUE
        return FalsificationOutcome.UNSUPPORTED

    @property
    def evidence_outcome(self) -> FalsificationOutcome:
        """Return the strongest search evidence, independent of promotion."""

        outcomes = {finding.outcome for finding in self.findings}
        if FalsificationOutcome.REFUTED in outcomes:
            return FalsificationOutcome.REFUTED
        if FalsificationOutcome.INCONCLUSIVE in outcomes:
            return FalsificationOutcome.INCONCLUSIVE
        if FalsificationOutcome.VERIFIED_TRUE in outcomes:
            return FalsificationOutcome.VERIFIED_TRUE
        if FalsificationOutcome.TRANSIENT_FAILURE in outcomes:
            return FalsificationOutcome.TRANSIENT_FAILURE
        return FalsificationOutcome.UNSUPPORTED

    @property
    def unpromoted_refutation_count(self) -> int:
        return sum(
            1
            for finding in self.findings
            if finding.outcome is FalsificationOutcome.REFUTED
            and not finding.authoritative_refutation
        )

    @property
    def has_transient_failures(self) -> bool:
        return any(
            finding.outcome is FalsificationOutcome.TRANSIENT_FAILURE
            for finding in self.findings
        )

    @property
    def has_pending_coverage(self) -> bool:
        return any(finding.coverage_pending for finding in self.findings)

    def to_record(self) -> dict[str, Any]:
        record = {
            "statement": self.statement,
            "target_kind": self.target_kind.value,
            # ``outcome`` remains the backward-compatible authority outcome.
            "outcome": self.outcome.value,
            "authority_outcome": self.outcome.value,
            "evidence_outcome": self.evidence_outcome.value,
            "unpromoted_refutation_count": self.unpromoted_refutation_count,
            "has_transient_failures": self.has_transient_failures,
            "started_at": self.started_at,
            "policy_hash": self.policy_hash,
            "environment_hash": self.environment_hash,
            "findings": [finding.to_record() for finding in self.findings],
        }
        record["report_hash"] = content_hash(record)
        return record


def finding_from_record(data: Mapping[str, Any]) -> FalsificationFinding:
    raw_certificate = data.get("certificate")
    certificate = None
    if isinstance(raw_certificate, Mapping):
        certificate = LeanCounterexampleCertificate(
            statement=str(raw_certificate.get("statement") or ""),
            negated_statement=str(raw_certificate.get("negated_statement") or ""),
            proof_code=str(raw_certificate.get("proof_code") or ""),
            witness_terms=tuple(raw_certificate.get("witness_terms") or ()),
            concrete_statement=str(raw_certificate.get("concrete_statement") or ""),
            lean_output=str(raw_certificate.get("lean_output") or ""),
            axioms=tuple(raw_certificate.get("axioms") or ()),
            trust=TrustLevel(
                str(raw_certificate.get("trust") or TrustLevel.HEURISTIC.value)
            ),
            environment_hash=str(raw_certificate.get("environment_hash") or ""),
        )
    candidates = tuple(
        candidate_from_record(item)
        for item in data.get("candidates") or ()
        if isinstance(item, Mapping)
    )
    return FalsificationFinding(
        engine=str(data.get("engine") or ""),
        outcome=FalsificationOutcome(str(data.get("outcome") or "inconclusive")),
        reason=str(data.get("reason") or ""),
        candidates=candidates,
        certificate=certificate,
        checks_run=int(data.get("checks_run") or 0),
        elapsed_s=float(data.get("elapsed_s") or 0.0),
        cursor=dict(data.get("cursor") or {}),
        error_kind=str(data.get("error_kind") or ""),
    )


def candidate_from_record(data: Mapping[str, Any]) -> CounterexampleCandidate:
    """Rehydrate one candidate after its containing envelope was validated."""

    return CounterexampleCandidate(
        engine=str(data.get("engine") or ""),
        witness_terms=tuple(data.get("witness_terms") or ()),
        concrete_statement=str(data.get("concrete_statement") or ""),
        explanation=str(data.get("explanation") or ""),
        complete_domain=bool(data.get("complete_domain", False)),
        metadata=dict(data.get("metadata") or {}),
    )


def certificate_record_is_valid(
    data: Any, *, require_authoritative: bool = False
) -> bool:
    if not isinstance(data, Mapping):
        return False
    record = dict(data)
    claimed_hash = str(record.pop("certificate_hash", "") or "")
    statement_value = record.get("statement")
    negated_value = record.get("negated_statement")
    proof_value = record.get("proof_code")
    witness_terms = record.get("witness_terms")
    concrete_statement = record.get("concrete_statement")
    lean_output = record.get("lean_output")
    environment_hash_value = record.get("environment_hash")
    statement = str(statement_value or "").strip()
    proof = str(proof_value or "")
    executable_proof = strip_lean_comments_and_string_literals(proof)
    negated = str(negated_value or "").strip()
    environment_hash = str(environment_hash_value or "").strip()
    axioms = record.get("axioms")
    if not (
        isinstance(statement_value, str)
        and isinstance(negated_value, str)
        and isinstance(proof_value, str)
        and isinstance(witness_terms, (list, tuple))
        and all(isinstance(item, str) for item in witness_terms)
        and isinstance(concrete_statement, str)
        and isinstance(lean_output, str)
        and isinstance(environment_hash_value, str)
        and isinstance(axioms, (list, tuple))
        and all(isinstance(item, str) for item in axioms)
        and isinstance(record.get("trust"), str)
        and (
            "authoritative" not in record
            or isinstance(record.get("authoritative"), bool)
        )
    ):
        return False
    if not set(str(item) for item in axioms).issubset(
        {"propext", "Classical.choice", "Quot.sound"}
    ):
        return False
    if re.search(
        r"(?<![A-Za-z0-9_'])(?:sorry|admit|native_decide|axiom|constant|unsafe|run_tac)(?![A-Za-z0-9_'])",
        executable_proof,
    ):
        return False
    if re.search(
        r"(?m)^\s*(?:import|theorem|lemma|def|abbrev|instance|namespace|"
        r"section|end|set_option|#\w+)\b",
        executable_proof,
    ):
        return False
    trust = str(record.get("trust") or "")
    authoritative = record.get("authoritative") is True
    return bool(
        re.fullmatch(r"[0-9a-f]{64}", claimed_hash)
        and trust
        in {
            TrustLevel.LEAN_NEGATION_CHECKED.value,
            TrustLevel.LEAN_AXIOM_AUDITED.value,
        }
        and authoritative == (trust == TrustLevel.LEAN_AXIOM_AUDITED.value)
        and (not require_authoritative or authoritative)
        and statement
        and negated == f"¬ ({statement})"
        and proof.lstrip().startswith("by")
        and re.fullmatch(r"[0-9a-f]{64}", environment_hash)
        and content_hash(record) == claimed_hash
    )


def authoritative_certificate_record_is_valid(data: Any) -> bool:
    return certificate_record_is_valid(data, require_authoritative=True)


def falsification_report_record_is_valid(data: Any) -> bool:
    """Validate the content-addressed envelope used by the durable ledger."""

    if not isinstance(data, Mapping):
        return False
    record = dict(data)
    claimed_hash = str(record.pop("report_hash", "") or "")
    statement = str(record.get("statement") or "").strip()
    environment_hash = str(record.get("environment_hash") or "").strip()
    started_at = record.get("started_at")
    if not (
        re.fullmatch(r"[0-9a-f]{64}", claimed_hash)
        and statement
        and isinstance(started_at, (int, float))
        and not isinstance(started_at, bool)
        and math.isfinite(float(started_at))
        and float(started_at) >= 0.0
        and str(record.get("target_kind") or "") in {item.value for item in TargetKind}
        and str(record.get("outcome") or "")
        in {item.value for item in FalsificationOutcome}
        and isinstance(record.get("findings"), list)
        and re.fullmatch(r"[0-9a-f]{64}", environment_hash)
        and content_hash(record) == claimed_hash
    ):
        return False
    finding_outcomes: set[str] = set()
    has_authoritative_refutation = False
    unpromoted_refutation_count = 0
    for finding in record["findings"]:
        if not isinstance(finding, Mapping):
            return False
        candidates = finding.get("candidates")
        checks_run = finding.get("checks_run")
        elapsed_s = finding.get("elapsed_s")
        if not (
            isinstance(finding.get("engine"), str)
            and bool(str(finding.get("engine") or "").strip())
            and isinstance(finding.get("reason"), str)
            and isinstance(candidates, (list, tuple))
            and isinstance(checks_run, int)
            and not isinstance(checks_run, bool)
            and checks_run >= 0
            and isinstance(elapsed_s, (int, float))
            and not isinstance(elapsed_s, bool)
            and math.isfinite(float(elapsed_s))
            and float(elapsed_s) >= 0.0
            and isinstance(finding.get("cursor"), Mapping)
            and isinstance(finding.get("error_kind"), str)
        ):
            return False
        finding_outcome = str(finding.get("outcome") or "")
        if finding_outcome not in {item.value for item in FalsificationOutcome}:
            return False
        finding_outcomes.add(finding_outcome)
        for candidate in candidates:
            if not counterexample_candidate_record_is_valid(candidate):
                return False
        certificate = finding.get("certificate")
        if certificate is not None:
            if not (
                finding_outcome == FalsificationOutcome.REFUTED.value
                and certificate_record_is_valid(certificate)
                and str(certificate.get("statement") or "").strip() == statement
                and str(certificate.get("environment_hash") or "").strip()
                == environment_hash
            ):
                return False
            if certificate.get("authoritative") is True:
                has_authoritative_refutation = True
        if finding_outcome == FalsificationOutcome.REFUTED.value and not (
            isinstance(certificate, Mapping)
            and certificate.get("authoritative") is True
        ):
            unpromoted_refutation_count += 1
    expected_outcome = FalsificationOutcome.UNSUPPORTED.value
    if has_authoritative_refutation:
        expected_outcome = FalsificationOutcome.REFUTED.value
    elif FalsificationOutcome.TRANSIENT_FAILURE.value in finding_outcomes:
        expected_outcome = FalsificationOutcome.TRANSIENT_FAILURE.value
    elif finding_outcomes.intersection(
        {FalsificationOutcome.INCONCLUSIVE.value, FalsificationOutcome.REFUTED.value}
    ):
        expected_outcome = FalsificationOutcome.INCONCLUSIVE.value
    elif FalsificationOutcome.VERIFIED_TRUE.value in finding_outcomes:
        expected_outcome = FalsificationOutcome.VERIFIED_TRUE.value
    if str(record.get("outcome") or "") != expected_outcome:
        return False
    authority_outcome = record.get("authority_outcome")
    if authority_outcome is not None and str(authority_outcome) != expected_outcome:
        return False
    expected_evidence_outcome = FalsificationOutcome.UNSUPPORTED.value
    if FalsificationOutcome.REFUTED.value in finding_outcomes:
        expected_evidence_outcome = FalsificationOutcome.REFUTED.value
    elif FalsificationOutcome.INCONCLUSIVE.value in finding_outcomes:
        expected_evidence_outcome = FalsificationOutcome.INCONCLUSIVE.value
    elif FalsificationOutcome.VERIFIED_TRUE.value in finding_outcomes:
        expected_evidence_outcome = FalsificationOutcome.VERIFIED_TRUE.value
    elif FalsificationOutcome.TRANSIENT_FAILURE.value in finding_outcomes:
        expected_evidence_outcome = FalsificationOutcome.TRANSIENT_FAILURE.value
    evidence_outcome = record.get("evidence_outcome")
    accepted_evidence_outcomes = {expected_evidence_outcome}
    if FalsificationOutcome.TRANSIENT_FAILURE.value in finding_outcomes:
        # Schema-10 reports ranked a transient above independent inconclusive
        # or finite-domain evidence.  Their content hashes remain valid and
        # must survive checkpoint replay; newly emitted reports use the more
        # informative evidence ordering above.
        accepted_evidence_outcomes.add(FalsificationOutcome.TRANSIENT_FAILURE.value)
    if (
        evidence_outcome is not None
        and str(evidence_outcome) not in accepted_evidence_outcomes
    ):
        return False
    declared_unpromoted_count = record.get("unpromoted_refutation_count")
    if declared_unpromoted_count is not None and (
        not isinstance(declared_unpromoted_count, int)
        or isinstance(declared_unpromoted_count, bool)
        or declared_unpromoted_count != unpromoted_refutation_count
    ):
        return False
    declared_transient = record.get("has_transient_failures")
    if declared_transient is not None and declared_transient is not (
        FalsificationOutcome.TRANSIENT_FAILURE.value in finding_outcomes
    ):
        return False
    return True
