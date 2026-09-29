"""Bounded, complementary research assignments without proof authority.

The scheduler only proposes work and records packets. It never runs submitted
commands, calls a model, writes a worker's output, or promotes a parent because
one of its helpers is supported.
"""

from __future__ import annotations

import base64
import math
from contextlib import nullcontext
from typing import Any, Protocol

from .model import (
    assignment_context_record,
    assignment_output_path,
    identifier,
    positive_int,
    text,
)


WORK_KINDS = (
    "investigate",
    "counterexample",
    "quantitative_bound",
    "independent_review",
)
PERMITTED_OUTCOMES = ("positive_argument", "counterexample", "precise_gap")
REQUIRED_CHECKS = (
    "Check the exact statement, quantifier order, and every hypothesis.",
    "Check that reductions preserve the ambient objects, domain, and structures required by the claim.",
    "State definitions, conventions, and normalizations used by the argument.",
    "Account for boundary cases, exceptional cases, and degeneracies.",
    "Track every relevant parameter, constant, and loss across the argument.",
    "Check that the resulting bound or implication suffices for the parent obligation in its required regime.",
    "Distinguish exact from approximate claims and finite experiments from general proofs.",
    "Identify which hypotheses are used; justify any stronger result and expose all remaining unproved premises.",
    "For a counterexample, show that it satisfies the hypotheses and violates the conclusion.",
    "For published inputs, check primary sources and record exact locations.",
)


class ClaimStore(Protocol):
    def get_claim(self, claim_id: str) -> dict[str, Any]: ...
    def assessment(self, claim_id: str) -> dict[str, Any]: ...
    def history(self, claim_id: str) -> dict[str, Any]: ...
    def read_artifact(self, artifact_id: str) -> bytes: ...
    def save_assignment(self, packet: dict[str, Any]) -> dict[str, Any]: ...


class ResearchScheduler:
    """Explain research priorities using explicit, currently needed obligations."""

    def __init__(self, store: ClaimStore) -> None:
        self.store = store

    def _context(self, target_id: str) -> list[dict[str, Any]]:
        # The SQLite store supplies a shared snapshot for the entire graph.
        # In-memory test adapters already expose an immutable local view.
        snapshot = getattr(self.store, "read_snapshot", None)
        with snapshot() if snapshot is not None else nullcontext():
            return self._read_context(target_id)

    def _read_context(self, target_id: str) -> list[dict[str, Any]]:
        identifier(target_id, "target_id")
        pending = [target_id]
        context: dict[str, dict[str, Any]] = {}
        while pending:
            claim_id = pending.pop()
            if claim_id in context:
                continue
            claim = self.store.get_claim(claim_id)
            assessment = self.store.assessment(claim_id)
            if assessment["revision"] != claim["revision"]:
                raise ValueError("claim changed while reading research context; retry")
            context[claim_id] = {"claim": claim, "assessment": assessment}
            pending.extend(
                item["supplier_id"] for item in claim["spec"]["dependencies"]
            )
        return [
            context[target_id],
            *(context[key] for key in sorted(context) if key != target_id),
        ]

    @staticmethod
    def _contributions(node: dict[str, Any]) -> dict[str, dict[str, Any]]:
        return {
            item["obligation_id"]: item for item in node["assessment"]["contributions"]
        }

    @staticmethod
    def _decision(contribution: dict[str, Any] | None) -> str:
        if contribution and contribution.get("active"):
            return contribution["decision"]
        return "unresolved"

    @staticmethod
    def _requires_revision(node: dict[str, Any]) -> bool:
        assessment = node["assessment"]
        return bool(
            assessment.get("requires_target_revision")
            or assessment["mathematical_status"] == "refuted"
        )

    def _needed_context(self, context: list[dict[str, Any]]) -> list[dict[str, Any]]:
        """Do not reward or schedule sublemmas underneath discarded routes."""
        if self._requires_revision(context[0]):
            return []
        by_id = {node["claim"]["claim_id"]: node for node in context}
        pending = [context[0]["claim"]["claim_id"]]
        needed: set[str] = set()
        while pending:
            claim_id = pending.pop()
            if claim_id in needed:
                continue
            needed.add(claim_id)
            node = by_id[claim_id]
            contributions = self._contributions(node)
            for obligation in node["claim"]["spec"]["dependencies"]:
                decision = self._decision(
                    contributions.get(obligation["obligation_id"])
                )
                supplier = by_id[obligation["supplier_id"]]
                if decision not in (
                    "irrelevant",
                    "eliminates_route",
                ) and not self._requires_revision(supplier):
                    pending.append(obligation["supplier_id"])
        return [node for node in context if node["claim"]["claim_id"] in needed]

    def _history_context(
        self,
        context: list[dict[str, Any]],
    ) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
        """Recover former routes, including suppliers removed by a revision."""
        claims = {node["claim"]["claim_id"]: node["claim"] for node in context}
        pending = list(claims)
        histories: dict[str, dict[str, Any]] = {}
        while pending:
            claim_id = pending.pop()
            if claim_id in histories:
                continue
            if claim_id not in claims:
                claims[claim_id] = self.store.get_claim(claim_id)
            history = self.store.history(claim_id)
            # Prior packets recursively contain prior histories. Preserve their
            # assignment metadata and outcomes, but include the mathematical
            # records themselves only once in this packet's history context.
            histories[claim_id] = {
                **history,
                "assignments": [
                    assignment_context_record(assignment)
                    for assignment in history.get("assignments", [])
                ],
            }
            specs = [
                claims[claim_id]["spec"],
                *(item["spec"] for item in history["revisions"]),
            ]
            for spec in specs:
                pending.extend(spec.get("supersedes", []))
                pending.extend(item["supplier_id"] for item in spec["dependencies"])
        revisions = [
            {"claim_id": claim_id, "revision": claims[claim_id]["revision"]}
            for claim_id in sorted(claims)
        ]
        return histories, revisions

    def _artifacts(
        self, histories: dict[str, dict[str, Any]]
    ) -> dict[str, dict[str, str]]:
        """Include complete derivations, not just otherwise opaque blob IDs."""
        artifact_ids = {
            artifact_id
            for history in histories.values()
            for evidence in history["evidence"]
            for artifact_id in evidence.get("artifact_ids", [])
        }
        artifacts = {}
        for artifact_id in sorted(artifact_ids):
            content = self.store.read_artifact(artifact_id)
            try:
                artifacts[artifact_id] = {
                    "encoding": "utf-8",
                    "content": content.decode("utf-8"),
                }
            except UnicodeDecodeError:
                artifacts[artifact_id] = {
                    "encoding": "base64",
                    "content": base64.b64encode(content).decode("ascii"),
                }
        return artifacts

    def frontier(self, target_id: str) -> list[dict[str, Any]]:
        """Rank missing implications, route attacks, and consequential bounds.

        Scores are transparent priorities, not mathematical probabilities. A
        supported claim without a reviewed contribution is still an open edge.
        Multiple entries for one edge are complementary investigation options.
        """
        context = self._context(target_id)
        target = context[0]
        if self._requires_revision(target):
            return [
                {
                    "target_id": target_id,
                    "parent_claim_id": None,
                    "parent_revision": None,
                    "claim_id": target_id,
                    "claim_revision": target["claim"]["revision"],
                    "obligation_id": None,
                    "obligation": None,
                    "subject": target,
                    "contribution": None,
                    "priority": 10,
                    "work_kind": "independent_review",
                    "contribution_goal": "review_refutation",
                    "reason": "The target has a reviewed counterexample. Dependency-only revisions do not resolve earlier counterexamples. Review the refutation and explicitly revise or replace the target before further proof work.",
                }
            ]
        by_id = {item["claim"]["claim_id"]: item for item in context}
        frontier: list[dict[str, Any]] = []
        for node in self._needed_context(context):
            parent = node["claim"]
            contributions = self._contributions(node)
            for obligation in parent["spec"]["dependencies"]:
                contribution = contributions.get(obligation["obligation_id"])
                decision = self._decision(contribution)
                supplier = by_id[obligation["supplier_id"]]
                status = supplier["assessment"]["mathematical_status"]
                base = {
                    "target_id": target_id,
                    "parent_claim_id": parent["claim_id"],
                    "parent_revision": parent["revision"],
                    "claim_id": obligation["supplier_id"],
                    "claim_revision": supplier["claim"]["revision"],
                    "obligation_id": obligation["obligation_id"],
                    "obligation": obligation,
                    "subject": supplier,
                    "contribution": contribution,
                }
                if self._requires_revision(supplier):
                    frontier.append(
                        {
                            **base,
                            "priority": 20,
                            "work_kind": "independent_review",
                            "contribution_goal": "review_refutation",
                            "reason": "Review this supplier's recorded counterexample and explicitly revise or replace the supplier. Dependency-only revisions do not resolve earlier counterexamples.",
                        }
                    )
                    continue
                if decision == "closes":
                    continue
                if decision == "eliminates_route":
                    frontier.append(
                        {
                            **base,
                            "priority": 10,
                            "work_kind": "investigate",
                            "contribution_goal": "closes",
                            "reason": "A reviewed refutation eliminated this route; supply a replacement implication.",
                        }
                    )
                    continue
                if decision == "irrelevant":
                    frontier.append(
                        {
                            **base,
                            "priority": 10,
                            "work_kind": "investigate",
                            "contribution_goal": "closes",
                            "reason": "This helper was reviewed as irrelevant; supply the actual required implication.",
                        }
                    )
                    continue
                supported = status == "supported"
                frontier.append(
                    {
                        **base,
                        "priority": 15 if supported else 10,
                        "work_kind": "independent_review"
                        if supported
                        else "investigate",
                        "contribution_goal": "closes",
                        "reason": (
                            "Check exact applicability and quantitative costs of this supported helper."
                            if supported
                            else "Establish the missing necessary implication or identify its exact gap."
                        ),
                    }
                )
                if not supported:
                    frontier.append(
                        {
                            **base,
                            "priority": 20,
                            "work_kind": "counterexample",
                            "contribution_goal": "eliminates_route",
                            "reason": "Test this proposed route with an example satisfying its hypotheses and violating its conclusion.",
                        }
                    )
                if any(
                    value.strip()
                    for value in obligation.get(
                        "quantitative_requirements", {}
                    ).values()
                ):
                    frontier.append(
                        {
                            **base,
                            "priority": 30,
                            "work_kind": "quantitative_bound",
                            "contribution_goal": "improves_bound",
                            "reason": "Improve a bound needed by this obligation and quantify whether iteration remains useful.",
                        }
                    )
        target = context[0]
        if (
            not target["assessment"]["remaining_obligations"]
            and target["assessment"]["mathematical_status"] != "supported"
        ):
            frontier.append(
                {
                    "target_id": target_id,
                    "parent_claim_id": None,
                    "parent_revision": None,
                    "claim_id": target_id,
                    "claim_revision": target["claim"]["revision"],
                    "obligation_id": None,
                    "obligation": None,
                    "subject": target,
                    "contribution": None,
                    "priority": 10,
                    "work_kind": "investigate",
                    "contribution_goal": "closes",
                    "reason": "Develop and independently review the target argument; helper evidence does not prove it.",
                }
            )
        return sorted(
            frontier,
            key=lambda item: (
                item["priority"],
                item["parent_claim_id"] or "",
                item["obligation_id"] or "",
                item["work_kind"],
            ),
        )

    def progress(self, target_id: str) -> dict[str, Any]:
        """Count reviewed contributions, keeping root and graph totals separate."""
        context = self._context(target_id)

        def counts(nodes: list[dict[str, Any]]) -> dict[str, int]:
            total = closed = eliminated = improved = 0
            for node in nodes:
                contributions = self._contributions(node)
                for obligation in node["claim"]["spec"]["dependencies"]:
                    total += 1
                    decision = self._decision(
                        contributions.get(obligation["obligation_id"])
                    )
                    closed += decision == "closes"
                    eliminated += decision == "eliminates_route"
                    improved += decision == "improves_bound"
            return {
                "total_obligations": total,
                "closed_obligations": closed,
                "eliminated_routes": eliminated,
                "improved_bounds": improved,
                # Eliminating a failed route leaves the necessary implication open.
                "remaining_obligations": total - closed,
            }

        target = context[0]
        requires_revision = self._requires_revision(target)
        return {
            "target_id": target_id,
            "revision": target["claim"]["revision"],
            "mathematical_status": target["assessment"]["mathematical_status"],
            "counts": counts([] if requires_revision else [target]),
            "transitive_counts": counts(self._needed_context(context)),
            "target_remaining_obligations": target["assessment"][
                "remaining_obligations"
            ],
            "root_proved": False,
            "requires_target_revision": requires_revision,
            "interpretation": (
                "A reviewed counterexample requires an explicit target revision or replacement. Dependency-only revisions do not resolve earlier counterexamples. Prior obligations remain in the ledger, but helper results do not count as current progress."
                if requires_revision
                else "Reviewed obligation progress is separate from target correctness and kernel verification."
            ),
        }

    def assign(
        self,
        target_id: str,
        *,
        assignment_id: str,
        round_id: str,
        worker: str,
        question: str,
        owned_output: str,
        work_kind: str,
        claim_id: str,
        max_steps: int,
        max_seconds: float,
        additional_checks: list[str] | None = None,
    ) -> dict[str, Any]:
        """Persist a bounded work packet with complete revision-fenced context."""
        for name, value in (
            ("assignment_id", assignment_id),
            ("round_id", round_id),
            ("worker", worker),
            ("claim_id", claim_id),
        ):
            identifier(value, name)
        text(question, "question")
        if additional_checks is not None and not isinstance(additional_checks, list):
            raise ValueError("additional_checks must be an array of nonempty strings")
        extra_checks = [
            text(item, "additional_checks item") for item in (additional_checks or [])
        ]
        if work_kind not in WORK_KINDS:
            raise ValueError(f"work_kind must be one of {WORK_KINDS}")
        positive_int(max_steps, "max_steps")
        try:
            finite_seconds = type(max_seconds) in (int, float) and math.isfinite(
                max_seconds
            )
        except OverflowError:
            finite_seconds = False
        if not finite_seconds or max_seconds <= 0:
            raise ValueError("max_seconds must be finite and positive")
        output = assignment_output_path(owned_output)

        context = self._context(target_id)
        by_id = {item["claim"]["claim_id"]: item for item in context}
        if claim_id not in by_id:
            raise ValueError("claim_id must be reachable from the target")
        subject = by_id[claim_id]
        if self._requires_revision(context[0]) and (
            work_kind != "independent_review" or claim_id != target_id
        ):
            raise ValueError(
                "refuted target requires independent review of its refutation before revising or replacing it"
            )
        if self._requires_revision(subject) and work_kind != "independent_review":
            raise ValueError(
                "refuted subject requires independent review of its counterexample before an explicit revision or replacement"
            )
        # Boundary suppliers remain available for review or replacement, but
        # their sublemmas need another live path to serve this target.
        assignable_ids = {target_id}
        for node in self._needed_context(context):
            assignable_ids.add(node["claim"]["claim_id"])
            assignable_ids.update(
                item["supplier_id"] for item in node["claim"]["spec"]["dependencies"]
            )
        if claim_id not in assignable_ids:
            raise ValueError(
                "claim_id is only reachable through a discarded route or held dependency; revise that route or choose a currently relevant subject"
            )
        histories, context_revisions = self._history_context(context)
        if work_kind == "independent_review":
            authors = {subject["claim"]["spec"]["author"]}
            authors.update(item["author"] for item in histories[claim_id]["evidence"])
            if worker in authors:
                raise ValueError(
                    "independent review requires a fresh worker who authored neither the claim nor its evidence"
                )

        obligations = [
            {
                "parent_claim_id": node["claim"]["claim_id"],
                "parent_revision": node["claim"]["revision"],
                "obligation": obligation,
            }
            for node in context
            for obligation in node["claim"]["spec"]["dependencies"]
            if obligation["supplier_id"] == claim_id
        ]
        if work_kind == "quantitative_bound":
            needed_ids = {
                node["claim"]["claim_id"] for node in self._needed_context(context)
            }
            quantitative_need = any(
                item["parent_claim_id"] in needed_ids
                and self._decision(
                    self._contributions(by_id[item["parent_claim_id"]]).get(
                        item["obligation"]["obligation_id"]
                    )
                )
                not in {"irrelevant", "eliminates_route", "closes"}
                and any(
                    value.strip()
                    for value in item["obligation"]
                    .get("quantitative_requirements", {})
                    .values()
                )
                for item in obligations
            )
            target_need = claim_id == target_id and any(
                value.strip()
                for value in subject["claim"]["spec"]["quantitative_costs"].values()
            )
            if not (quantitative_need or target_need):
                raise ValueError(
                    "quantitative_bound requires a quantitative requirement relevant to the target"
                )

        packet = {
            "assignment_id": assignment_id,
            "round_id": round_id,
            "worker": worker,
            "target_id": target_id,
            "claim_id": claim_id,
            "question": question,
            "owned_output": output,
            "work_kind": work_kind,
            "max_steps": max_steps,
            "max_seconds": max_seconds,
            "target": context[0],
            "subject": subject,
            "dependency_context": context,
            "context_revisions": context_revisions,
            # Evidence and reviews can change without a claim revision. Fence
            # both the complete histories and the earlier derived assessments
            # so a concurrent publication cannot produce a stale work packet.
            "context_state_tokens": [
                {
                    "claim_id": history_id,
                    "state_token": histories[history_id]["state_token"],
                }
                for history_id in sorted(histories)
            ],
            "context_assessment_tokens": [
                {
                    "claim_id": node["claim"]["claim_id"],
                    "assessment_token": node["assessment"]["assessment_token"],
                }
                for node in context
            ],
            "required_by": obligations,
            "required_checks": [*REQUIRED_CHECKS, *extra_checks],
            "quantitative_checks": {
                "offered_costs": subject["claim"]["spec"]["quantitative_costs"],
                "parent_requirements": obligations,
                "unknown_costs_close_obligations": False,
            },
            # Complete history preserves exact failed routes and corrected
            # interpretations even when later revisions supersede them.
            "history_context": histories,
            "artifacts": self._artifacts(histories),
            "permitted_outcomes": list(PERMITTED_OUTCOMES),
            "operational_outcomes": {
                "timeout": "operational outcome; no mathematical evidence",
                "provider_failure": "operational outcome; no mathematical evidence",
                "tool_unavailable": "operational outcome; no mathematical evidence",
            },
            "verification_policy": "Written arguments, independent reviews, finite computations, sources, and reported kernel artifacts remain distinct; this packet grants no proof authority.",
        }
        return self.store.save_assignment(packet)
