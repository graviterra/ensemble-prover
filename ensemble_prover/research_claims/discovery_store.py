"""Durable admission and atomic research-result application, on the ledger DB.

One process owns execution; its workers cooperate asynchronously. Model and
tool operations never run inside a database transaction. Dispatch reservations
are conservative intents, not claims that the provider billed those requests.
"""

from __future__ import annotations

import fcntl
import json
import time
import uuid
from contextlib import contextmanager
from typing import Any, Iterator

from .model import json_text
from .store import ResearchStore, ResearchStoreError, RevisionConflict


class AdmissionStopped(RuntimeError):
    """No more external work may be started under the saved authorization."""


def provider_routes(record: dict[str, Any]) -> tuple[str, str]:
    """Schema-5 routing is explicit, including in upgraded API-only ledgers."""
    provider = record.get("provider")
    review_provider = record.get("review_provider")
    if (
        not isinstance(provider, str)
        or provider not in ("openai", "codex")
        or not isinstance(review_provider, str)
        or review_provider not in ("openai", "codex")
    ):
        raise ValueError(
            "research provider and review_provider must be openai or codex"
        )
    return provider, review_provider


class DiscoveryStore(ResearchStore):
    _applying = False

    def __enter__(self) -> DiscoveryStore:
        return self

    @contextmanager
    def _transaction(self, *, write: bool = False) -> Iterator[None]:
        # Only the synchronous atomic() boundary below may compose mutations.
        # Ordinary read snapshots retain ResearchStore's no-mutation rule.
        if self._applying and self._connection.in_transaction:
            yield
        else:
            with super()._transaction(write=write):
                yield

    @contextmanager
    def atomic(self) -> Iterator[None]:
        if self._applying or self._connection.in_transaction:
            raise ResearchStoreError("nested discovery transaction")
        with super()._transaction(write=True):
            self._applying = True
            try:
                yield
            finally:
                self._applying = False

    @contextmanager
    def execution_lock(self) -> Iterator[None]:
        # Advisory process lock: released by the OS on crash, never stolen from
        # a slow but living controller. It does not lock manual ledger readers.
        with (self.directory / "discovery.lock").open("a+b") as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise ResearchStoreError(
                    "another discovery controller owns this run"
                ) from exc
            try:
                yield
            finally:
                fcntl.flock(handle, fcntl.LOCK_UN)

    def run_record(self) -> dict[str, Any]:
        with self._transaction():
            row = self._connection.execute(
                "SELECT record FROM discovery_runs WHERE run_id = 'main'"
            ).fetchone()
            if row is None:
                raise ResearchStoreError("no autonomous discovery run initialized")
            return json.loads(row[0])

    def save_run(self, record: dict[str, Any]) -> None:
        with self._transaction(write=True):
            self._connection.execute(
                "INSERT INTO discovery_runs VALUES ('main', ?) "
                "ON CONFLICT(run_id) DO UPDATE SET record = excluded.record",
                (json_text(record),),
            )

    def jobs(self) -> list[dict[str, Any]]:
        with self._transaction():
            return [
                json.loads(row[0])
                for row in self._connection.execute(
                    "SELECT record FROM discovery_jobs ORDER BY rowid"
                )
            ]

    def job(self, job_id: str) -> dict[str, Any]:
        with self._transaction():
            row = self._connection.execute(
                "SELECT record FROM discovery_jobs WHERE job_id = ?", (job_id,)
            ).fetchone()
            if row is None:
                raise ResearchStoreError("unknown discovery job")
            return json.loads(row[0])

    def save_job(self, record: dict[str, Any]) -> None:
        with self._transaction(write=True):
            previous = self._connection.execute(
                "SELECT record FROM discovery_jobs WHERE job_id = ?",
                (record["job_id"],),
            ).fetchone()
            if record["status"] == "pending" and (
                previous is None
                or json.loads(previous[0])["status"] != "pending"
                or "queue_order" not in record
            ):
                # New work and continuing turns join the pending queue's tail.
                # Keep the order in job JSON so crashes preserve fairness and
                # older ledgers need no table or authorization changes.
                record["queue_order"] = 1 + max(
                    (job.get("queue_order", 0) for job in self.jobs()), default=0
                )
            self._connection.execute(
                "INSERT INTO discovery_jobs VALUES (?, ?, ?) ON CONFLICT(job_id) "
                "DO UPDATE SET status = excluded.status, record = excluded.record",
                (record["job_id"], record["status"], json_text(record)),
            )

    def add_job(
        self,
        claim_id: str,
        question: str,
        *,
        role: str = "research",
        parent_job: str | None = None,
        evidence_id: str | None = None,
    ) -> dict[str, Any]:
        job_id = "job-" + uuid.uuid4().hex
        claim = self.get_claim(claim_id)
        record = {
            "job_id": job_id,
            "claim_id": claim_id,
            "revision": claim["revision"],
            "worker": "worker-" + uuid.uuid4().hex,
            "role": role,
            "question": question,
            "parent_job": parent_job,
            "evidence_id": evidence_id,
            "status": "pending",
            "turn": 0,
            "messages": [],
            "response": None,
            "last_error": None,
            "last_error_details": None,
            "tool_result": None,
            "request": None,
            "inbox": [],
            "supersedes_review_ids": [],
        }
        self.save_job(record)
        return record

    def stop_reason(self, record: dict[str, Any] | None = None) -> str | None:
        run = record or self.run_record()
        root = self.get_claim(run["target_id"])
        if (
            root["revision"] != run["target_revision"]
            or root["spec"] != run["target_spec"]
        ):
            return "target_changed"
        if run["deadline"] is not None and time.time() >= run["deadline"]:
            return "deadline_exhausted"
        if run["requests_used"] >= run["max_requests"]:
            return "budget_exhausted"
        return None

    def authorize(self, job_id: str, turn: int) -> None:
        with self.atomic():
            run = self.run_record()
            reason = self.stop_reason(run)
            job = self.job(job_id)
            if reason or run["status"] != "running":
                raise AdmissionStopped(reason or run["status"])
            if job["status"] != "running" or job["turn"] != turn:
                raise AdmissionStopped("stale_job")
            if self.get_claim(job["claim_id"])["revision"] != job["revision"]:
                raise AdmissionStopped("claim_changed")
            run["requests_used"] += 1
            self.save_run(run)
            self._event(
                job["claim_id"],
                job["revision"],
                "discovery_dispatch_intent",
                {
                    "job_id": job_id,
                    "turn": turn,
                    "request_number": run["requests_used"],
                    "request_artifact": job["request"],
                },
            )

    def status(self) -> dict[str, Any]:
        with self.read_snapshot():
            run = self.run_record()
            from .proof_bridge import configuration, handoff_bundle, validate_receipt

            configuration(run)
            proofs = []
            stale_proofs = []
            for job in self.jobs():
                if job["role"] == "formalization" and job["status"] == "verified":
                    # A normal ledger revision retires this proof's authority;
                    # it does not corrupt its historical Lean artifacts. Check
                    # the handoff before opening the old campaign or receipt.
                    try:
                        handoff_bundle(self, job)
                    except RevisionConflict:
                        stale_proofs.append(
                            {
                                "program_id": job["job_id"],
                                "claim_id": job["claim_id"],
                                "reason": "claim_changed",
                            }
                        )
                        continue
                    receipt = validate_receipt(self, job, job.get("proof_receipt"))
                    proofs.append(
                        {
                            "program_id": job["job_id"],
                            "claim_id": job["claim_id"],
                            "polarity": job["polarity"],
                            "receipt": receipt,
                        }
                    )
            return {
                **run,
                "status": (
                    "target_changed"
                    if self.stop_reason(run) == "target_changed"
                    else "stale_proof"
                )
                if stale_proofs
                and run["status"] in {"proved", "refuted"}
                and not any(item["claim_id"] == run["target_id"] for item in proofs)
                else run["status"],
                "jobs": [
                    {
                        **{
                            key: job[key]
                            for key in (
                                "job_id",
                                "claim_id",
                                "role",
                                "status",
                                "turn",
                                "last_error",
                            )
                        },
                        "last_error_details": job.get("last_error_details"),
                    }
                    for job in self.jobs()
                ],
                "assessment": self.assessment(run["target_id"]),
                "root_proved": any(
                    item["claim_id"] == run["target_id"] and item["polarity"] == "prove"
                    for item in proofs
                ),
                "root_refuted": any(
                    item["claim_id"] == run["target_id"]
                    and item["polarity"] == "refute"
                    for item in proofs
                ),
                "verified_proofs": proofs,
                "stale_proofs": stale_proofs,
                "novelty": "not_established_by_literature_review",
            }
