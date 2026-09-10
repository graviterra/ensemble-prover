"""A local, revision-fenced ledger for research assertions and their provenance.

This database records assertions, not authenticated identities or kernel trust.
All public reads use a consistent SQLite snapshot; mutations take a write lock
before checking revisions. No submitted experiment command is executed.
"""

from __future__ import annotations

import hashlib
import json
import os
import sqlite3
import uuid
from contextlib import contextmanager
from copy import deepcopy
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator

from .model import (
    CONTRIBUTION_DECISIONS,
    EVIDENCE_KINDS,
    OPERATIONAL_OUTCOMES,
    REVIEW_VERDICTS,
    ClaimSpec,
    assignment_context_record,
    assignment_output_path,
    compatibility_issues,
    identifier,
    json_text,
    positive_int,
    text,
    validate_json_structure,
)

# Version 4 adds waiting jobs and durable child-result notification semantics.
# Version 3 adds executable research state in the same transactional database.
# Version 2 introduced conflict-aware review interpretation.
SCHEMA_VERSION = 4
APPLICATION_ID = 0x52534348


class ResearchStoreError(ValueError):
    """Invalid ledger input or missing ledger content."""


class RevisionConflict(ResearchStoreError):
    """The submitted work no longer targets the current claim revision."""


class UnknownSchema(ResearchStoreError):
    """The ledger format is unknown; it must not be silently upgraded."""


_SCHEMA = {
    "claims": "claim_id TEXT PRIMARY KEY, revision INTEGER NOT NULL",
    "revisions": "claim_id TEXT NOT NULL, revision INTEGER NOT NULL, spec TEXT NOT NULL, created_at TEXT NOT NULL, cause TEXT NOT NULL, PRIMARY KEY(claim_id, revision)",
    "artifacts": "artifact_id TEXT PRIMARY KEY, content BLOB NOT NULL, metadata TEXT NOT NULL",
    "evidence": "evidence_id TEXT PRIMARY KEY, claim_id TEXT NOT NULL, revision INTEGER NOT NULL, record TEXT NOT NULL",
    "reviews": "review_id TEXT PRIMARY KEY, claim_id TEXT NOT NULL, revision INTEGER NOT NULL, record TEXT NOT NULL",
    "contributions": "contribution_id TEXT PRIMARY KEY, claim_id TEXT NOT NULL, revision INTEGER NOT NULL, record TEXT NOT NULL",
    "operations": "operation_id TEXT PRIMARY KEY, claim_id TEXT NOT NULL, revision INTEGER NOT NULL, record TEXT NOT NULL",
    "assignments": "assignment_id TEXT PRIMARY KEY, owned_output TEXT NOT NULL, round_id TEXT NOT NULL, question TEXT NOT NULL, status TEXT NOT NULL, record TEXT NOT NULL",
    "events": "sequence INTEGER PRIMARY KEY AUTOINCREMENT, claim_id TEXT, revision INTEGER, kind TEXT NOT NULL, record TEXT NOT NULL",
    "discovery_runs": "run_id TEXT PRIMARY KEY, record TEXT NOT NULL",
    "discovery_jobs": "job_id TEXT PRIMARY KEY, status TEXT NOT NULL, record TEXT NOT NULL",
}
_COLUMNS = {
    "claims": ["claim_id", "revision"],
    "revisions": ["claim_id", "revision", "spec", "created_at", "cause"],
    "artifacts": ["artifact_id", "content", "metadata"],
    "evidence": ["evidence_id", "claim_id", "revision", "record"],
    "reviews": ["review_id", "claim_id", "revision", "record"],
    "contributions": ["contribution_id", "claim_id", "revision", "record"],
    "operations": ["operation_id", "claim_id", "revision", "record"],
    "assignments": [
        "assignment_id",
        "owned_output",
        "round_id",
        "question",
        "status",
        "record",
    ],
    "events": ["sequence", "claim_id", "revision", "kind", "record"],
    "discovery_runs": ["run_id", "record"],
    "discovery_jobs": ["job_id", "status", "record"],
}
_INDEX_SCHEMA = {
    "active_output": "CREATE UNIQUE INDEX active_output ON assignments(owned_output) WHERE status = 'pending'",
    "round_question": "CREATE UNIQUE INDEX round_question ON assignments(round_id, question)",
}


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _id(prefix: str) -> str:
    return f"{prefix}-{uuid.uuid4().hex}"


def _object(value: Any, name: str, *, max_depth: int = 64) -> dict[str, Any]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise ResearchStoreError(f"{name} must be an object with string keys")
    try:
        validate_json_structure(value, max_depth=max_depth)
        return json.loads(json_text(value))
    except (TypeError, ValueError) as exc:
        raise ResearchStoreError(f"{name}: {exc}") from exc


def _active_records(
    records: list[dict[str, Any]], id_key: str, supersedes_key: str
) -> list[dict[str, Any]]:
    superseded = {
        record_id for item in records for record_id in item.get(supersedes_key, [])
    }
    return [item for item in records if item[id_key] not in superseded]


def _supersession_ids(value: list[str] | None, name: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list):
        raise ResearchStoreError(f"{name} must be an array of distinct record IDs")
    result = [identifier(item, name) for item in value]
    if len(set(result)) != len(result):
        raise ResearchStoreError(f"{name} must contain distinct record IDs")
    return result


def _check_supersession(
    ids: list[str], records: list[dict[str, Any]], id_key: str, supersedes_key: str
) -> None:
    known = {item[id_key] for item in records}
    if not set(ids) <= known:
        raise ResearchStoreError(
            "superseded records must belong to the same current evidence or obligation state"
        )
    active = {item[id_key] for item in _active_records(records, id_key, supersedes_key)}
    if not set(ids) <= active:
        raise RevisionConflict(
            "a superseded assessment was already replaced; reread the ledger"
        )


class ResearchStore:
    """Open ``directory/ledger.sqlite3``; creation is always explicit."""

    def __init__(
        self, directory: str | Path, create: bool = False, *, upgrade: bool = False
    ):
        if create and upgrade:
            raise ResearchStoreError("create and upgrade are mutually exclusive")
        self._snapshot_assessment_cache: dict[str, dict[str, Any]] | None = None
        self.directory = Path(directory)
        self.path = self.directory / "ledger.sqlite3"
        if not self.path.exists() and not create:
            raise ResearchStoreError(f"research ledger does not exist: {self.path}")
        if create:
            self.directory.mkdir(parents=True, exist_ok=True)
            try:
                descriptor = os.open(
                    self.path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600
                )
            except FileExistsError as exc:
                raise ResearchStoreError(
                    f"research ledger already exists: {self.path}"
                ) from exc
            os.close(descriptor)
        # URI mode prevents an existing ledger from being silently recreated
        # between the existence check and connection opening.
        self._connection = sqlite3.connect(
            f"{self.path.resolve().as_uri()}?mode=rw",
            uri=True,
            timeout=30,
            isolation_level=None,
        )
        self._connection.row_factory = sqlite3.Row
        try:
            with self._transaction(write=True):
                tables = self._tables()
                if not tables and create:
                    for name, fields in _SCHEMA.items():
                        self._connection.execute(f"CREATE TABLE {name} ({fields})")
                    for definition in _INDEX_SCHEMA.values():
                        self._connection.execute(definition)
                    self._connection.execute(
                        f"PRAGMA application_id = {APPLICATION_ID}"
                    )
                    self._connection.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
                version = self._connection.execute("PRAGMA user_version").fetchone()[0]
                if upgrade and version in (1, 2, 3):
                    # Validate the entire known legacy schema before changing
                    # anything. Records/artifacts stay byte-for-byte intact.
                    self._validate_schema(expected_version=version)
                    if version < 3:
                        for name in ("discovery_runs", "discovery_jobs"):
                            self._connection.execute(
                                f"CREATE TABLE {name} ({_SCHEMA[name]})"
                            )
                    self._connection.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
                self._validate_schema()
            self._connection.execute("PRAGMA journal_mode = WAL")
            self._connection.execute("PRAGMA synchronous = FULL")
        except BaseException:
            self._connection.close()
            raise

    def __enter__(self) -> ResearchStore:
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()

    def close(self) -> None:
        self._connection.close()

    @contextmanager
    def _transaction(self, *, write: bool = False) -> Iterator[None]:
        if self._connection.in_transaction:
            if write:
                raise ResearchStoreError(
                    "cannot mutate inside an active ledger snapshot"
                )
            yield
            return
        self._connection.execute("BEGIN IMMEDIATE" if write else "BEGIN")
        try:
            yield
            self._connection.commit()
        except BaseException:
            try:
                if self._connection.in_transaction:
                    self._connection.rollback()
            except BaseException:
                # Preserve the original failure while preventing a failed
                # rollback from exposing uncommitted writes as a read snapshot.
                try:
                    self._connection.close()
                except BaseException:
                    pass
            raise

    @contextmanager
    def read_snapshot(self) -> Iterator[ResearchStore]:
        """Compose public reads against one snapshot; mutations are forbidden."""
        with self._transaction():
            previous = self._snapshot_assessment_cache
            if previous is None:
                self._snapshot_assessment_cache = {}
            try:
                yield self
            finally:
                self._snapshot_assessment_cache = previous

    def _tables(self) -> set[str]:
        return {
            row[0]
            for row in self._connection.execute(
                "SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT GLOB 'sqlite_*'"
            )
        }

    def _validate_schema(self, *, expected_version: int = SCHEMA_VERSION) -> None:
        schema = {
            name: fields
            for name, fields in _SCHEMA.items()
            if expected_version >= 3 or not name.startswith("discovery_")
        }
        version = self._connection.execute("PRAGMA user_version").fetchone()[0]
        application = self._connection.execute("PRAGMA application_id").fetchone()[0]
        if (
            version != expected_version
            or application != APPLICATION_ID
            or self._tables() != set(schema)
        ):
            raise UnknownSchema(
                "unrecognized research ledger schema; no migration was attempted. "
                "For a version 1, 2, or 3 ledger, explicitly run research_claims upgrade DIRECTORY."
            )
        for name, expected in _COLUMNS.items():
            if name not in schema:
                continue
            actual = [
                row[1] for row in self._connection.execute(f"PRAGMA table_info({name})")
            ]
            if actual != expected:
                raise UnknownSchema(
                    f"unexpected columns in {name}; no migration was attempted"
                )
        expected_definitions = {
            **{
                name: f"CREATE TABLE {name} ({fields})"
                for name, fields in schema.items()
            },
            **_INDEX_SCHEMA,
        }
        definitions = {
            row["name"]: row["sql"]
            for row in self._connection.execute(
                "SELECT name, sql FROM sqlite_master WHERE name NOT GLOB 'sqlite_*'"
            )
        }
        if definitions != expected_definitions:
            raise UnknownSchema(
                "unexpected ledger constraints or indexes; no migration was attempted"
            )

    def _event(
        self,
        claim_id: str | None,
        revision: int | None,
        kind: str,
        record: dict[str, Any],
    ) -> None:
        self._connection.execute(
            "INSERT INTO events(claim_id, revision, kind, record) VALUES (?, ?, ?, ?)",
            (claim_id, revision, kind, json_text({"created_at": _now(), **record})),
        )

    def _claim(self, claim_id: str) -> dict[str, Any]:
        identifier(claim_id, "claim_id")
        row = self._connection.execute(
            "SELECT c.claim_id, c.revision, r.spec FROM claims c JOIN revisions r "
            "ON c.claim_id = r.claim_id AND c.revision = r.revision WHERE c.claim_id = ?",
            (claim_id,),
        ).fetchone()
        if row is None:
            raise ResearchStoreError(f"unknown claim: {claim_id}")
        return {
            "claim_id": row["claim_id"],
            "revision": row["revision"],
            "spec": json.loads(row["spec"]),
        }

    def _fenced_claim(self, claim_id: str, expected_revision: int) -> dict[str, Any]:
        positive_int(expected_revision, "expected_revision")
        claim = self._claim(claim_id)
        if claim["revision"] != expected_revision:
            raise RevisionConflict(
                f"stale claim {claim_id}: expected revision {expected_revision}, current revision {claim['revision']}"
            )
        return claim

    def _all_claims(self) -> list[dict[str, Any]]:
        return [
            self._claim(row[0])
            for row in self._connection.execute(
                "SELECT claim_id FROM claims ORDER BY claim_id"
            )
        ]

    def _validate_graph(self, spec: ClaimSpec) -> None:
        specs = {
            claim["claim_id"]: ClaimSpec.from_dict(claim["spec"])
            for claim in self._all_claims()
        }
        specs[spec.claim_id] = spec
        graph = {
            key: {item.supplier_id for item in value.dependencies}
            | set(value.supersedes)
            for key, value in specs.items()
        }
        for reference in graph[spec.claim_id]:
            if reference not in specs:
                raise ResearchStoreError(f"unknown claim reference: {reference}")
        # Iterative traversal permits long dependency chains without exhausting
        # Python's recursion limit. Supersession cycles are rejected as well.
        visiting: set[str] = set()
        visited: set[str] = set()
        for root in graph:
            stack = [(root, False)]
            while stack:
                node, leaving = stack.pop()
                if leaving:
                    visiting.remove(node)
                    visited.add(node)
                elif node in visiting:
                    raise ResearchStoreError("claim dependency or supersession cycle")
                elif node not in visited:
                    visiting.add(node)
                    stack.append((node, True))
                    stack.extend((child, False) for child in sorted(graph[node]))

    def _insert_revision(self, spec: ClaimSpec, revision: int, cause: str) -> None:
        self._connection.execute(
            "INSERT INTO revisions(claim_id, revision, spec, created_at, cause) VALUES (?, ?, ?, ?, ?)",
            (spec.claim_id, revision, json_text(spec.to_dict()), _now(), cause),
        )
        self._connection.execute(
            "INSERT INTO claims(claim_id, revision) VALUES (?, ?) "
            "ON CONFLICT(claim_id) DO UPDATE SET revision = excluded.revision",
            (spec.claim_id, revision),
        )
        self._event(
            spec.claim_id,
            revision,
            "claim_revision",
            {"cause": cause, "spec": spec.to_dict()},
        )

    def create_claim(self, spec: ClaimSpec) -> dict[str, Any]:
        if not isinstance(spec, ClaimSpec):
            raise ResearchStoreError("spec must be a ClaimSpec")
        with self._transaction(write=True):
            if self._connection.execute(
                "SELECT 1 FROM claims WHERE claim_id = ?", (spec.claim_id,)
            ).fetchone():
                raise ResearchStoreError(f"claim already exists: {spec.claim_id}")
            self._validate_graph(spec)
            self._insert_revision(spec, 1, "created")
            return self._claim(spec.claim_id)

    def revise_claim(
        self, claim_id: str, spec: ClaimSpec, *, expected_revision: int
    ) -> dict[str, Any]:
        if not isinstance(spec, ClaimSpec) or spec.claim_id != claim_id:
            raise ResearchStoreError("revision spec must retain the same claim_id")
        with self._transaction(write=True):
            current = self._fenced_claim(claim_id, expected_revision)
            self._validate_graph(spec)
            claims = self._all_claims()
            affected = {claim_id}
            while True:
                additional = {
                    claim["claim_id"]
                    for claim in claims
                    if any(
                        item["supplier_id"] in affected
                        for item in claim["spec"]["dependencies"]
                    )
                } - affected
                if not additional:
                    break
                affected.update(additional)
            self._insert_revision(spec, current["revision"] + 1, "revised")
            for claim in claims:
                if claim["claim_id"] in affected - {claim_id}:
                    self._insert_revision(
                        ClaimSpec.from_dict(claim["spec"]),
                        claim["revision"] + 1,
                        f"dependency_revised:{claim_id}",
                    )
            return self._claim(claim_id)

    def get_claim(self, claim_id: str) -> dict[str, Any]:
        with self._transaction():
            return self._claim(claim_id)

    def list_claims(self) -> list[dict[str, Any]]:
        with self._transaction():
            return self._all_claims()

    def put_artifact(self, content: bytes, *, name: str) -> str:
        if not isinstance(content, bytes):
            raise ResearchStoreError("artifact content must be bytes")
        text(name, "artifact name")
        digest = hashlib.sha256(content).hexdigest()
        with self._transaction(write=True):
            existing = self._connection.execute(
                "SELECT content FROM artifacts WHERE artifact_id = ?", (digest,)
            ).fetchone()
            if existing is not None:
                if existing[0] != content:
                    raise ResearchStoreError("artifact integrity failure")
            else:
                metadata = {
                    "artifact_id": digest,
                    "name": name,
                    "size_bytes": len(content),
                    "created_at": _now(),
                }
                self._connection.execute(
                    "INSERT INTO artifacts(artifact_id, content, metadata) VALUES (?, ?, ?)",
                    (digest, content, json_text(metadata)),
                )
                self._event(None, None, "artifact_added", metadata)
            return digest

    def _artifact(self, artifact_id: str) -> bytes:
        if (
            not isinstance(artifact_id, str)
            or len(artifact_id) != 64
            or any(char not in "0123456789abcdef" for char in artifact_id)
        ):
            raise ResearchStoreError("artifact_id must be a lowercase SHA256 digest")
        row = self._connection.execute(
            "SELECT content FROM artifacts WHERE artifact_id = ?", (artifact_id,)
        ).fetchone()
        if row is None:
            raise ResearchStoreError(f"unknown artifact: {artifact_id}")
        content = bytes(row[0])
        if hashlib.sha256(content).hexdigest() != artifact_id:
            raise ResearchStoreError(f"artifact integrity failure: {artifact_id}")
        return content

    def read_artifact(self, artifact_id: str) -> bytes:
        with self._transaction():
            return self._artifact(artifact_id)

    def _insert_record(
        self,
        table: str,
        record_id: str,
        claim_id: str,
        revision: int,
        record: dict[str, Any],
    ) -> None:
        # Table names are internal constants, never submitted text.
        self._connection.execute(
            f"INSERT INTO {table} VALUES (?, ?, ?, ?)",
            (record_id, claim_id, revision, json_text(record)),
        )
        self._event(claim_id, revision, table, record)

    def _records(
        self, table: str, claim_id: str, revision: int | None = None
    ) -> list[dict[str, Any]]:
        query = f"SELECT record FROM {table} WHERE claim_id = ?"
        parameters: tuple[Any, ...] = (claim_id,)
        if revision is not None:
            query += " AND revision = ?"
            parameters += (revision,)
        return [
            json.loads(row[0])
            for row in self._connection.execute(query + " ORDER BY rowid", parameters)
        ]

    def add_evidence(
        self,
        claim_id: str,
        *,
        expected_revision: int,
        kind: str,
        author: str,
        artifact_ids: list[str],
        details: dict[str, Any],
    ) -> dict[str, Any]:
        if kind not in EVIDENCE_KINDS:
            raise ResearchStoreError(f"unknown evidence kind: {kind}")
        identifier(author, "author")
        details = _object(details, "details")
        if (
            not isinstance(artifact_ids, list)
            or not artifact_ids
            or any(not isinstance(item, str) for item in artifact_ids)
        ):
            raise ResearchStoreError("evidence requires a nonempty artifact_ids array")
        if len(set(artifact_ids)) != len(artifact_ids):
            raise ResearchStoreError("duplicate artifact_ids")
        if kind == "exact_computation":
            text(details.get("scope"), "computation scope")
            command = details.get("command")
            if (
                not isinstance(command, list)
                or not command
                or any(not isinstance(item, str) for item in command)
                or not command[0].strip()
            ):
                raise ResearchStoreError(
                    "computation command must be a nonempty argv array"
                )
            if not _object(details.get("environment"), "computation environment"):
                raise ResearchStoreError("computation environment must be recorded")
            if type(details.get("exit_code")) is not int:
                raise ResearchStoreError("computation exit_code must be an integer")
        if kind == "counterexample":
            text(details.get("hypotheses_check"), "counterexample hypotheses_check")
            text(
                details.get("conclusion_violation"),
                "counterexample conclusion_violation",
            )
        with self._transaction(write=True):
            self._fenced_claim(claim_id, expected_revision)
            for artifact_id in artifact_ids:
                self._artifact(artifact_id)
            evidence_id = _id("evidence")
            record = {
                "evidence_id": evidence_id,
                "claim_id": claim_id,
                "revision": expected_revision,
                "kind": kind,
                "author": author,
                "artifact_ids": artifact_ids,
                "details": details,
                "created_at": _now(),
            }
            self._insert_record(
                "evidence", evidence_id, claim_id, expected_revision, record
            )
            return record

    def add_review(
        self,
        claim_id: str,
        *,
        expected_revision: int,
        evidence_id: str,
        reviewer: str,
        verdict: str,
        rationale: str,
        supersedes_review_ids: list[str] | None = None,
    ) -> dict[str, Any]:
        identifier(reviewer, "reviewer")
        text(rationale, "rationale")
        if verdict not in REVIEW_VERDICTS:
            raise ResearchStoreError(f"unknown review verdict: {verdict}")
        supersedes = _supersession_ids(supersedes_review_ids, "supersedes_review_ids")
        with self._transaction(write=True):
            claim = self._fenced_claim(claim_id, expected_revision)
            evidence = next(
                (
                    item
                    for item in self._records("evidence", claim_id, expected_revision)
                    if item["evidence_id"] == evidence_id
                ),
                None,
            )
            if evidence is None:
                raise ResearchStoreError(
                    "review evidence must belong to the current claim revision"
                )
            if reviewer in {claim["spec"]["author"], evidence["author"]}:
                raise ResearchStoreError(
                    "independent review cannot be authored by the claim or evidence author"
                )
            if verdict == "supported" and evidence["kind"] != "written_proof":
                raise ResearchStoreError("support requires review of a written_proof")
            if verdict == "refuted" and evidence["kind"] != "counterexample":
                raise ResearchStoreError(
                    "refutation requires review of a counterexample"
                )
            _check_supersession(
                supersedes,
                [
                    item
                    for item in self._records("reviews", claim_id, expected_revision)
                    if item["evidence_id"] == evidence_id
                ],
                "review_id",
                "supersedes_review_ids",
            )
            review_id = _id("review")
            record = {
                "review_id": review_id,
                "claim_id": claim_id,
                "revision": expected_revision,
                "evidence_id": evidence_id,
                "reviewer": reviewer,
                "verdict": verdict,
                "rationale": rationale,
                "supersedes_review_ids": supersedes,
                "created_at": _now(),
            }
            self._insert_record(
                "reviews", review_id, claim_id, expected_revision, record
            )
            return record

    def record_operation(
        self,
        claim_id: str,
        *,
        expected_revision: int,
        outcome: str,
        details: dict[str, Any],
    ) -> dict[str, Any]:
        if outcome not in OPERATIONAL_OUTCOMES:
            raise ResearchStoreError(f"unknown operational outcome: {outcome}")
        details = _object(details, "details")
        with self._transaction(write=True):
            self._fenced_claim(claim_id, expected_revision)
            operation_id = _id("operation")
            record = {
                "operation_id": operation_id,
                "claim_id": claim_id,
                "revision": expected_revision,
                "outcome": outcome,
                "details": details,
                "created_at": _now(),
            }
            self._insert_record(
                "operations", operation_id, claim_id, expected_revision, record
            )
            return record

    def _verification(
        self, claim_id: str, revision: int
    ) -> tuple[str, dict[str, Any], str]:
        evidence = self._records("evidence", claim_id, revision)
        reviews = self._records("reviews", claim_id, revision)
        active_reviews = _active_records(reviews, "review_id", "supersedes_review_ids")
        verdicts_by_evidence: dict[str, set[str]] = {}
        for review in active_reviews:
            verdicts_by_evidence.setdefault(review["evidence_id"], set()).add(
                review["verdict"]
            )
        positive = negative = disputed = False
        for item in evidence:
            verdicts = verdicts_by_evidence.get(item["evidence_id"], set())
            if verdicts == {"dismissed"}:
                continue
            if "dismissed" in verdicts:
                # A dismissal is not an implicit override of a contrary review.
                disputed = True
                continue
            if item["kind"] == "written_proof" and "supported" in verdicts:
                positive = True
            if item["kind"] == "counterexample" and "refuted" in verdicts:
                negative = True
            if item["kind"] in {"gap", "counterexample"} and not (
                item["kind"] == "counterexample" and verdicts == {"refuted"}
            ):
                disputed = True
            if "unresolved" in verdicts:
                disputed = True
        if (positive and negative) or disputed:
            status = "unresolved"
        elif negative:
            status = "refuted"
        elif positive:
            status = "supported"
        else:
            status = "proposed"
        grouped = {
            "written_proofs": "written_proof",
            "exact_computations": "exact_computation",
            "primary_sources": "primary_source",
            "kernel_reports": "kernel_report",
            "gaps": "gap",
            "counterexamples": "counterexample",
        }
        verification: dict[str, Any] = {
            key: [item for item in evidence if item["kind"] == kind]
            for key, kind in grouped.items()
        }
        verification.update(
            {
                "independent_reviews": reviews,
                "active_review_ids": [item["review_id"] for item in active_reviews],
                "dismissed_evidence_ids": [
                    item["evidence_id"]
                    for item in evidence
                    if verdicts_by_evidence.get(item["evidence_id"]) == {"dismissed"}
                ],
                "kernel_verified": False,
            }
        )
        state_token = hashlib.sha256(
            json_text({"evidence": evidence, "reviews": reviews}).encode()
        ).hexdigest()
        return status, verification, state_token

    def assess_contribution(
        self,
        parent_id: str,
        *,
        expected_revision: int,
        obligation_id: str,
        expected_supplier_revision: int,
        reviewer: str,
        decision: str,
        costs_acceptable: bool,
        rationale: str,
        supersedes_contribution_ids: list[str] | None = None,
        expected_supplier_state_token: str | None = None,
    ) -> dict[str, Any]:
        identifier(reviewer, "reviewer")
        identifier(obligation_id, "obligation_id")
        text(rationale, "rationale")
        if decision not in CONTRIBUTION_DECISIONS:
            raise ResearchStoreError(f"unknown contribution decision: {decision}")
        if type(costs_acceptable) is not bool:
            raise ResearchStoreError("costs_acceptable must be an explicit boolean")
        supersedes = _supersession_ids(
            supersedes_contribution_ids, "supersedes_contribution_ids"
        )
        if expected_supplier_state_token is not None:
            text(expected_supplier_state_token, "expected_supplier_state_token")
        if supersedes and expected_supplier_state_token is None:
            raise ResearchStoreError(
                "supersession requires expected_supplier_state_token"
            )
        with self._transaction(write=True):
            parent = self._fenced_claim(parent_id, expected_revision)
            spec = ClaimSpec.from_dict(parent["spec"])
            obligation = next(
                (
                    item
                    for item in spec.dependencies
                    if item.obligation_id == obligation_id
                ),
                None,
            )
            if obligation is None:
                raise ResearchStoreError(f"unknown parent obligation: {obligation_id}")
            supplier = self._fenced_claim(
                obligation.supplier_id, expected_supplier_revision
            )
            supplier_spec = ClaimSpec.from_dict(supplier["spec"])
            supplier_assessment = self._assessment(supplier["claim_id"])
            status = supplier_assessment["mathematical_status"]
            token = supplier_assessment["assessment_token"]
            if (
                expected_supplier_state_token is not None
                and expected_supplier_state_token != token
            ):
                raise RevisionConflict(
                    "supplier assessment state changed; reread before reviewing"
                )
            _check_supersession(
                supersedes,
                [
                    item
                    for item in self._records(
                        "contributions", parent_id, expected_revision
                    )
                    if item["obligation_id"] == obligation_id
                    and item["supplier_revision"] == expected_supplier_revision
                    and item["supplier_state_token"] == token
                ],
                "contribution_id",
                "supersedes_contribution_ids",
            )
            issues = compatibility_issues(supplier_spec, obligation)
            if reviewer == supplier_spec.author:
                raise ResearchStoreError(
                    "contribution review must be independent of the supplier author"
                )
            if decision in {"closes", "improves_bound"}:
                if status != "supported":
                    raise ResearchStoreError(
                        "positive contribution requires a currently supported supplier"
                    )
                if not costs_acceptable:
                    raise ResearchStoreError(
                        "positive contribution requires explicit acceptance of quantitative costs"
                    )
            if decision == "closes" and issues:
                raise ResearchStoreError(
                    f"supplier does not meet the required contract: {', '.join(issues)}"
                )
            if decision == "improves_bound":
                invalid = [issue for issue in issues if issue != "statement_mismatch"]
                quantitative_need = any(
                    value.strip()
                    for value in vars(obligation.quantitative_requirements).values()
                )
                if invalid or not quantitative_need:
                    raise ResearchStoreError(
                        "bound improvement requires a relevant quantitative requirement and compatible domain, hypotheses, quantifiers, and recorded costs"
                    )
            if decision == "eliminates_route" and status != "refuted":
                raise ResearchStoreError(
                    "route elimination requires a currently refuted supplier"
                )
            contribution_id = _id("contribution")
            record = {
                "contribution_id": contribution_id,
                "claim_id": parent_id,
                "revision": expected_revision,
                "obligation_id": obligation_id,
                "supplier_id": supplier["claim_id"],
                "supplier_revision": expected_supplier_revision,
                "supplier_state_token": token,
                "reviewer": reviewer,
                "decision": decision,
                "costs_acceptable": costs_acceptable,
                "rationale": rationale,
                "compatibility_issues": issues,
                "supersedes_contribution_ids": supersedes,
                "created_at": _now(),
            }
            self._insert_record(
                "contributions", contribution_id, parent_id, expected_revision, record
            )
            return record

    def _assessment(
        self, claim_id: str, cache: dict[str, dict[str, Any]] | None = None
    ) -> dict[str, Any]:
        if cache is None:
            cache = {}
        if claim_id in cache:
            return cache[claim_id]
        pending = [(claim_id, False)]
        visiting: set[str] = set()
        while pending:
            current_id, ready = pending.pop()
            if current_id in cache:
                continue
            if ready:
                self._assess_ready_claim(current_id, cache)
                visiting.remove(current_id)
                continue
            if current_id in visiting:
                raise ResearchStoreError("claim dependency cycle in ledger")
            visiting.add(current_id)
            current = self._claim(current_id)
            pending.append((current_id, True))
            pending.extend(
                (item["supplier_id"], False)
                for item in current["spec"]["dependencies"]
                if item["supplier_id"] not in cache
            )
        return cache[claim_id]

    def _assess_ready_claim(
        self, claim_id: str, cache: dict[str, dict[str, Any]]
    ) -> dict[str, Any]:
        """Assess a node after all suppliers have been assessed in this snapshot."""
        claim = self._claim(claim_id)
        local_status, verification, local_token = self._verification(
            claim_id, claim["revision"]
        )
        # Automatic dependency invalidation is not an explicit reconsideration
        # of this claim's counterexamples. Keep those reviews visible as a
        # scheduling hold, without treating stale evidence as a current verdict.
        explicit_revision = self._connection.execute(
            "SELECT MAX(revision) FROM revisions WHERE claim_id = ? "
            "AND revision <= ? AND cause IN ('created', 'revised')",
            (claim_id, claim["revision"]),
        ).fetchone()[0]
        historical_reviews = [
            json.loads(row[0])
            for row in self._connection.execute(
                "SELECT record FROM reviews WHERE claim_id = ? "
                "AND revision >= ? AND revision < ? ORDER BY rowid",
                (claim_id, explicit_revision, claim["revision"]),
            )
        ]
        historical_refutations = [
            record
            for record in _active_records(
                historical_reviews, "review_id", "supersedes_review_ids"
            )
            if record["verdict"] == "refuted"
        ]
        active_review_ids = set(verification["active_review_ids"])
        requires_target_revision = bool(historical_refutations) or any(
            review["verdict"] == "refuted" and review["review_id"] in active_review_ids
            for review in verification["independent_reviews"]
        )
        records = self._records("contributions", claim_id, claim["revision"])
        active_contributions: dict[str, list[dict[str, Any]]] = {}
        for item in _active_records(
            records, "contribution_id", "supersedes_contribution_ids"
        ):
            active_contributions.setdefault(item["obligation_id"], []).append(item)
        contributions = []
        remaining = []
        supplier_tokens = []
        spec = ClaimSpec.from_dict(claim["spec"])
        for obligation, obligation_dict in zip(
            spec.dependencies, claim["spec"]["dependencies"]
        ):
            supplier = self._claim(obligation.supplier_id)
            supplier_assessment = cache[supplier["claim_id"]]
            supplier_status = supplier_assessment["mathematical_status"]
            token = supplier_assessment["assessment_token"]
            supplier_tokens.append(token)
            issues = compatibility_issues(
                ClaimSpec.from_dict(supplier["spec"]), obligation
            )
            candidates = active_contributions.get(obligation.obligation_id, [])
            current = [
                item
                for item in candidates
                if item["supplier_revision"] == supplier["revision"]
                and item["supplier_state_token"] == token
            ]
            conflicted = (
                len({(item["decision"], item["costs_acceptable"]) for item in current})
                > 1
            )
            record = candidates[-1] if candidates else None
            entry = (
                dict(record)
                if record
                else {
                    "obligation_id": obligation.obligation_id,
                    "supplier_id": supplier["claim_id"],
                    "supplier_revision": supplier["revision"],
                    "decision": "unresolved",
                }
            )
            if current:
                # This is consensus, not one reviewer's newest assertion. The
                # IDs below link to every original rationale in the history.
                entry = {
                    "obligation_id": obligation.obligation_id,
                    "supplier_id": supplier["claim_id"],
                    "supplier_revision": supplier["revision"],
                    "supplier_state_token": token,
                    "decision": "unresolved" if conflicted else current[0]["decision"],
                    "costs_acceptable": not conflicted
                    and current[0]["costs_acceptable"],
                }
            entry["assessment_ids"] = [item["contribution_id"] for item in current]
            entry["conflicted"] = conflicted
            active = bool(current)
            if entry["decision"] in {"closes", "improves_bound"}:
                active = (
                    active
                    and supplier_status == "supported"
                    and bool(entry.get("costs_acceptable"))
                )
            if entry["decision"] == "closes":
                active = active and not issues
            if entry["decision"] == "improves_bound":
                active = active and not any(
                    issue != "statement_mismatch" for issue in issues
                )
                active = active and any(
                    value.strip()
                    for value in vars(obligation.quantitative_requirements).values()
                )
            if entry["decision"] == "eliminates_route":
                active = active and supplier_status == "refuted"
            entry.update(
                {
                    "active": active,
                    "supplier_status": supplier_status,
                    "compatibility_issues": issues,
                }
            )
            contributions.append(entry)
            if not (active and entry["decision"] == "closes"):
                remaining.append(obligation_dict)
        reasons = []
        if local_status == "supported" and remaining:
            reasons.append("required_obligations_remain_open")
        if historical_refutations:
            reasons.append("prior_refutation_requires_explicit_revision")
        status = (
            "unresolved" if local_status == "supported" and reasons else local_status
        )
        result = {
            "claim_id": claim_id,
            "revision": claim["revision"],
            "mathematical_status": status,
            "local_mathematical_status": local_status,
            "status_reasons": reasons,
            "requires_target_revision": requires_target_revision,
            "historical_refutations": historical_refutations,
            "verification": verification,
            "contributions": contributions,
            "remaining_obligations": remaining,
        }
        result["assessment_token"] = hashlib.sha256(
            json_text(
                {
                    "revision": claim["revision"],
                    "local_token": local_token,
                    "supplier_tokens": supplier_tokens,
                    "contributions": contributions,
                    "historical_refutations": historical_refutations,
                }
            ).encode()
        ).hexdigest()
        cache[claim_id] = result
        return result

    def assessment(self, claim_id: str) -> dict[str, Any]:
        with self._transaction():
            result = self._assessment(claim_id, self._snapshot_assessment_cache)
            # Cached internals cannot be exposed for callers to mutate while
            # composing multiple public reads in the same snapshot.
            return (
                deepcopy(result)
                if self._snapshot_assessment_cache is not None
                else result
            )

    def _history_state(self, claim_id: str) -> dict[str, Any]:
        self._claim(claim_id)
        revisions = [
            {
                "claim_id": row["claim_id"],
                "revision": row["revision"],
                "spec": json.loads(row["spec"]),
                "created_at": row["created_at"],
                "cause": row["cause"],
            }
            for row in self._connection.execute(
                "SELECT * FROM revisions WHERE claim_id = ? ORDER BY revision",
                (claim_id,),
            )
        ]
        result = {"claim_id": claim_id, "revisions": revisions}
        result.update(
            {
                table: self._records(table, claim_id)
                for table in ("evidence", "reviews", "contributions", "operations")
            }
        )
        assignments = [
            item
            for item in self._assignments()
            if any(
                context["claim_id"] == claim_id for context in item["context_revisions"]
            )
        ]
        # Assignment completion changes the operational history presented to a
        # worker even when mathematical records and claim revisions do not.
        # Hash the same nonrecursive projection included in new work packets.
        token_state = {
            **result,
            "assignments": [assignment_context_record(item) for item in assignments],
        }
        result["state_token"] = hashlib.sha256(
            json_text(token_state).encode()
        ).hexdigest()
        result["assignments"] = assignments
        return result

    def _history(self, claim_id: str) -> dict[str, Any]:
        result = self._history_state(claim_id)
        result["events"] = [
            {
                "sequence": row["sequence"],
                "claim_id": row["claim_id"],
                "revision": row["revision"],
                "kind": row["kind"],
                "record": json.loads(row["record"]),
            }
            for row in self._connection.execute(
                "SELECT * FROM events WHERE claim_id = ? ORDER BY sequence", (claim_id,)
            )
        ]
        return result

    def history(self, claim_id: str) -> dict[str, Any]:
        with self._transaction():
            return self._history(claim_id)

    def export(self) -> dict[str, Any]:
        with self._transaction():
            claims = self._all_claims()
            assessment_cache: dict[str, dict[str, Any]] = {}
            return {
                "schema_version": SCHEMA_VERSION,
                "claims": [
                    {
                        **claim,
                        "assessment": self._assessment(
                            claim["claim_id"], assessment_cache
                        ),
                    }
                    for claim in claims
                ],
                "histories": {
                    claim["claim_id"]: self._history(claim["claim_id"])
                    for claim in claims
                },
                "artifacts": [
                    json.loads(row[0])
                    for row in self._connection.execute(
                        "SELECT metadata FROM artifacts ORDER BY artifact_id"
                    )
                ],
                "assignments": self._assignments(),
                "events": [
                    {
                        "sequence": row["sequence"],
                        "claim_id": row["claim_id"],
                        "revision": row["revision"],
                        "kind": row["kind"],
                        "record": json.loads(row["record"]),
                    }
                    for row in self._connection.execute(
                        "SELECT * FROM events ORDER BY sequence"
                    )
                ],
            }

    def _assignments(self) -> list[dict[str, Any]]:
        return [
            json.loads(row[0])
            for row in self._connection.execute(
                "SELECT record FROM assignments ORDER BY rowid"
            )
        ]

    def save_assignment(self, packet: dict[str, Any]) -> dict[str, Any]:
        packet = _object(packet, "assignment packet", max_depth=128)
        # Compact metadata is embedded into future packets. Its caller-supplied
        # fields need the external bound, leaving room for those new envelopes.
        validate_json_structure(assignment_context_record(packet))
        assignment_id = identifier(packet.get("assignment_id"), "assignment_id")
        round_id = identifier(packet.get("round_id"), "round_id")
        question = text(packet.get("question"), "question")
        # Canonical paths prevent alternate spellings and current symlink
        # aliases from defeating output ownership. No output file is written.
        owned_output = assignment_output_path(packet.get("owned_output"))
        context = packet.get("context_revisions")
        if not isinstance(context, list) or not context:
            raise ResearchStoreError(
                "assignment requires a nonempty context_revisions array"
            )
        seen: set[str] = set()
        for item in context:
            if not isinstance(item, dict) or set(item) != {"claim_id", "revision"}:
                raise ResearchStoreError(
                    "context revisions require exactly claim_id and revision"
                )
            identifier(item["claim_id"], "context claim_id")
            positive_int(item["revision"], "context revision")
            if item["claim_id"] in seen:
                raise ResearchStoreError("duplicate context claim")
            seen.add(item["claim_id"])
        if any(
            key in packet
            for key in ("status", "outcome", "completion_details", "finished_at")
        ):
            raise ResearchStoreError("new assignment cannot contain completion fields")
        with self._transaction(write=True):
            for item in context:
                self._fenced_claim(item["claim_id"], item["revision"])
            # Revision numbers fence statement changes. These additional tokens
            # fence evidence and reviews arriving under the same statement.
            assessment_cache: dict[str, dict[str, Any]] = {}
            for field, key, embedded_context in (
                ("context_state_tokens", "state_token", "history_context"),
                ("context_assessment_tokens", "assessment_token", "dependency_context"),
            ):
                if field not in packet:
                    if embedded_context in packet:
                        raise ResearchStoreError(
                            f"{field} is required for a complete research packet"
                        )
                    continue
                tokens = packet[field]
                if not isinstance(tokens, list) or not tokens:
                    raise ResearchStoreError(f"{field} must be a nonempty array")
                token_ids: set[str] = set()
                for item in tokens:
                    if not isinstance(item, dict) or set(item) != {"claim_id", key}:
                        raise ResearchStoreError(
                            f"{field} entries require claim_id and {key}"
                        )
                    subject_id = identifier(item["claim_id"], "token claim_id")
                    if subject_id in token_ids or subject_id not in seen:
                        raise ResearchStoreError(
                            f"duplicate or unfenced claim in {field}"
                        )
                    token_ids.add(subject_id)
                    current = (
                        self._history_state(subject_id)
                        if key == "state_token"
                        else self._assessment(subject_id, assessment_cache)
                    )
                    if item[key] != current[key]:
                        raise RevisionConflict(
                            f"stale research context for {subject_id}: {key} changed"
                        )
                if key == "state_token" and token_ids != seen:
                    raise ResearchStoreError(
                        "context_state_tokens must cover every context revision"
                    )
                if key == "assessment_token" and "dependency_context" in packet:
                    try:
                        assessed_ids = {
                            node["claim"]["claim_id"]
                            for node in packet["dependency_context"]
                        }
                    except (KeyError, TypeError) as exc:
                        raise ResearchStoreError("invalid dependency_context") from exc
                    if token_ids != assessed_ids:
                        raise ResearchStoreError(
                            "context_assessment_tokens must cover the dependency context"
                        )
            if packet.get("work_kind") == "independent_review":
                subject_id = identifier(packet.get("claim_id"), "claim_id")
                worker = identifier(packet.get("worker"), "worker")
                if subject_id not in seen:
                    raise ResearchStoreError(
                        "review subject must be included in assignment context"
                    )
                authors = {self._claim(subject_id)["spec"]["author"]}
                authors.update(
                    item["author"] for item in self._records("evidence", subject_id)
                )
                if worker in authors:
                    raise ResearchStoreError(
                        "independent review worker authored the claim or its evidence"
                    )
            record = {
                **packet,
                "owned_output": owned_output,
                "status": "pending",
                "created_at": _now(),
            }
            try:
                self._connection.execute(
                    "INSERT INTO assignments VALUES (?, ?, ?, ?, ?, ?)",
                    (
                        assignment_id,
                        owned_output,
                        round_id,
                        question,
                        "pending",
                        json_text(record),
                    ),
                )
            except sqlite3.IntegrityError as exc:
                raise ResearchStoreError(
                    "duplicate assignment, round/question, or unfinished output ownership"
                ) from exc
            self._event(None, None, "assignment_saved", record)
            return record

    def list_assignments(self) -> list[dict[str, Any]]:
        with self._transaction():
            return self._assignments()

    def finish_assignment(
        self, assignment_id: str, *, outcome: str, details: dict[str, Any]
    ) -> dict[str, Any]:
        identifier(assignment_id, "assignment_id")
        if outcome not in OPERATIONAL_OUTCOMES:
            raise ResearchStoreError(f"unknown operational outcome: {outcome}")
        details = _object(details, "details")
        with self._transaction(write=True):
            row = self._connection.execute(
                "SELECT status, record FROM assignments WHERE assignment_id = ?",
                (assignment_id,),
            ).fetchone()
            if row is None:
                raise ResearchStoreError(f"unknown assignment: {assignment_id}")
            if row["status"] != "pending":
                raise ResearchStoreError("assignment is already finished")
            record = {
                **json.loads(row["record"]),
                "status": "finished",
                "outcome": outcome,
                "completion_details": details,
                "finished_at": _now(),
            }
            self._connection.execute(
                "UPDATE assignments SET status = ?, record = ? WHERE assignment_id = ?",
                ("finished", json_text(record), assignment_id),
            )
            self._event(None, None, "assignment_finished", record)
            return record
