"""Lightweight shared identities for durable falsification cursors."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Mapping


GRAPH_PLAN_CURSOR_SCHEMA = "mini_graph_search_v2"

RIGHT_PI_LEGACY_PLAN_CURSOR_SCHEMA = "mini_right_pi_search_v1"
RIGHT_PI_OLDER_PLAN_CURSOR_SCHEMA = "mini_right_pi_search_v2"
RIGHT_PI_PREVIOUS_PLAN_CURSOR_SCHEMA = "mini_right_pi_search_v3"
RIGHT_PI_RECENT_PLAN_CURSOR_SCHEMA = "mini_right_pi_search_v4"
RIGHT_PI_PLAN_CURSOR_SCHEMA = "mini_right_pi_search_v5"
RIGHT_PI_RECIPE_REPAIR_SCHEMA = "mini_right_pi_recipe_repair_v1"
RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS = 2
RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES = 30_000

# Cursor caches are indexed canonically only as a bounded shortlist.  The
# actual resume identity lives in the exact-statement target entries inside
# that shortlist; a lossy canonical key is never itself proof-search state.
FALSIFICATION_CURSOR_TARGET_SCHEMA = "mini_falsification_target_v2"


def _cursor_content_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def counterexample_candidate_record_is_valid(data: Any) -> bool:
    """Validate the typed envelope consumed by candidate rehydration."""

    if not isinstance(data, Mapping):
        return False
    candidate = dict(data)
    claimed_hash = candidate.pop("candidate_hash", None)
    witness_terms = candidate.get("witness_terms")
    metadata = candidate.get("metadata")
    return bool(
        isinstance(claimed_hash, str)
        and re.fullmatch(r"[0-9a-f]{64}", claimed_hash)
        and isinstance(candidate.get("engine"), str)
        and bool(str(candidate.get("engine") or "").strip())
        and isinstance(witness_terms, (list, tuple))
        and all(isinstance(item, str) for item in witness_terms)
        and isinstance(candidate.get("concrete_statement"), str)
        and isinstance(candidate.get("explanation"), str)
        and isinstance(candidate.get("complete_domain"), bool)
        and isinstance(metadata, Mapping)
        and _cursor_content_hash(candidate) == claimed_hash
    )


def right_pi_candidate_record_is_persistable(data: Any) -> bool:
    """Check the one shared size/integrity contract for preserved candidates."""

    if not isinstance(data, Mapping):
        return False
    try:
        encoded = json.dumps(
            data,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    except (TypeError, ValueError, UnicodeError):
        return False
    return bool(
        len(encoded) <= RIGHT_PI_PRESERVED_CANDIDATE_MAX_BYTES
        and counterexample_candidate_record_is_valid(data)
    )


def right_pi_recipe_repair_key(
    *,
    statement: str,
    environment_hash: str,
    plan_hash: str,
    candidate_index: int,
    candidate_hash: str,
) -> str:
    """Bind recipe repair to exactly one candidate in one verifier world."""

    return _cursor_content_hash(
        {
            "statement": str(statement or "").strip(),
            "environment_hash": str(environment_hash or "").strip(),
            "plan_hash": str(plan_hash or "").strip(),
            "candidate_index": int(candidate_index),
            "candidate_hash": str(candidate_hash or "").strip(),
        }
    )


def make_right_pi_recipe_repair_disposition(
    *,
    statement: str,
    environment_hash: str,
    plan_hash: str,
    candidate_index: int,
    candidate_record: Mapping[str, Any],
    attempts: int,
    reason: str,
) -> dict[str, Any]:
    """Create the bounded, content-addressed replay-repair disposition."""

    candidate = dict(candidate_record)
    candidate_hash = str(candidate.get("candidate_hash") or "").strip()
    bounded_attempts = min(
        RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS,
        max(1, int(attempts)),
    )
    record: dict[str, Any] = {
        "schema": RIGHT_PI_RECIPE_REPAIR_SCHEMA,
        "statement_hash": _cursor_content_hash(str(statement or "").strip()),
        "environment_hash": str(environment_hash or "").strip(),
        "plan_hash": str(plan_hash or "").strip(),
        "candidate_index": int(candidate_index),
        "candidate_hash": candidate_hash,
        "repair_key": right_pi_recipe_repair_key(
            statement=statement,
            environment_hash=environment_hash,
            plan_hash=plan_hash,
            candidate_index=candidate_index,
            candidate_hash=candidate_hash,
        ),
        "attempts": bounded_attempts,
        "max_attempts": RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS,
        "status": (
            "exhausted"
            if bounded_attempts >= RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS
            else "pending"
        ),
        # Preserve the Lean-checked concrete counterexample while quarantining
        # its broken generated full-negation recipe.  Candidate construction is
        # already bounded by the right-Pi engine/certificate boundary.
        "candidate": candidate,
        "reason": str(reason or "")[:500],
    }
    record["disposition_hash"] = _cursor_content_hash(record)
    return record


def make_right_pi_oversized_recipe_repair_disposition(
    *,
    statement: str,
    environment_hash: str,
    plan_hash: str,
    candidate_index: int,
    candidate_hash: str,
    attempts: int,
    reason: str,
) -> dict[str, Any]:
    """Record bounded repair attempts without embedding an oversized candidate."""

    bounded_attempts = min(
        RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS,
        max(1, int(attempts)),
    )
    record: dict[str, Any] = {
        "schema": RIGHT_PI_RECIPE_REPAIR_SCHEMA,
        "statement_hash": _cursor_content_hash(str(statement or "").strip()),
        "environment_hash": str(environment_hash or "").strip(),
        "plan_hash": str(plan_hash or "").strip(),
        "candidate_index": int(candidate_index),
        "candidate_hash": str(candidate_hash or "").strip(),
        "repair_key": right_pi_recipe_repair_key(
            statement=statement,
            environment_hash=environment_hash,
            plan_hash=plan_hash,
            candidate_index=candidate_index,
            candidate_hash=candidate_hash,
        ),
        "attempts": bounded_attempts,
        "max_attempts": RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS,
        "status": "pending",
        "candidate_oversized": True,
        "reason": str(reason or "")[:500],
    }
    record["disposition_hash"] = _cursor_content_hash(record)
    return record


def right_pi_recipe_repair_disposition_is_valid(
    data: Any,
    *,
    statement: str = "",
    environment_hash: str = "",
    cursor: Mapping[str, Any] | None = None,
) -> bool:
    """Validate a durable recipe disposition without granting authority."""

    if not isinstance(data, Mapping):
        return False
    record = dict(data)
    claimed_disposition_hash = str(record.pop("disposition_hash", "") or "")
    candidate = record.get("candidate")
    candidate_oversized = record.get("candidate_oversized") is True
    if not isinstance(candidate, Mapping) and not (
        candidate is None and candidate_oversized
    ):
        return False
    claimed_candidate_hash = (
        str(candidate.get("candidate_hash") or "")
        if isinstance(candidate, Mapping)
        else str(record.get("candidate_hash") or "")
    )
    attempts = record.get("attempts")
    candidate_index = record.get("candidate_index")
    expected_statement = str(statement or "").strip()
    expected_environment = str(environment_hash or "").strip()
    plan_hash = str(record.get("plan_hash") or "").strip()
    candidate_hash = str(record.get("candidate_hash") or "").strip()
    if not (
        record.get("schema") == RIGHT_PI_RECIPE_REPAIR_SCHEMA
        and re.fullmatch(r"[0-9a-f]{64}", claimed_disposition_hash)
        and _cursor_content_hash(record) == claimed_disposition_hash
        and (
            right_pi_candidate_record_is_persistable(candidate)
            if isinstance(candidate, Mapping)
            else candidate_oversized
        )
        and candidate_hash == claimed_candidate_hash
        and (
            str(candidate.get("engine") or "") == "function"
            if isinstance(candidate, Mapping)
            else candidate is None and candidate_oversized
        )
        and re.fullmatch(r"[0-9a-f]{64}", str(record.get("statement_hash") or ""))
        and re.fullmatch(r"[0-9a-f]{64}", str(record.get("environment_hash") or ""))
        and re.fullmatch(r"[0-9a-f]{64}", plan_hash)
        and re.fullmatch(r"[0-9a-f]{64}", candidate_hash)
        and re.fullmatch(r"[0-9a-f]{64}", str(record.get("repair_key") or ""))
        and isinstance(candidate_index, int)
        and not isinstance(candidate_index, bool)
        and candidate_index >= 0
        and isinstance(attempts, int)
        and not isinstance(attempts, bool)
        and 1 <= attempts <= RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS
        and record.get("max_attempts") == RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS
        and record.get("status")
        == (
            "pending"
            if candidate_oversized
            else (
                "exhausted"
                if attempts == RIGHT_PI_RECIPE_REPAIR_MAX_ATTEMPTS
                else "pending"
            )
        )
    ):
        return False
    if expected_statement and record.get("statement_hash") != _cursor_content_hash(
        expected_statement
    ):
        return False
    if expected_environment and record.get("environment_hash") != expected_environment:
        return False
    if record.get("repair_key") != right_pi_recipe_repair_key(
        statement=expected_statement if expected_statement else "",
        environment_hash=expected_environment or str(record["environment_hash"]),
        plan_hash=plan_hash,
        candidate_index=candidate_index,
        candidate_hash=candidate_hash,
    ):
        # Without the statement bytes the statement hash alone cannot safely
        # reconstruct the key.  Durable cursor validation in ProofDossier
        # supplies only cursor structure, so defer that exact-key comparison
        # until lookup/service time rather than guessing source bytes.
        if expected_statement:
            return False
    if cursor is not None:
        domain_size = cursor.get("domain_size")
        if not (
            cursor.get("cursor_schema") == RIGHT_PI_PLAN_CURSOR_SCHEMA
            and cursor.get("plan_hash") == plan_hash
            and isinstance(domain_size, int)
            and not isinstance(domain_size, bool)
            and 0 <= candidate_index < domain_size
            and cursor.get("next_index") == candidate_index
        ):
            return False
    return True
