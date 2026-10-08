"""Immutable local receipt versions for bounded scheduler cutpoints.

Durable session checkpoints carry the receipts themselves. Diagnostic snapshots
carry a cursor into this process-local history; a cursor alone never grants
permission to resume execution in another process.
"""

from __future__ import annotations

import copy
import uuid
from typing import Any


class ExecutionReceiptHistory:
    """Append-only version graph; rollback can branch without invalidating a cursor."""

    def __init__(self, receipts: dict[str, dict[str, Any]]) -> None:
        self.identity = uuid.uuid4().hex
        self.base = copy.deepcopy(receipts)
        self.versions: list[tuple[int, str, str, Any]] = []

    def append(self, parent: int, key: str, field: str, value: Any) -> int:
        self.versions.append((parent, key, field, copy.deepcopy(value)))
        return len(self.versions)

    def restore(self, cursor: dict[str, Any]) -> dict[str, dict[str, Any]]:
        validate_execution_cursor(cursor)
        if cursor["history_id"] != self.identity or cursor["version"] > len(
            self.versions
        ):
            raise ValueError("execution receipt cursor has no local history")
        changes = []
        version = cursor["version"]
        while version:
            previous, key, field, value = self.versions[version - 1]
            changes.append((key, field, value))
            version = previous
        receipts = copy.deepcopy(self.base)
        for key, field, value in reversed(changes):
            if field == "receipt":
                receipts[key] = copy.deepcopy(value)
            elif field == "semantic_attempt_completed":
                receipts[key][field] = value
            elif field == "detached_tail_pending":
                receipts[key]["details"][field] = value
            else:
                raise ValueError("invalid local execution receipt change")
        if (
            len(receipts) != cursor["receipt_count"]
            or sum(int(r["semantic_attempt_completed"]) for r in receipts.values())
            != cursor["completed_count"]
            or sum(
                r["details"].get("detached_tail_pending") is True
                for r in receipts.values()
            )
            != cursor["pending_count"]
        ):
            raise ValueError("execution receipt cursor does not match local history")
        return receipts


def validate_execution_cursor(cursor: Any) -> None:
    if (
        type(cursor) is not dict
        or set(cursor)
        != {
            "schema_version",
            "history_id",
            "version",
            "receipt_count",
            "completed_count",
            "pending_count",
        }
        or type(cursor["schema_version"]) is not int
        or cursor["schema_version"] != 1
        or type(cursor["history_id"]) is not str
        or len(cursor["history_id"]) != 32
        or any(c not in "0123456789abcdef" for c in cursor["history_id"])
        or any(
            type(cursor[key]) is not int or cursor[key] < 0
            for key in ("version", "receipt_count", "completed_count", "pending_count")
        )
        or cursor["completed_count"] > cursor["receipt_count"]
        or cursor["pending_count"] > cursor["receipt_count"]
    ):
        raise ValueError("invalid execution receipt cursor")
