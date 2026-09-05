"""Indexed, local-machine project ledger with fenced worker leases.

SQLite owns task state; immutable blobs own potentially large source/output
bytes. Each process opens its own store, and no model or Lean work runs inside
a database transaction. A worker may publish a result only while its current
task generation and lease token still match the ledger.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import sqlite3
import tempfile
import time
import uuid
from collections import deque
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from urllib.parse import quote


STATES = ("ready", "pending", "running", "verified", "failed", "blocked")


class LeaseLostError(RuntimeError):
    """The attempt expired, finished, or was superseded by another generation."""


@dataclass(frozen=True)
class Task:
    id: str
    kind: str
    description: str
    payload: dict[str, Any]
    state: str
    generation: int
    attempts: int
    result: dict[str, Any] | None
    error: str
    priority: int
    session: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class Claim:
    task: Task
    token: str
    generation: int
    lease_until: float


_EVENT_SCHEMA = """
CREATE TABLE events (
    id INTEGER PRIMARY KEY,
    task_id TEXT NOT NULL REFERENCES tasks(id),
    generation INTEGER NOT NULL,
    kind TEXT NOT NULL,
    payload TEXT NOT NULL,
    created REAL NOT NULL
);
CREATE INDEX events_task ON events(task_id,id);
"""

_SCHEMA = (
    """
CREATE TABLE metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE tasks (
    id TEXT PRIMARY KEY,
    kind TEXT NOT NULL,
    description TEXT NOT NULL,
    payload TEXT NOT NULL,
    state TEXT NOT NULL CHECK (state IN ('ready','pending','running','verified','failed','blocked')),
    generation INTEGER NOT NULL DEFAULT 0,
    attempts INTEGER NOT NULL DEFAULT 0,
    result TEXT,
    session TEXT NOT NULL DEFAULT '{}',
    error TEXT NOT NULL DEFAULT '',
    priority INTEGER NOT NULL DEFAULT 0,
    remaining_deps INTEGER NOT NULL DEFAULT 0 CHECK (remaining_deps >= 0),
    lease_token TEXT,
    lease_owner TEXT,
    lease_until REAL
);
CREATE TABLE dependencies (
    task_id TEXT NOT NULL REFERENCES tasks(id),
    prerequisite_id TEXT NOT NULL REFERENCES tasks(id),
    PRIMARY KEY (task_id, prerequisite_id),
    CHECK (task_id <> prerequisite_id)
);
CREATE INDEX dependencies_reverse ON dependencies(prerequisite_id, task_id);
CREATE INDEX tasks_ready ON tasks(state, priority DESC, id);
CREATE INDEX tasks_leases ON tasks(state, lease_until);
CREATE TABLE attempts (
    token TEXT PRIMARY KEY,
    task_id TEXT NOT NULL REFERENCES tasks(id),
    generation INTEGER NOT NULL,
    owner TEXT NOT NULL,
    started REAL NOT NULL,
    finished REAL,
    outcome TEXT,
    result TEXT,
    error TEXT NOT NULL DEFAULT ''
);
CREATE INDEX attempts_task ON attempts(task_id, started);
"""
    + _EVENT_SCHEMA
    + "PRAGMA user_version = 2;\n"
)


def _json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, allow_nan=False, separators=(",", ":"))


def _clock(now: float | None) -> float:
    value = time.time() if now is None else float(now)
    if not math.isfinite(value):
        raise ValueError("time must be finite")
    return value


def _lease_end(now: float, lease_s: float) -> float:
    if not math.isfinite(lease_s) or lease_s <= 0 or not math.isfinite(now + lease_s):
        raise ValueError("lease_s must be finite and positive")
    return now + lease_s


def _task(row: sqlite3.Row) -> Task:
    return Task(
        id=row["id"],
        kind=row["kind"],
        description=row["description"],
        payload=json.loads(row["payload"]),
        state=row["state"],
        generation=row["generation"],
        attempts=row["attempts"],
        result=json.loads(row["result"]) if row["result"] is not None else None,
        error=row["error"],
        priority=row["priority"],
        session=json.loads(row["session"]),
    )


class ProjectStore:
    """Durable DAG scheduling on a local SQLite database.

    Connections are not shared between threads/processes. SQLite WAL permits
    concurrent readers and short serialized writers on the same local host.
    """

    def __init__(
        self,
        directory: Path,
        *,
        create: bool = False,
        metadata: Mapping[str, Any] | None = None,
    ) -> None:
        encoded_metadata = (
            [(key, _json(value)) for key, value in (metadata or {}).items()]
            if create
            else []
        )
        self.directory = Path(directory).expanduser().resolve()
        self.path = self.directory / "project.sqlite3"
        if create:
            self.directory.mkdir(parents=True, exist_ok=True)
            descriptor = os.open(self.path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
            os.close(descriptor)
        elif not self.path.is_file():
            raise FileNotFoundError(self.path)
        self._connection = sqlite3.connect(
            "file:" + quote(str(self.path)) + "?mode=rw",
            uri=True,
            timeout=30,
            isolation_level=None,
        )
        self._connection.row_factory = sqlite3.Row
        try:
            self._connection.execute("PRAGMA busy_timeout = 30000")
            self._connection.execute("PRAGMA foreign_keys = ON")
            self._connection.execute("PRAGMA synchronous = FULL")
            if create:
                self._connection.execute("PRAGMA journal_mode = WAL")
                self._connection.executescript("BEGIN IMMEDIATE;\n" + _SCHEMA)
                self._connection.executemany(
                    "INSERT INTO metadata(key,value) VALUES (?,?)",
                    encoded_metadata,
                )
                self._connection.execute("COMMIT")
            else:
                version = self._connection.execute("PRAGMA user_version").fetchone()[0]
                if version == 1:
                    with self._transaction():
                        # Recheck under the writer lock if another opener migrated.
                        if (
                            self._connection.execute("PRAGMA user_version").fetchone()[
                                0
                            ]
                            == 1
                        ):
                            self._connection.execute(
                                "ALTER TABLE tasks ADD COLUMN session TEXT NOT NULL DEFAULT '{}'"
                            )
                            for command in _EVENT_SCHEMA.split(";"):
                                if command.strip():
                                    self._connection.execute(command)
                            self._connection.execute("PRAGMA user_version = 2")
                elif version != 2:
                    raise ValueError("unsupported or incomplete project ledger schema")
            self._connection.execute(
                "CREATE INDEX IF NOT EXISTS tasks_state_id ON tasks(state,id)"
            )
            self._connection.execute("CREATE TEMP TABLE affected (id TEXT PRIMARY KEY)")
        except BaseException:
            self._connection.close()
            raise

    def __enter__(self) -> ProjectStore:
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def close(self) -> None:
        """Close this connection without altering outstanding durable leases."""
        self._connection.close()

    @contextmanager
    def _transaction(self) -> Iterator[None]:
        self._connection.execute("BEGIN IMMEDIATE")
        try:
            yield
            self._connection.execute("COMMIT")
        except BaseException:
            if self._connection.in_transaction:
                self._connection.execute("ROLLBACK")
            raise

    def get_metadata(self, key: str | None = None) -> Any:
        """Read one metadata value, or the small project metadata dictionary."""
        if key is None:
            return {
                row[0]: json.loads(row[1])
                for row in self._connection.execute("SELECT key,value FROM metadata")
            }
        row = self._connection.execute(
            "SELECT value FROM metadata WHERE key=?", (key,)
        ).fetchone()
        return json.loads(row[0]) if row else None

    def set_metadata(self, key: str, value: Any) -> None:
        """Atomically replace one small metadata value."""
        encoded = _json(value)
        with self._transaction():
            self._connection.execute(
                "INSERT INTO metadata(key,value) VALUES (?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, encoded),
            )

    def get_task(self, task_id: str) -> Task:
        """Read one task; unknown identifiers are errors."""
        row = self._connection.execute(
            "SELECT * FROM tasks WHERE id=?", (task_id,)
        ).fetchone()
        if row is None:
            raise KeyError(task_id)
        return _task(row)

    def dependency_count(self, task_id: str) -> int:
        """Count direct edges without materializing their contracts."""
        self.get_task(task_id)
        return self._connection.execute(
            "SELECT COUNT(*) FROM dependencies WHERE task_id=?", (task_id,)
        ).fetchone()[0]

    def is_prerequisite(self, task_id: str, prerequisite_id: str) -> bool:
        """Whether a prerequisite reaches this task, including the task itself.

        Follow indexed reverse edges only for actual blocking questions; normal
        campaign steps do not need to enumerate the root dependency DAG.
        """
        self.get_task(task_id)
        self.get_task(prerequisite_id)
        return (
            self._connection.execute(
                """WITH RECURSIVE dependents(id) AS (
                SELECT ? UNION
                SELECT d.task_id FROM dependencies d
                JOIN dependents p ON d.prerequisite_id=p.id
            ) SELECT 1 FROM dependents WHERE id=? LIMIT 1""",
                (prerequisite_id, task_id),
            ).fetchone()
            is not None
        )

    def dependencies(
        self, task_id: str, limit: int | None = None, after: str = ""
    ) -> list[Task]:
        """Return direct prerequisite contracts, in stable identifier order."""
        self.get_task(task_id)
        if limit is not None and (type(limit) is not int or limit < 1):
            raise ValueError("limit must be a positive integer or None")
        return [
            _task(row)
            for row in self._connection.execute(
                "SELECT t.* FROM dependencies d JOIN tasks t ON t.id=d.prerequisite_id WHERE d.task_id=? AND d.prerequisite_id>? ORDER BY d.prerequisite_id LIMIT ?",
                (task_id, after, -1 if limit is None else limit),
            )
        ]

    def list_tasks(
        self, state: str | None = None, limit: int = 50, after: str = ""
    ) -> list[Task]:
        """Page through tasks without reading or serializing the entire DAG."""
        if not isinstance(limit, int) or isinstance(limit, bool) or limit <= 0:
            raise ValueError("limit must be a positive integer")
        if state is not None and state not in STATES:
            raise ValueError("unknown task state")
        if state is None:
            rows = self._connection.execute(
                "SELECT * FROM tasks WHERE id>? ORDER BY id LIMIT ?", (after, limit)
            )
        else:
            rows = self._connection.execute(
                "SELECT * FROM tasks WHERE state=? AND id>? ORDER BY id LIMIT ?",
                (state, after, limit),
            )
        return [_task(row) for row in rows]

    def status(self) -> dict[str, int]:
        """Count each state; failed/blocked tasks still count as unfinished."""
        counts = dict.fromkeys(STATES, 0)
        counts.update(
            self._connection.execute(
                "SELECT state,COUNT(*) FROM tasks GROUP BY state"
            ).fetchall()
        )
        counts["total"] = sum(counts.values())
        counts["unfinished"] = counts["total"] - counts["verified"]
        return counts

    @staticmethod
    def _spec(value: Mapping[str, Any]) -> tuple[tuple[Any, ...], tuple[str, ...]]:
        for key in ("id", "kind", "description"):
            if not isinstance(value.get(key), str) or (
                key != "description" and not value[key].strip()
            ):
                raise ValueError(f"task requires a valid {key}")
        payload = value.get("payload", {})
        if not isinstance(payload, dict):
            raise ValueError("task payload must be an object")
        priority = value.get("priority", 0)
        if not isinstance(priority, int) or isinstance(priority, bool):
            raise ValueError("task priority must be an integer")
        dependencies = value.get("dependencies", [])
        if not isinstance(dependencies, (list, tuple)) or any(
            not isinstance(item, str) or not item.strip() for item in dependencies
        ):
            raise ValueError("dependencies must be a list of task identifiers")
        return (
            value["id"],
            value["kind"],
            value["description"],
            _json(payload),
            priority,
        ), tuple(dict.fromkeys(dependencies))

    def add_tasks(self, tasks: Sequence[Mapping[str, Any]]) -> list[Task]:
        """Add a batch atomically, allowing forward references inside the batch."""
        specs = [self._spec(value) for value in tasks]
        with self._transaction():
            self._add_specs(specs)
        return [self.get_task(row[0]) for row, _ in specs]

    def _add_specs(self, specs: list) -> None:
        identifiers = {row[0] for row, _ in specs}
        if len(identifiers) != len(specs):
            raise ValueError("duplicate task identifier")
        self._validate_batch_dag(specs, identifiers)
        try:
            self._connection.executemany(
                "INSERT INTO tasks(id,kind,description,payload,priority,state) VALUES (?,?,?,?,?,'pending')",
                (row for row, _ in specs),
            )
            self._connection.executemany(
                "INSERT INTO dependencies(task_id,prerequisite_id) VALUES (?,?)",
                (
                    (row[0], dependency)
                    for row, dependencies in specs
                    for dependency in dependencies
                ),
            )
        except sqlite3.IntegrityError as exc:
            raise ValueError(
                "duplicate task, missing prerequisite, or invalid dependency"
            ) from exc
        self._set_affected(identifiers)
        self._refresh_affected()

    @staticmethod
    def _validate_batch_dag(specs: list, identifiers: set[str]) -> None:
        # Existing tasks cannot point at these not-yet-created IDs, so cycles
        # introduced by insertion lie entirely in this batch. Kahn is O(V+E).
        counts: dict[str, int] = {}
        reverse: dict[str, list[str]] = {}
        for row, dependencies in specs:
            counts[row[0]] = sum(
                dependency in identifiers for dependency in dependencies
            )
            for dependency in dependencies:
                if dependency in identifiers:
                    reverse.setdefault(dependency, []).append(row[0])
        queue = deque(key for key, count in counts.items() if count == 0)
        visited = 0
        while queue:
            current = queue.popleft()
            visited += 1
            for dependent in reverse.get(current, ()):
                counts[dependent] -= 1
                if counts[dependent] == 0:
                    queue.append(dependent)
        if visited != len(identifiers):
            raise ValueError("task dependencies contain a cycle")

    def _set_affected(self, identifiers: Iterator[str] | set[str]) -> None:
        self._connection.execute("DELETE FROM affected")
        self._connection.executemany(
            "INSERT OR IGNORE INTO affected(id) VALUES (?)",
            ((item,) for item in identifiers),
        )

    def _descendants(self, task_id: str, *, include_self: bool = True) -> None:
        self._connection.execute("DELETE FROM affected")
        self._connection.execute(
            """WITH RECURSIVE descendants(id) AS (
                SELECT ? UNION SELECT d.task_id FROM dependencies d JOIN descendants s ON d.prerequisite_id=s.id
            ) INSERT INTO affected SELECT id FROM descendants""",
            (task_id,),
        )
        if not include_self:
            self._connection.execute("DELETE FROM affected WHERE id=?", (task_id,))

    def _refresh_affected(self) -> None:
        self._connection.execute("""
            UPDATE tasks SET remaining_deps=(
                SELECT COUNT(*) FROM dependencies d JOIN tasks p ON p.id=d.prerequisite_id
                WHERE d.task_id=tasks.id AND p.state<>'verified'
            ) WHERE id IN (SELECT id FROM affected)
        """)
        self._connection.execute("""
            UPDATE tasks SET state=CASE WHEN remaining_deps=0 THEN 'ready' ELSE 'pending' END
            WHERE id IN (SELECT id FROM affected) AND state IN ('ready','pending','blocked')
        """)
        self._connection.execute("""
            WITH RECURSIVE blocked(id) AS (
                SELECT d.task_id FROM affected a JOIN dependencies d ON d.task_id=a.id
                JOIN tasks p ON p.id=d.prerequisite_id WHERE p.state IN ('failed','blocked')
                UNION
                SELECT d.task_id FROM dependencies d JOIN blocked b ON d.prerequisite_id=b.id
                JOIN affected a ON a.id=d.task_id
            ) UPDATE tasks SET state='blocked'
            WHERE id IN (SELECT id FROM blocked) AND state IN ('pending','ready')
        """)

    def _reap(self, now: float) -> None:
        self._connection.execute("DELETE FROM affected")
        self._connection.execute(
            "INSERT INTO affected SELECT id FROM tasks WHERE state='running' AND lease_until<=?",
            (now,),
        )
        self._connection.execute(
            """
            UPDATE attempts SET finished=?,outcome='expired'
            WHERE token IN (SELECT lease_token FROM tasks WHERE id IN (SELECT id FROM affected)) AND finished IS NULL
        """,
            (now,),
        )
        self._connection.execute("""
            UPDATE tasks SET state='pending',lease_token=NULL,lease_owner=NULL,lease_until=NULL
            WHERE id IN (SELECT id FROM affected)
        """)
        self._refresh_affected()

    def claim(
        self,
        owner: str,
        lease_s: float = 300,
        now: float | None = None,
        kinds: Sequence[str] | None = None,
    ) -> Claim | None:
        """Recover expired leases and atomically reserve one ready task."""
        _lease_end(_clock(now), lease_s)
        if not isinstance(owner, str) or not owner.strip():
            raise ValueError("lease owner must be nonempty")
        with self._transaction():
            timestamp = _clock(now)
            self._reap(timestamp)
            if kinds is not None and not kinds:
                return None
            query = "SELECT * FROM tasks WHERE state='ready'"
            values: list[Any] = []
            if kinds is not None:
                query += " AND kind IN (" + ",".join("?" for _ in kinds) + ")"
                values.extend(kinds)
            row = self._connection.execute(
                query + " ORDER BY priority DESC,id LIMIT 1", values
            ).fetchone()
            if row is None:
                return None
            timestamp = _clock(now)
            until = _lease_end(timestamp, lease_s)
            token = uuid.uuid4().hex
            self._connection.execute(
                "UPDATE tasks SET state='running',attempts=attempts+1,lease_token=?,lease_owner=?,lease_until=? WHERE id=?",
                (token, owner, until, row["id"]),
            )
            self._connection.execute(
                "INSERT INTO attempts(token,task_id,generation,owner,started) VALUES (?,?,?,?,?)",
                (token, row["id"], row["generation"], owner, timestamp),
            )
            return Claim(self.get_task(row["id"]), token, row["generation"], until)

    def _assert_lease(self, claim: Claim, now: float) -> None:
        row = self._connection.execute(
            """SELECT 1 FROM tasks WHERE id=? AND generation=? AND lease_token=?
            AND state='running' AND lease_until>?""",
            (claim.task.id, claim.generation, claim.token, now),
        ).fetchone()
        if row is None:
            raise LeaseLostError(f"lease lost for task {claim.task.id}")

    def heartbeat(
        self, claim: Claim, lease_s: float, now: float | None = None
    ) -> Claim:
        """Extend only a currently valid lease; expired leases never revive."""
        _lease_end(_clock(now), lease_s)
        with self._transaction():
            timestamp = _clock(now)
            until = _lease_end(timestamp, lease_s)
            self._assert_lease(claim, timestamp)
            self._connection.execute(
                "UPDATE tasks SET lease_until=? WHERE id=?", (until, claim.task.id)
            )
            return Claim(
                self.get_task(claim.task.id), claim.token, claim.generation, until
            )

    def complete(
        self, claim: Claim, result: dict[str, Any], now: float | None = None
    ) -> Task:
        """Record caller-verified output and unlock its direct dependents."""
        if not isinstance(result, dict):
            raise ValueError("task result must be an object")
        encoded = _json(result)
        with self._transaction():
            timestamp = _clock(now)
            self._assert_lease(claim, timestamp)
            self._connection.execute(
                """
                UPDATE tasks SET state='verified',result=?,error='',lease_token=NULL,lease_owner=NULL,lease_until=NULL WHERE id=?
            """,
                (encoded, claim.task.id),
            )
            self._connection.execute(
                "UPDATE attempts SET outcome='verified',result=?,finished=? WHERE token=?",
                (encoded, timestamp, claim.token),
            )
            self._set_affected(
                row[0]
                for row in self._connection.execute(
                    "SELECT task_id FROM dependencies WHERE prerequisite_id=?",
                    (claim.task.id,),
                )
            )
            # This prerequisite crossed running -> verified exactly once under
            # its fenced lease. Update direct dependents in O(outdegree), not
            # by recounting every sibling prerequisite on each completion.
            self._connection.execute("""
                UPDATE tasks SET remaining_deps=remaining_deps-1,
                    state=CASE WHEN remaining_deps=1 AND state IN ('pending','blocked')
                               THEN 'ready' ELSE state END
                WHERE id IN (SELECT id FROM affected) AND remaining_deps>0
            """)
            return self.get_task(claim.task.id)

    def fail(
        self, claim: Claim, error: str, retry: bool = False, now: float | None = None
    ) -> Task:
        """Release a failed attempt; terminal failure blocks dependent work."""
        if not isinstance(error, str):
            raise ValueError("error must be a string")
        with self._transaction():
            timestamp = _clock(now)
            self._assert_lease(claim, timestamp)
            self._connection.execute(
                """
                UPDATE tasks SET state=?,error=?,lease_token=NULL,lease_owner=NULL,lease_until=NULL WHERE id=?
            """,
                ("pending" if retry else "failed", error, claim.task.id),
            )
            self._connection.execute(
                "UPDATE attempts SET outcome=?,error=?,finished=? WHERE token=?",
                ("retry" if retry else "failed", error, timestamp, claim.token),
            )
            self._descendants(claim.task.id)
            self._refresh_affected()
            return self.get_task(claim.task.id)

    def revise(
        self,
        task_id: str,
        payload: dict[str, Any] | None = None,
        dependencies: Sequence[str] | None = None,
        description: str | None = None,
        *,
        claim: Claim | None = None,
    ) -> Task:
        """Revise a contract and invalidate only it and its dependent closure."""
        if payload is not None and not isinstance(payload, dict):
            raise ValueError("payload must be an object")
        if description is not None and not isinstance(description, str):
            raise ValueError("description must be a string")
        encoded = _json(payload) if payload is not None else None
        with self._transaction():
            self.get_task(task_id)
            if claim is not None:
                if claim.task.id != task_id:
                    raise LeaseLostError("claim belongs to another task")
                self._assert_lease(claim, _clock(None))
            if dependencies is not None:
                self._replace_dependencies(task_id, dependencies)
            if encoded is not None:
                self._connection.execute(
                    "UPDATE tasks SET payload=? WHERE id=?", (encoded, task_id)
                )
            if description is not None:
                self._connection.execute(
                    "UPDATE tasks SET description=? WHERE id=?", (description, task_id)
                )
            self._invalidate(task_id, _clock(None))
            return self.get_task(task_id)

    def _invalidate(
        self, task_id: str, now: float, *, preserve_session: bool = False
    ) -> None:
        self._descendants(task_id)
        self._connection.execute(
            """
            UPDATE attempts SET outcome='superseded',finished=?
            WHERE token IN (SELECT lease_token FROM tasks WHERE id IN (SELECT id FROM affected)) AND finished IS NULL
        """,
            (now,),
        )
        self._connection.execute(
            """
            UPDATE tasks SET generation=generation+1,state='pending',result=NULL,error='',attempts=0,
                session=CASE WHEN id=? THEN session ELSE '{}' END,
                lease_token=NULL,lease_owner=NULL,lease_until=NULL WHERE id IN (SELECT id FROM affected)
        """,
            (task_id if preserve_session else None,),
        )
        self._refresh_affected()

    def expand(
        self,
        claim: Claim,
        tasks: Sequence[Mapping[str, Any]],
        dependencies: Sequence[str],
        *,
        now: float | None = None,
    ) -> Task:
        """Atomically add prerequisites and defer a leased parent without changing its contract.

        The parent's frozen session survives; dependent sessions are invalidated.
        Existing prerequisites cannot be removed by a worker expansion.
        """
        specs = [self._spec(value) for value in tasks]
        with self._transaction():
            timestamp = _clock(now)
            self._assert_lease(claim, timestamp)
            previous = {
                row[0]
                for row in self._connection.execute(
                    "SELECT prerequisite_id FROM dependencies WHERE task_id=?",
                    (claim.task.id,),
                )
            }
            if isinstance(dependencies, (str, bytes)) or not previous.issubset(
                dependencies
            ):
                raise ValueError("expansion must preserve existing prerequisites")
            self._add_specs(specs)
            self._replace_dependencies(claim.task.id, dependencies)
            self._append_event(
                claim,
                "plan_expanded",
                _json(
                    {
                        "tasks": [row[0] for row, _ in specs],
                        "dependencies": list(dependencies),
                    }
                ),
                timestamp,
            )
            self._invalidate(claim.task.id, timestamp, preserve_session=True)
            return self.get_task(claim.task.id)

    def checkpoint(
        self, claim: Claim, session: dict[str, Any], now: float | None = None
    ) -> Task:
        """Save exact worker state under its lease without changing the mathematical contract."""
        if not isinstance(session, dict):
            raise ValueError("session must be an object")
        encoded = _json(session)
        with self._transaction():
            self._assert_lease(claim, _clock(now))
            self._connection.execute(
                "UPDATE tasks SET session=? WHERE id=?", (encoded, claim.task.id)
            )
            return self.get_task(claim.task.id)

    def _append_event(self, claim: Claim, kind: str, encoded: str, now: float) -> int:
        cursor = self._connection.execute(
            "INSERT INTO events(task_id,generation,kind,payload,created) VALUES (?,?,?,?,?)",
            (claim.task.id, claim.generation, kind, encoded, now),
        )
        assert cursor.lastrowid is not None
        return cursor.lastrowid

    def append_event(
        self, claim: Claim, kind: str, payload: dict[str, Any], now: float | None = None
    ) -> int:
        """Append a leased observation; store large response bytes in blobs."""
        if (
            not isinstance(kind, str)
            or not kind.strip()
            or not isinstance(payload, dict)
        ):
            raise ValueError("events require a kind and object payload")
        encoded = _json(payload)
        with self._transaction():
            timestamp = _clock(now)
            self._assert_lease(claim, timestamp)
            return self._append_event(claim, kind, encoded, timestamp)

    def events(
        self, task_id: str, limit: int = 50, after: int = 0
    ) -> list[dict[str, Any]]:
        """Read a bounded page of append-only task observations."""
        if not isinstance(limit, int) or isinstance(limit, bool) or limit <= 0:
            raise ValueError("limit must be a positive integer")
        self.get_task(task_id)
        rows = self._connection.execute(
            "SELECT * FROM events WHERE task_id=? AND id>? ORDER BY id LIMIT ?",
            (task_id, after, limit),
        )
        return [{**dict(row), "payload": json.loads(row["payload"])} for row in rows]

    def _replace_dependencies(self, task_id: str, dependencies: Sequence[str]) -> None:
        if isinstance(dependencies, (str, bytes)) or any(
            not isinstance(item, str) or not item.strip() for item in dependencies
        ):
            raise ValueError("dependencies must contain task identifiers")
        self._connection.execute("DELETE FROM dependencies WHERE task_id=?", (task_id,))
        try:
            self._connection.executemany(
                "INSERT INTO dependencies VALUES (?,?)",
                ((task_id, item) for item in dict.fromkeys(dependencies)),
            )
        except sqlite3.IntegrityError as exc:
            raise ValueError("missing prerequisite or self dependency") from exc
        cycle = self._connection.execute(
            """
            WITH RECURSIVE ancestors(id) AS (
                SELECT prerequisite_id FROM dependencies WHERE task_id=?
                UNION SELECT d.prerequisite_id FROM dependencies d JOIN ancestors a ON d.task_id=a.id
            ) SELECT 1 FROM ancestors WHERE id=? LIMIT 1
        """,
            (task_id, task_id),
        ).fetchone()
        if cycle:
            raise ValueError("task dependencies contain a cycle")

    def write_blob(self, data: bytes) -> str:
        """Atomically publish full bytes under their SHA-256 identity."""
        digest = hashlib.sha256(data).hexdigest()
        parent = self.directory / "blobs" / digest[:2]
        parent.mkdir(parents=True, exist_ok=True)
        # A durable file is insufficient if either newly created ancestor
        # directory entry disappears after power loss. Sync even when another
        # worker created the directory: that worker may not have synced it yet.
        self._sync_directory(self.directory)
        self._sync_directory(self.directory / "blobs")
        target = parent / digest
        descriptor, name = tempfile.mkstemp(prefix=".pending-", dir=parent)
        temporary = Path(name)
        try:
            with os.fdopen(descriptor, "wb") as output:
                output.write(data)
                output.flush()
                os.fsync(output.fileno())
            try:
                os.link(temporary, target)
            except FileExistsError:
                self.read_blob(digest)
            self._sync_directory(parent)
        finally:
            temporary.unlink(missing_ok=True)
        return digest

    @staticmethod
    def _sync_directory(path: Path) -> None:
        descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    def read_blob(self, digest: str) -> bytes:
        """Read a blob, rejecting invalid identifiers and corrupt content."""
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise ValueError("invalid blob hash")
        data = (self.directory / "blobs" / digest[:2] / digest).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError("blob content does not match its hash")
        return data
