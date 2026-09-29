"""Immutable UTF-8 sources with indexed, exact character-range retrieval.

Search returns complete indexed chunks with explicit offsets. It never replaces
the source document: ``read(id)`` returns all its text, without a context cap.
Names are labels; only content hashes determine blob paths.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sqlite3
import tempfile
from dataclasses import dataclass
from itertools import chain
from pathlib import Path
from typing import Iterator


@dataclass(frozen=True, slots=True)
class SourceDocument:
    id: str
    name: str
    sha256: str
    length: int


@dataclass(frozen=True, slots=True)
class SourceExcerpt:
    document_id: str
    start: int
    end: int
    total_length: int
    text: str
    sha256: str


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _positive_integer(value: int, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 1:
        raise ValueError(f"{name} must be a positive integer")


def _sync_directory(directory: Path) -> None:
    descriptor = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _mkdir_durable(directory: Path) -> None:
    # Persist each newly introduced directory name, including ancestors made
    # for a new campaign, before durable index rows can refer to its contents.
    missing = []
    current = directory
    while not current.exists():
        missing.append(current)
        current = current.parent
    for item in reversed(missing):
        item.mkdir(exist_ok=True)
        _sync_directory(item.parent)


def _ranges(text: str, maximum: int = 4096) -> Iterator[tuple[int, int]]:
    """Partition at paragraphs, splitting oversized paragraphs near whitespace."""
    start = 0
    boundaries = (match.end() for match in re.finditer(r"\r?\n[ \t]*\r?\n", text))
    for boundary in chain(boundaries, (len(text),)):
        while start < boundary:
            end = min(boundary, start + maximum)
            if end < boundary:
                # Keep ordinary words whole without creating unbounded chunks.
                whitespace = list(re.finditer(r"\s+", text[start + maximum // 2:end]))
                if whitespace:
                    end = start + maximum // 2 + whitespace[-1].end()
            yield start, end
            start = end


class SourceLibrary:
    """Persist complete sources and retrieve indexed excerpts without model calls."""

    def __init__(self, directory: Path | str):
        self.directory = Path(directory).expanduser().resolve()
        _mkdir_durable(self.directory)
        self._blobs = self.directory / "blobs"
        _mkdir_durable(self._blobs)
        self._db = sqlite3.connect(self.directory / "documents.sqlite3", timeout=30)
        self._db.row_factory = sqlite3.Row
        try:
            self._db.execute("PRAGMA journal_mode=WAL")
            self._db.execute("PRAGMA foreign_keys=ON")
            self._db.executescript(
                """
                CREATE TABLE IF NOT EXISTS documents (
                    id TEXT PRIMARY KEY, name TEXT NOT NULL, sha256 TEXT NOT NULL,
                    length INTEGER NOT NULL, byte_length INTEGER NOT NULL
                );
                CREATE TABLE IF NOT EXISTS chunks (
                    id INTEGER PRIMARY KEY,
                    document_id TEXT NOT NULL REFERENCES documents(id),
                    start INTEGER NOT NULL, end INTEGER NOT NULL,
                    byte_start INTEGER NOT NULL, byte_end INTEGER NOT NULL,
                    sha256 TEXT NOT NULL,
                    UNIQUE(document_id, start)
                );
                CREATE INDEX IF NOT EXISTS chunks_document_range
                    ON chunks(document_id, start, end);
                CREATE VIRTUAL TABLE IF NOT EXISTS chunks_fts USING fts5(
                    text, content='', tokenize='unicode61'
                );
                """
            )
        except BaseException:
            self._db.close()
            raise

    def __enter__(self) -> SourceLibrary:
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()

    def close(self) -> None:
        self._db.close()

    def _publish_blob(self, sha256: str, data: bytes) -> None:
        destination = self._blobs / sha256
        # A complete blob appears atomically. Interrupted ingestion may leave an
        # unreferenced temporary file, but never a partially published source.
        with tempfile.NamedTemporaryFile(dir=self._blobs, delete=False) as handle:
            temporary = Path(handle.name)
            try:
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
                try:
                    os.link(temporary, destination)
                except FileExistsError:
                    with destination.open("rb") as existing:
                        if hashlib.file_digest(existing, "sha256").hexdigest() != sha256:
                            raise ValueError("source blob integrity check failed")
            finally:
                temporary.unlink(missing_ok=True)
        # File fsync persists bytes; directory fsync persists the hash-addressed
        # hard-link name. Both must precede the SQLite transaction's commit.
        _sync_directory(self._blobs)

    def add(self, name: str, text: str) -> SourceDocument:
        if not isinstance(name, str) or not name.strip():
            raise ValueError("source name must be nonempty text")
        if not isinstance(text, str):
            raise ValueError("source content must be text")
        data = text.encode("utf-8")
        sha256 = _hash(data)
        identity = _hash(json.dumps([name, sha256], ensure_ascii=False).encode("utf-8"))
        self._publish_blob(sha256, data)
        with self._db:
            inserted = self._db.execute(
                "INSERT OR IGNORE INTO documents VALUES (?, ?, ?, ?, ?)",
                (identity, name, sha256, len(text), len(data)),
            ).rowcount
            if inserted:
                byte_start = 0
                for start, end in _ranges(text):
                    chunk = text[start:end]
                    chunk_bytes = chunk.encode("utf-8")
                    byte_end = byte_start + len(chunk_bytes)
                    cursor = self._db.execute(
                        "INSERT INTO chunks(document_id, start, end, byte_start, byte_end, sha256) "
                        "VALUES (?, ?, ?, ?, ?, ?)",
                        (identity, start, end, byte_start, byte_end, _hash(chunk_bytes)),
                    )
                    self._db.execute(
                        "INSERT INTO chunks_fts(rowid, text) VALUES (?, ?)",
                        (cursor.lastrowid, chunk),
                    )
                    byte_start = byte_end
        return self.get(identity)

    def _record(self, document_id: str) -> sqlite3.Row:
        row = self._db.execute("SELECT * FROM documents WHERE id = ?", (document_id,)).fetchone()
        if row is None:
            raise KeyError(document_id)
        return row

    @staticmethod
    def _document(row: sqlite3.Row) -> SourceDocument:
        return SourceDocument(row["id"], row["name"], row["sha256"], row["length"])

    def get(self, document_id: str) -> SourceDocument:
        return self._document(self._record(document_id))

    def list(self, limit: int = 50, after: str = "") -> list[SourceDocument]:
        """Page by stable document ID; use the last returned ID as ``after``."""
        _positive_integer(limit, "limit")
        if not isinstance(after, str):
            raise ValueError("after must be a document ID string")
        rows = self._db.execute(
            "SELECT * FROM documents WHERE id > ? ORDER BY id LIMIT ?", (after, limit)
        )
        return [self._document(row) for row in rows]

    def read(self, document_id: str, start: int = 0, end: int | None = None) -> SourceExcerpt:
        row = self._record(document_id)
        length = row["length"]
        if end is None:
            end = length
        if any(not isinstance(value, int) or isinstance(value, bool) for value in (start, end)):
            raise ValueError("source range offsets must be integers")
        if not 0 <= start <= end <= length:
            raise ValueError(f"source range must satisfy 0 <= start <= end <= {length}")
        chunks = self._db.execute(
            "SELECT * FROM chunks WHERE document_id = ? "
            "AND start >= (SELECT MAX(start) FROM chunks WHERE document_id = ? AND start <= ?) "
            "AND start < ? AND end > ? ORDER BY start",
            (document_id, document_id, start, end, start),
        )
        fragments = []
        position = start
        try:
            with (self._blobs / row["sha256"]).open("rb") as handle:
                if os.fstat(handle.fileno()).st_size != row["byte_length"]:
                    raise ValueError("source blob changed: byte-length integrity check failed")
                for chunk in chunks:
                    if not chunk["start"] <= position < chunk["end"]:
                        raise ValueError("source range index integrity check failed")
                    handle.seek(chunk["byte_start"])
                    data = handle.read(chunk["byte_end"] - chunk["byte_start"])
                    if _hash(data) != chunk["sha256"]:
                        raise ValueError("source blob changed: chunk hash integrity check failed")
                    decoded = data.decode("utf-8")
                    if len(decoded) != chunk["end"] - chunk["start"]:
                        raise ValueError("source character-range integrity check failed")
                    stop = min(end, chunk["end"])
                    fragments.append(decoded[position - chunk["start"]:stop - chunk["start"]])
                    position = stop
        except OSError as exc:
            raise ValueError("source blob missing or unreadable: integrity check failed") from exc
        if position != end:
            raise ValueError("source range index is incomplete")
        text = "".join(fragments)
        if start == 0 and end == length and _hash(text.encode("utf-8")) != row["sha256"]:
            raise ValueError("source document hash integrity check failed")
        return SourceExcerpt(document_id, start, end, length, text, row["sha256"])

    def search(self, query: str, limit: int = 8) -> list[SourceExcerpt]:
        """Match literal Unicode word tokens, ANDed within indexed paragraphs.

        SQL, FTS operators and punctuation have no control meaning. Returned
        ranges are explicit and can be expanded with ``read`` when needed.
        """
        _positive_integer(limit, "limit")
        if not isinstance(query, str):
            raise ValueError("search query must be text")
        terms = re.findall(r"[^\W_]+", query, flags=re.UNICODE)
        if not terms:
            return []
        expression = " AND ".join('"' + term + '"' for term in terms)
        rows = self._db.execute(
            "SELECT c.document_id, c.start, c.end FROM chunks_fts "
            "JOIN chunks c ON c.id = chunks_fts.rowid "
            "WHERE chunks_fts MATCH ? ORDER BY rank, c.id LIMIT ?",
            (expression, limit),
        ).fetchall()
        return [self.read(row["document_id"], row["start"], row["end"]) for row in rows]
