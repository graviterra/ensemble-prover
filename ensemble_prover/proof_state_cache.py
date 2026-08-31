"""Persistent verified-helper cache for proof-state search."""

from __future__ import annotations

import json
import inspect
import os
import re
import time
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, ClassVar, Dict, List, Mapping, Optional, Sequence, Set, Tuple

try:  # The Mini prover runs on POSIX hosts; retain a fail-closed fallback.
    import fcntl
except ImportError:  # pragma: no cover - exercised only on unsupported hosts.
    fcntl = None  # type: ignore[assignment]

from .proof_dossier import (
    helper_decl_name,
    is_answer_unsafe_helper_source,
    text_hash,
    verified_helper_is_premise_projection,
)
from .helper_quality import classify_auxiliary_statement_quality
from .proof_graph import (
    graph_statement_key,
    graph_statement_non_theorem_reason,
    helper_decl_statement,
)
from .proof_state import (
    _compact_search_text,
    canonicalize_lean_statement_for_identity,
    lean_referenced_helper_names,
)
from .utils import has_sorry_or_admit

_PROJECT_ROOT = Path(__file__).resolve().parent.parent

# A durable marker is the cross-process fail-closed mechanism.  If the
# filesystem is unhealthy enough that even that marker cannot be written, a
# live process can still prevent sibling parallel samples from consuming the
# stranded row.  This registry is deliberately monotone for the process
# lifetime: an operator must repair/quarantine a path before a fresh process
# may trust it again.
_UNTRUSTED_DEADLINE_PUBLICATION_PATHS: Set[str] = set()


def _deadline_publication_path_key(path: Path) -> str:
    candidate = Path(path)
    try:
        return str(candidate.resolve())
    except Exception:
        return str(candidate.absolute())


def _mark_deadline_publication_path_untrusted(path: Path) -> None:
    _UNTRUSTED_DEADLINE_PUBLICATION_PATHS.add(
        _deadline_publication_path_key(Path(path))
    )


def _deadline_publication_path_is_trusted(path: Path) -> bool:
    return _deadline_publication_path_key(Path(path)) not in (
        _UNTRUSTED_DEADLINE_PUBLICATION_PATHS
    )


def _clone_cache_value(value: Any) -> Any:
    """Clone JSON-like cache metadata without invoking user callbacks.

    Cache records cross reader, sample, and public API boundaries.  Their
    nested provenance containers must therefore be private even though
    immutable scalar values can be shared safely.  Restricting the clone to
    exact built-in containers avoids executing arbitrary copy hooks.
    """

    if type(value) is dict:
        return {key: _clone_cache_value(item) for key, item in value.items()}
    if type(value) is list:
        return [_clone_cache_value(item) for item in value]
    if type(value) is tuple:
        return tuple(_clone_cache_value(item) for item in value)
    if type(value) is set:
        return {_clone_cache_value(item) for item in value}
    if type(value) is frozenset:
        return frozenset(_clone_cache_value(item) for item in value)
    return value


def _clone_cache_record(record: Mapping[str, Any]) -> Dict[str, Any]:
    """Return a private, callback-free copy of one cache record."""

    return {key: _clone_cache_value(value) for key, value in record.items()}


@dataclass
class DeadlineAwareCachePublication:
    """A lock-held, reversible cache append owned by one outer transaction.

    The cache is JSONL and therefore cannot be deep-copied or naively
    rewritten after another process appends.  This receipt reserves a
    per-path POSIX lock before the outer dossier transaction commits, appends
    only during ``commit``, and keeps that lock until ``finalize`` or
    ``rollback``.  Readers and ordinary writers use the same lock, so a
    deadline-losing row is neither indexed nor observable as a seed.
    """

    cache: "MiniVerifiedLemmaCache"
    record: Dict[str, Any]
    owner_record_id: str
    deadline_exhausted: Callable[[], bool]
    lock_file: Any
    offset: Optional[int] = None
    appended: bool = False
    indexed: bool = False
    closed: bool = False
    displaced_advisory_records: List[Dict[str, Any]] = field(default_factory=list)

    def _deadline_elapsed(self) -> bool:
        try:
            return bool(self.deadline_exhausted())
        except Exception:
            return True

    def _release_lock(self) -> None:
        if self.closed:
            return
        self.closed = True
        self.cache._release_path_lock(self.lock_file)

    def _discard_index(self) -> None:
        if self.indexed:
            self.cache._remove_owner_record_from_indexes(self.owner_record_id)
            self.cache._restore_advisory_records(self.displaced_advisory_records)
            self.displaced_advisory_records.clear()
            self.indexed = False

    def _truncate_append(self) -> bool:
        if not self.appended or self.offset is None:
            return True
        try:
            current_size = int(self.cache.path.stat().st_size)
            expected_size = int(self.offset) + len(
                (json.dumps(self.record, ensure_ascii=False) + "\n").encode("utf-8")
            )
            if current_size != expected_size:
                raise OSError(
                    "cache changed while deadline-aware publication held its lock"
                )
            with self.cache.path.open("r+b") as fp:
                fp.truncate(self.offset)
            self.appended = False
            return True
        except Exception as exc:
            self.cache._quarantine_deadline_publication_failure(exc)
            return False

    def commit(self) -> bool:
        """Append a private row, retaining the lock for final visibility."""

        if self.closed:
            return False
        # This receipt owns the destination's exclusive path lock.  A prior
        # publisher may have installed the durable fail-closed marker while
        # this receipt was waiting to acquire it, so destination trust must be
        # checked here rather than only before lock acquisition.
        if self.cache._cache_is_disabled():
            self._release_lock()
            # Persistence is advisory once Lean accepted the helper.
            return True
        if self._deadline_elapsed():
            self.rollback()
            return False
        try:
            self.offset = int(self.cache.path.stat().st_size) if self.cache.path.exists() else 0
            with self.cache.path.open("a", encoding="utf-8") as fp:
                fp.write(json.dumps(self.record, ensure_ascii=False) + "\n")
                fp.flush()
            self.appended = True
        except Exception as exc:
            # Cache durability is advisory for a successfully kernel-checked
            # helper.  Preserve the pre-existing acceptance semantics while
            # making the failed append observable.
            self.cache._record_store_failure(exc)
            self._release_lock()
            return True
        if self._deadline_elapsed():
            self.rollback()
            return False
        return True

    def finalize(self) -> bool:
        """Index a row while retaining rollback until the outer final gate."""

        if self.closed:
            # An advisory I/O failure closed the receipt without a row.
            return not self.appended
        if self._deadline_elapsed():
            self.rollback()
            return False
        if self.appended:
            self.displaced_advisory_records = (
                self.cache._advisory_records_superseded_by(self.record)
            )
            self.indexed = True
            try:
                self.cache._index_stored_record(self.record, self.owner_record_id)
            except Exception:
                # ``_index_stored_record`` may have inserted one tier before
                # an adapter/subclass raises.  Marking first guarantees the
                # enclosing transaction compensates both disk and every
                # partial in-memory index.
                return False
        if self._deadline_elapsed():
            self.rollback()
            return False
        return True

    def release(self) -> bool:
        """Unlock only after the outer transaction chose its commit point."""

        self.displaced_advisory_records.clear()
        self._release_lock()
        return True

    def rollback(self) -> None:
        """Remove an uncommitted append while the reserved path lock is held."""

        if self.closed:
            return
        self._discard_index()
        self._truncate_append()
        self._release_lock()

_TOP_LEVEL_HEADER_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|by\b)",
)
_FORBIDDEN_LEAN_COMMAND_RE = re.compile(
    r"(?m)^\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"("
    r"#\w+"
    r"|import\b"
    r"|axiom\b"
    r"|constant\b"
    r"|opaque\b"
    r"|structure\b"
    r"|class\b"
    r"|inductive\b"
    r"|coinductive\b"
    r"|mutual\b"
    r"|namespace\b"
    r"|section\b"
    r"|end\b"
    r"|open\b"
    r"|variable\b"
    r"|variables\b"
    r"|universe\b"
    r"|universes\b"
    r"|syntax\b"
    r"|macro\b"
    r"|elab\b"
    r"|notation\b"
    r"|infix\b"
    r"|prefix\b"
    r"|postfix\b"
    r"|scoped\b"
    r"|initialize\b"
    r"|builtin_initialize\b"
    r"|declare_syntax_cat\b"
    r"|set_option\b"
    r"|attribute\b"
    r"|register_simp_attr\b"
    r"|register_option\b"
    r"|export\b"
    r"|alias\b"
    r"|elab_rules\b"
    r"|run_cmd\b"
    r"|local\b"
    r")"
)
_SAFE_TOP_LEVEL_HELPER_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:theorem|lemma)\b"
)


def _strip_lean_comments_and_strings(src: str) -> str:
    text = str(src or "")
    out: List[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            out.append("\n" if ch in "\r\n" else " ")
            if ch == "\\" and i + 1 < n:
                i += 2
                out.append(" ")
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch in "\r\n" else " ")
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and text[i] not in "\r\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _find_forbidden_lean_command(helpers: List[str], proof: str) -> Optional[str]:
    src = "\n\n".join([*helpers, proof])
    stripped = _strip_lean_comments_and_strings(src)
    for match in _FORBIDDEN_LEAN_COMMAND_RE.finditer(stripped):
        command = match.group(1)
        leading = stripped[match.start() : match.start(1)]
        line_end = stripped.find("\n", match.end())
        if line_end < 0:
            line_end = len(stripped)
        tail = stripped[match.end() : line_end]
        in_match = re.search(r"\bin\b", tail)
        dangerous_open_body = bool(
            in_match
            and _FORBIDDEN_LEAN_COMMAND_RE.match(tail[in_match.end() :])
        )
        if command == "open" and leading and in_match and not dangerous_open_body:
            continue
        return command
    return None


def _split_top_level_chunks(src: str) -> Tuple[str, List[str]]:
    scan_src = _strip_lean_comments_and_strings(src)
    matches = list(_TOP_LEVEL_HEADER_RE.finditer(scan_src))
    if not matches:
        return src.strip(), []
    leading = src[: matches[0].start()].strip()
    chunks: List[str] = []
    for i, match in enumerate(matches):
        start = match.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(src)
        chunks.append(src[start:end].strip())
    return leading, chunks


def _normalize_cache_statement(statement: str) -> str:
    return graph_statement_key(canonicalize_lean_statement_for_identity(statement))


@lru_cache(maxsize=32768)
def _cached_semantic_record_analysis(
    source: str,
    fallback_statement: str,
) -> Tuple[str, str, str, str, str]:
    """Return immutable helper-ingest analysis shared by cache readers.

    Every cache instance still derives identity and applies every publication
    boundary from source.  The result is callback-free and depends only on the
    exact persisted source plus its fallback statement, so reusing it within a
    process cannot grant authority to a changed row.  It avoids repeating the
    comparatively expensive Lean-syntax analysis once per reader/sample.

    The tuple is ``(rejection_kind, source_statement, statement,
    source_hash, statement_hash)``.  An empty rejection kind denotes an
    admissible semantic shape; record-specific schema, preamble, provenance,
    and ownership checks remain in ``_record_ingest_keys``.
    """

    helper_source = str(source or "").strip()
    source_statement = helper_decl_statement(helper_source)
    statement_source = source_statement or str(fallback_statement or "")
    statement = _normalize_cache_statement(statement_source)
    source_hash = text_hash(helper_source)
    if not helper_source or not statement or not source_hash:
        return "field_rejected", source_statement, statement, source_hash, ""
    if not source_statement or graph_statement_non_theorem_reason(source_statement):
        return "non_theorem", source_statement, statement, source_hash, ""
    if verified_helper_is_premise_projection(
        {"source": helper_source, "statement": source_statement}
    ):
        return "projection_rejected", source_statement, statement, source_hash, ""
    if not classify_auxiliary_statement_quality(
        source_statement
    ).cache_publishable:
        return "quality_rejected", source_statement, statement, source_hash, ""
    if _proof_state_helper_policy_rejection(
        helper_source,
        expected_statement=source_statement or statement,
    ):
        return "policy_rejected", source_statement, statement, source_hash, ""
    return "", source_statement, statement, source_hash, text_hash(statement)


class MiniVerifiedLemmaCache:
    """Persistent cache for kernel-checked proof-state helper declarations.

    Two-tier in-memory index (2026-05-08, Gap 2 fix):

    - **Tier 1** (``_by_exact_key``) — keyed by ``(canonical_stmt_hash, preamble_hash)``.
      Fast path for same-preamble rehydration: when a problem is re-attempted
      with the same preamble, cached helpers replay instantly.
    - **Tier 2** (``_by_canonical_statement``) — keyed by ``canonical_stmt_hash`` alone.
      Cross-preamble fallback: every PutnamBench problem has a different
      ``_solution`` axiom in its preamble, so the Tier 1 key is mismatched
      across problems. Tier 2 lets a generic helper (e.g. ``∀ n, n + 0 = n``)
      proven under one problem's preamble be tried under a different problem's
      preamble. The Lean kernel is still the judge — ``_accept_proof_state_helper``
      re-compiles the cached body in the new preamble before accepting; bodies
      that reference unavailable symbols simply fail to compile.

    Soundness rationale:
    - ``is_answer_unsafe_helper_source`` rejects any helper referencing ``_solution``
      at storage time (via ``_proof_state_helper_policy_rejection``), so the
      stored bodies are problem-generic.
    - The cache never trusts a body without re-verification — every consumer
      goes through ``_accept_proof_state_helper``, which kernel-checks the body
      under the current preamble.

    Schema v4 added replay-context provenance. Schema v5 invalidates identity
    keys produced before bounded-quantifier canonicalization preserved nested
    big-operator commas. Schema v6 invalidates identity keys produced before
    (a) the chained-implication α-stability fix (``∀ x, x ∈ S → ∀ y, …`` no
    longer fabricates a bounded binder / leaks un-renamed variables) and
    (b) uniform colon-spacing normalization (``(0:ℝ)`` ≡ ``(0 : ℝ)``).
    Schema v7 invalidates keys produced before the capture-safety fixes
    (glyph rewriting skipped when both spellings coexist; alpha names
    reserved above literal ``_bN`` tokens) — false MATCHES between
    non-equivalent propositions were possible before.
    Schema v8 invalidates keys produced before pattern-lambda identity stopped
    parsing ``=>`` as a relation and before partially parsed tuple patterns
    could rewrite an outer binder into a captured local name.
    Schema v9 adds the structural auxiliary-helper quality boundary.  Older
    rows may contain kernel-valid vacuities (for example ``P -> True``) that
    are unsuitable as durable cross-problem evidence even though Lean accepts
    their declarations.
    Schema v10 invalidates identity keys produced before whitespace
    normalization became Lean-lexer-aware.  Earlier keys collapsed whitespace
    inside strings, raw strings, character literals, and quoted identifiers,
    allowing different executable propositions to share a cache bucket.
    Schema migration (2026-08-19).  A bump must not silently zero the cache:
    every dropped row is a helper the Lean kernel already verified and would
    have to prove again.  ``_record_ingest_keys`` therefore admits every row at
    or below the current version and re-derives its identity keys
    (``statement`` / ``statement_hash`` / ``source_hash`` / tier keys) from
    ``source`` + ``preamble_hash`` through the *current* normalizer, and
    re-applies the current publication filters (non-theorem, premise
    projection, auxiliary-quality, helper policy).  Every v5..v8 invalidation
    reason is a defect in the key-derivation function, and every v9 reason is a
    publication filter, so both are fully repaired by that re-derivation --
    a stale stored key is never trusted, it is recomputed.

    What re-derivation cannot repair is provenance.  Schema v4 introduced the
    replay-context fields (``replay_context_names`` /
    ``replay_context_source_hashes``); a v1..v3 row predates them, and an
    implicit tactic dependency (an ``@[simp]`` sibling that made the body
    compile) cannot be reconstructed from source text.  Such rows are admitted
    in an **advisory tier**: indexed for Tier 1/Tier 2 ``lookup`` and
    ``retrieval_records`` -- both documented candidate-only paths whose
    consumers re-kernel-check ``source`` before trusting it -- but kept out of
    ``records_for_theorem``, which reconstructs a replay dependency closure and
    would read their absent closure as an authoritative "no dependencies".
    Advisory rows also claim no owner-record identity, so the republication
    that upgrades them to a provenance-bearing row is never blocked.  They are
    tagged with ``migrated_from_schema_version`` and
    ``replay_provenance_available: False``, their provenance fields are
    stripped, and they keep their original ``schema_version`` when written
    back out by a merge, so they cannot masquerade as provenance-bearing --
    not to this build, and not to one without this migration.

    Ingest counters record migrated, advisory and rejected rows so a bump is
    never a silent empty index.
    """

    schema_version = 10

    # Schema v4 introduced replay-context provenance.  Rows written before it
    # cannot supply an implicit tactic dependency, so they are admitted only in
    # the advisory tier described above.
    _PROVENANCE_SCHEMA_VERSION: ClassVar[int] = 4
    # Oldest on-disk row shape whose ``source``/``preamble_hash`` pair is still
    # interpretable by the current ingestion path.
    _MIN_MIGRATABLE_SCHEMA_VERSION: ClassVar[int] = 1
    # Persisted migration markers.  ``merge_records_from_path`` writes the
    # migrated row back out under the current ``schema_version``, so the
    # advisory classification has to survive that round trip instead of being
    # recoverable only from the raw version field.
    _ORIGIN_SCHEMA_FIELD: ClassVar[str] = "migrated_from_schema_version"
    _PROVENANCE_FLAG_FIELD: ClassVar[str] = "replay_provenance_available"
    _RESTORE_TIER_RANKS_FIELD: ClassVar[str] = "_cache_restore_tier_ranks"
    # Fields a pre-v4 row can never have carried.  Stripped on ingestion so no
    # consumer anywhere can read a fabricated (empty) dependency closure off a
    # legacy row and mistake it for "this helper has no dependencies".
    _PROVENANCE_FIELDS: ClassVar[Tuple[str, ...]] = (
        "support_names",
        "support_source_hashes",
        "replay_context_names",
        "replay_context_source_hashes",
    )

    def __init__(
        self,
        path: Path,
        *,
        read_paths: Sequence[Path] = (),
        validated_seed: Optional["MiniVerifiedLemmaCache"] = None,
        store_failure_metric_sink: Optional[Callable[[str, int], None]] = None,
    ) -> None:
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._deadline_publication_disabled = self._disabled_marker_path(
            self.path
        ).exists()
        # Tier 1: (canonical_stmt_hash, preamble_hash) → records (most-recent first).
        self._by_exact_key: Dict[str, List[Dict[str, Any]]] = {}
        # Tier 2: canonical_stmt_hash → records (most-recent first), used for
        # cross-preamble fallback. Same record may appear in both tiers.
        self._by_canonical_statement: Dict[str, List[Dict[str, Any]]] = {}
        # Owner namespace → records.  Same-problem seeding is an ownership
        # query, not a statement lookup, so it must retain an alias even when
        # the declaration body is already globally indexed for another root.
        self._by_theorem_name: Dict[str, List[Dict[str, Any]]] = {}
        # Body identity is global for lookup de-duplication, while cache
        # ownership is a separate relation.  A verified declaration can be
        # relevant to several root theorems; collapsing those owner records
        # made same-problem rehydration depend on which child happened to
        # store first.
        self._source_hashes: Set[str] = set()
        # Subset of ``_source_hashes`` currently held by an advisory
        # (pre-provenance) row.  Tracked so a later provenance-bearing row for
        # the same body supersedes the weaker copy instead of being deduped
        # away behind it.
        self._advisory_source_keys: Set[str] = set()
        self._owner_record_ids: Set[str] = set()
        self._local_owner_record_ids: Set[str] = set()
        self._cache_access_seq: int = 0
        self._defer_cache_bucket_trim = False
        self._storage_reload_depth = 0
        self._index_record_context: List[
            Tuple[
                Tuple[str, str, str],
                Optional[Set[str]],
                Optional[Mapping[str, Mapping[str, int]]],
                bool,
            ]
        ] = []
        self._read_paths: List[Path] = [Path(item) for item in (read_paths or ())]
        self._read_path_line_counts: Dict[str, int] = {}
        self._read_path_snapshots: Dict[str, Tuple[int, int, int, int, int]] = {}
        self.last_merge_errors: List[str] = []
        self.last_ingest_rejections: List[str] = []
        self.total_ingest_schema_migrated = 0
        self.total_ingest_schema_advisory = 0
        self.total_ingest_schema_rejected = 0
        self.total_ingest_quality_rejected = 0
        self.total_ingest_projection_rejected = 0
        self.total_ingest_policy_rejected = 0
        self.total_ingest_field_rejected = 0
        self.total_ingest_owner_deduped = 0
        self._ingest_metrics_published: Dict[str, int] = {}
        # B3 fix (2026-05-11): observability for ``store`` failures.
        # ``store`` previously swallowed IO exceptions silently and
        # returned ``False``; the five callers (mini_prover, helper_only_salvage,
        # proof_state_executor) discard the bool. A failed store leaves the
        # helper durable in the dossier+graph but ABSENT from the on-disk
        # cache JSONL — breaking the cross-problem Tier-2 reuse that
        # ``_by_canonical_statement`` enables. Mirroring the
        # ``last_merge_errors`` pattern lets the summary writer surface
        # this drift in run.log/summary.json without changing caller
        # semantics. Capped to ``_STORE_ERROR_RETENTION`` to bound
        # memory under pathological failure loops.
        self.last_store_errors: List[str] = []
        # Total uncapped count complements the 64-entry list. The list
        # gives diagnostic detail (last N error strings); this counter
        # is the SLI — answers "did ANY store fail this run?" and how
        # many. Surfaced via summary writer + RunMetrics
        # ``mini_lemma_cache_store_errors`` key.
        self.total_store_failures: int = 0
        # True only when neither truncation/quarantine nor the durable
        # fail-closed marker could be written.  This is an external storage
        # integrity incident, not a recoverable cache miss.
        self.deadline_publication_integrity_unrecoverable = False
        self._store_failure_metric_sink = store_failure_metric_sink
        if not self._deadline_publication_disabled:
            seeded_read_path = self._seed_from_validated_cache(validated_seed)
            for read_path in self._read_paths:
                if self._read_path_key(read_path) == seeded_read_path:
                    continue
                self._load_new_records(Path(read_path))
            self._load(self.path)

    @staticmethod
    def _read_path_key(path: Path) -> str:
        candidate = Path(path)
        # Keep the configured logical path stable across symlink retargeting;
        # the opened-file snapshot separately detects the new target inode.
        return str(candidate.absolute())

    def _seed_from_validated_cache(
        self,
        seed: Optional["MiniVerifiedLemmaCache"],
    ) -> str:
        """Copy a validated read-through index without replaying its JSONL.

        Parallel samples need private writer files, but they all begin from the
        same durable base cache.  Re-parsing and reclassifying that base in
        every sample blocks the event loop before any sample can yield.  Copy
        only the already-validated in-memory indexes; records remain private
        dicts so lookup ranking in one sample cannot mutate a sibling.

        The source line cursor is copied with the index.  Ordinary refreshes
        therefore ingest only rows appended after the shared cache snapshot,
        preserving live cross-process and sibling visibility.
        """

        if seed is None or seed is self or seed._cache_is_disabled():
            return ""
        seed_path_key = self._read_path_key(seed.path)
        if seed_path_key not in {
            self._read_path_key(read_path) for read_path in self._read_paths
        }:
            return ""
        line_count = seed._read_path_line_counts.get(seed_path_key)
        snapshot = seed._read_path_snapshots.get(seed_path_key)
        if line_count is None or snapshot is None:
            return ""

        self._by_exact_key = {
            key: [_clone_cache_record(record) for record in records]
            for key, records in seed._by_exact_key.items()
        }
        self._by_canonical_statement = {
            key: [_clone_cache_record(record) for record in records]
            for key, records in seed._by_canonical_statement.items()
        }
        self._by_theorem_name = {
            key: [_clone_cache_record(record) for record in records]
            for key, records in seed._by_theorem_name.items()
        }
        self._source_hashes = set(seed._source_hashes)
        self._advisory_source_keys = set(seed._advisory_source_keys)
        self._owner_record_ids = set(seed._owner_record_ids)
        # Base ownership is visible for de-duplication but is not local to the
        # sample writer.  Only rows written to this sample path may suppress a
        # second local publication or be treated as sample-owned at merge.
        self._local_owner_record_ids = set()
        self._cache_access_seq = int(seed._cache_access_seq or 0)
        self._read_path_line_counts[seed_path_key] = int(line_count or 0)
        self._read_path_snapshots[seed_path_key] = tuple(snapshot)
        return seed_path_key

    # Most-recent N retained; older entries are dropped to prevent
    # unbounded growth under pathological failure loops (e.g., read-only
    # cache directory throughout a multi-thousand-helper run).
    _STORE_ERROR_RETENTION: ClassVar[int] = 64
    _INGEST_REJECTION_RETENTION: ClassVar[int] = 64
    _INGEST_METRIC_NAMES: ClassVar[Dict[str, str]] = {
        "schema_migrated": "mini_lemma_cache_ingest_schema_migrated",
        "schema_advisory": "mini_lemma_cache_ingest_schema_advisory",
        "schema_rejected": "mini_lemma_cache_ingest_schema_rejected",
        "quality_rejected": "mini_lemma_cache_ingest_quality_rejected",
        "projection_rejected": "mini_lemma_cache_ingest_projection_rejected",
        "policy_rejected": "mini_lemma_cache_ingest_policy_rejected",
        "field_rejected": "mini_lemma_cache_ingest_field_rejected",
        "owner_deduped": "mini_lemma_cache_ingest_owner_deduped",
    }

    # Backward-compat alias: existing callers and tests may reference
    # ``_by_key`` directly. Keep a property that exposes Tier 1 so the
    # rename is transparent.
    @property
    def _by_key(self) -> Dict[str, List[Dict[str, Any]]]:
        return self._by_exact_key

    def request_config(self) -> Dict[str, Any]:
        """Stable cache configuration for recursive solver-lane accounting.

        Mutable corpus identity belongs to ``solver_frontier_config``.  Keeping
        global source/owner counts here would let an unrelated theorem append
        mint a fresh model lane even though the current goal's served helpers
        are unchanged.
        """

        self.refresh_read_paths()
        return {
            "schema_version": self.schema_version,
            "path": str(self.path.resolve()),
            "read_paths": tuple(
                str(path.resolve()) for path in self._read_paths
            ),
            "deadline_publication_disabled": self._cache_is_disabled(),
        }

    def solver_frontier_config(
        self,
        statements: Sequence[str],
        *,
        preamble: str,
        max_hits: int = 3,
    ) -> Dict[str, Any]:
        """Describe the capped helper frontier without changing hit ranks.

        Recursive model-lane accounting must distinguish two calls when the
        cache would serve different helpers.  The ordinary lookup is
        intentionally hit-ranked and mutates recency, so corpus identity alone
        is insufficient.  This method records the exact ordered candidates
        without touching them.  Ordinary lookup updates the selected batch in
        an order-preserving transaction, so a repeat read stays stable while a
        real external rank change remains visible.
        """

        cap = max(0, int(max_hits or 0))
        if self._cache_is_disabled() or cap <= 0:
            return {
                "schema_version": 1,
                "max_hits": cap,
                "targets": (),
            }
        self.refresh_read_paths()
        targets: List[Dict[str, Any]] = []
        normalized_statements = {
            _normalize_cache_statement(str(statement or ""))
            for statement in statements
            if _normalize_cache_statement(str(statement or ""))
        }
        for statement in sorted(normalized_statements):
            canonical_key = self._canonical_key(statement)
            exposed = [
                {
                    "tier": tier,
                    "source_hash": str(record.get("source_hash") or ""),
                    "preamble_hash": str(record.get("preamble_hash") or ""),
                    "name": str(record.get("name") or ""),
                }
                for tier, record in self._select_lookup_records(
                    statement,
                    preamble=preamble,
                    cap=cap,
                )
            ]
            targets.append(
                {
                    "statement_hash": canonical_key,
                    # Ordered identity is solver-semantic: verification is
                    # sequential and deadline-bounded. ``lookup`` batch-touches
                    # this selection without permuting it, so a repeat read is
                    # stable while an external rank change remains visible.
                    "exposed": tuple(exposed),
                }
            )
        return {
            "schema_version": 1,
            "max_hits": cap,
            "targets": tuple(targets),
        }

    def set_store_failure_metric_sink(
        self,
        sink: Optional[Callable[[str, int], None]],
    ) -> None:
        """Attach a run-level metric sink for cache write and ingest events."""

        self._store_failure_metric_sink = sink
        self._flush_ingest_metrics_to_sink()

    def _flush_ingest_metrics_to_sink(self) -> None:
        """Publish ingest counters that accrued before a sink was attached."""

        sink = self._store_failure_metric_sink
        if sink is None:
            return
        for kind, metric_name in self._INGEST_METRIC_NAMES.items():
            total = int(getattr(self, f"total_ingest_{kind}", 0) or 0)
            already = int(self._ingest_metrics_published.get(kind, 0) or 0)
            delta = total - already
            if delta <= 0:
                continue
            try:
                sink(metric_name, delta)
            except Exception:
                continue
            self._ingest_metrics_published[kind] = total

    def _record_store_failure(self, exc: BaseException) -> None:
        """Record a failed cache append on the cache and its run metric sink."""

        try:
            self.total_store_failures += 1
            self.last_store_errors.append(
                f"{type(exc).__name__}: {exc} (path={self.path})"
            )
            if len(self.last_store_errors) > self._STORE_ERROR_RETENTION:
                # Drop oldest; the most-recent N are typically most
                # diagnostically relevant.
                del self.last_store_errors[
                    : len(self.last_store_errors) - self._STORE_ERROR_RETENTION
                ]
        except Exception:
            # The observability path must never itself raise out of a caller's
            # exception handler.
            pass
        sink = self._store_failure_metric_sink
        if sink is not None:
            try:
                sink("mini_lemma_cache_store_errors", 1)
            except Exception:
                pass

    def _note_ingest(self, kind: str, detail: str = "") -> None:
        """Count one ingest migration or rejection without raising to callers."""

        attr = f"total_ingest_{kind}"
        try:
            setattr(self, attr, int(getattr(self, attr, 0) or 0) + 1)
            # Migrated and advisory rows are admissions, not rejections; only
            # genuine rejections belong in the diagnostic tail.
            if kind not in ("schema_migrated", "schema_advisory"):
                preview = str(detail or kind).replace("\n", " ")[:160]
                self.last_ingest_rejections.append(preview)
                if len(self.last_ingest_rejections) > self._INGEST_REJECTION_RETENTION:
                    del self.last_ingest_rejections[
                        : len(self.last_ingest_rejections)
                        - self._INGEST_REJECTION_RETENTION
                    ]
        except Exception:
            return
        sink = self._store_failure_metric_sink
        metric_name = self._INGEST_METRIC_NAMES.get(kind)
        if sink is None or not metric_name:
            return
        try:
            sink(metric_name, 1)
        except Exception:
            return
        self._ingest_metrics_published[kind] = int(getattr(self, attr, 0) or 0)

    def _count_schema_migration_if_needed(self, record: Mapping[str, Any]) -> None:
        try:
            raw_version = int(record.get("schema_version") or 0)
        except (TypeError, ValueError):
            return
        # Full (non-advisory) migration range: provenance-bearing rows below
        # the current version.  Advisory admissions (pre-provenance rows) are
        # counted separately as schema_advisory.
        if (
            raw_version >= int(self._PROVENANCE_SCHEMA_VERSION)
            and raw_version < self.schema_version
        ):
            self._note_ingest("schema_migrated")

    @staticmethod
    def _disabled_marker_path(path: Path) -> Path:
        target = Path(path)
        return target.with_name(f".{target.name}.deadline-publication-disabled")

    def _cache_is_disabled(self) -> bool:
        return (
            bool(self._deadline_publication_disabled)
            or not _deadline_publication_path_is_trusted(self.path)
            or self._disabled_marker_path(self.path).exists()
        )

    def _disable_deadline_publication_cache(self, exc: BaseException) -> None:
        """Persist a fail-closed marker if a suspect row cannot be removed."""

        marker = self._disabled_marker_path(self.path)
        try:
            marker.write_text(
                f"disabled after deadline cache recovery failure: {type(exc).__name__}\n",
                encoding="utf-8",
            )
        except Exception as marker_exc:
            self._record_store_failure(marker_exc)
            self.deadline_publication_integrity_unrecoverable = True
            _mark_deadline_publication_path_untrusted(self.path)
            sink = self._store_failure_metric_sink
            if sink is not None:
                try:
                    sink("mini_lemma_cache_deadline_integrity_unrecoverable", 1)
                except Exception:
                    pass
        self._deadline_publication_disabled = True

    @staticmethod
    def _lock_path_for(path: Path) -> Path:
        target = Path(path)
        return target.with_name(f".{target.name}.lock")

    @classmethod
    def _acquire_path_lock(
        cls,
        path: Path,
        *,
        exclusive: bool,
        nonblocking: bool = False,
    ) -> Any:
        """Acquire the shared lock used by cache readers and publishers."""

        if fcntl is None:
            raise OSError("deadline-aware cache publication requires POSIX file locks")
        lock_path = cls._lock_path_for(Path(path))
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        lock_file = lock_path.open("a+")
        try:
            mode = fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH
            if nonblocking:
                mode |= fcntl.LOCK_NB
            fcntl.flock(lock_file.fileno(), mode)
        except Exception:
            lock_file.close()
            raise
        return lock_file

    @staticmethod
    def _release_path_lock(lock_file: Any) -> None:
        if lock_file is None:
            return
        try:
            if fcntl is not None:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
        except Exception:
            pass
        try:
            lock_file.close()
        except Exception:
            pass

    @classmethod
    def _read_locked_text(cls, path: Path) -> str:
        lock_file = cls._acquire_path_lock(path, exclusive=False)
        try:
            return Path(path).read_text(encoding="utf-8")
        finally:
            cls._release_path_lock(lock_file)

    @classmethod
    def _read_trusted_locked_text(cls, path: Path) -> Optional[str]:
        """Read one source only while it remains publication-trusted.

        The disabled marker is written by a deadline rollback while holding
        this same path lock.  Checking it before waiting on the lock leaves a
        TOCTOU window: a reader can pass the check, block behind a receipt,
        then ingest a row after rollback has disabled the source.  Check the
        marker *after* the shared lock is acquired and read under that lock.
        ``None`` is a deliberate fail-closed rejection, distinct from an I/O
        failure.
        """

        snapshot = cls._read_trusted_locked_snapshot(path)
        return None if snapshot is None else snapshot[0]

    @classmethod
    def _read_trusted_locked_snapshot(
        cls,
        path: Path,
    ) -> Optional[Tuple[str, Tuple[int, int, int, int, int]]]:
        """Read trusted text and its exact opened-file identity under lock."""

        trusted_path = Path(path)
        lock_file = cls._acquire_path_lock(trusted_path, exclusive=False)
        try:
            if (
                not _deadline_publication_path_is_trusted(trusted_path)
                or cls._disabled_marker_path(trusted_path).exists()
            ):
                return None
            with trusted_path.open("r", encoding="utf-8") as source:
                stat = os.fstat(source.fileno())
                text = source.read()
            identity = (
                int(stat.st_dev),
                int(stat.st_ino),
                int(stat.st_size),
                int(stat.st_mtime_ns),
                int(stat.st_ctime_ns),
            )
            return text, identity
        finally:
            cls._release_path_lock(lock_file)

    def _quarantine_deadline_publication_failure(self, exc: BaseException) -> None:
        """Fail closed if a deadline-losing append cannot be truncated.

        A partial cache row must never become a future seed.  Under the
        receipt's exclusive lock, move the suspect JSONL aside and continue
        with an empty cache rather than leaving an ambiguous append in place.
        """

        self._record_store_failure(exc)
        quarantine = self.path.with_name(
            f"{self.path.name}.deadline-publication-quarantine-{time.time_ns()}"
        )
        quarantined = False
        try:
            if self.path.exists():
                os.replace(self.path, quarantine)
            self.path.touch(exist_ok=True)
            quarantined = True
        except Exception as quarantine_exc:
            self._record_store_failure(quarantine_exc)
        if not quarantined:
            self._disable_deadline_publication_cache(exc)
        self._by_exact_key.clear()
        self._by_canonical_statement.clear()
        self._by_theorem_name.clear()
        self._source_hashes.clear()
        self._advisory_source_keys.clear()
        self._owner_record_ids.clear()
        self._local_owner_record_ids.clear()
        # Quarantine replaces the owned file and clears every in-memory
        # index, including read-through rows.  Their cursors must be replayed
        # from zero; retaining any prior line count would skip replacement or
        # sibling rows when the empty indexes are rebuilt.
        self._read_path_line_counts.clear()
        self._read_path_snapshots.clear()

    def _index_stored_record(
        self,
        record: Dict[str, Any],
        owner_record_id: str,
    ) -> None:
        source_hash = str(record.get("source_hash") or "")
        preamble_hash = str(record.get("preamble_hash") or "")
        source_key = f"{source_hash}:{preamble_hash}"
        self._supersede_advisory_source_key(source_key, record)
        if source_key not in self._source_hashes:
            self._index_record(record)
            self._source_hashes.add(source_key)
        self._index_theorem_record(record)
        self._owner_record_ids.add(owner_record_id)
        self._local_owner_record_ids.add(owner_record_id)

    @classmethod
    def _record_origin_schema_version(
        cls,
        record: Dict[str, Any],
    ) -> Optional[int]:
        """Return the schema version this row's *content* was written under.

        ``None`` means the row is not migratable at all (unparseable, or from a
        future schema this build cannot interpret).  A row that has already
        been migrated once carries ``migrated_from_schema_version``; that
        origin wins over the rewritten ``schema_version`` so an advisory row
        stays advisory across merges and reloads.
        """

        try:
            declared = int(record.get("schema_version") or 0)
        except (TypeError, ValueError):
            return None
        if declared > cls.schema_version:
            # Fail closed on the future: a newer writer may rely on fields or
            # invariants this build does not implement.
            return None
        if declared < cls._MIN_MIGRATABLE_SCHEMA_VERSION:
            return None
        try:
            origin = int(record.get(cls._ORIGIN_SCHEMA_FIELD) or declared)
        except (TypeError, ValueError):
            origin = declared
        if origin < cls._MIN_MIGRATABLE_SCHEMA_VERSION:
            return None
        # Never let a marker upgrade a row's effective age.
        return min(origin, declared)

    @classmethod
    def _record_is_provenance_bearing(cls, record: Dict[str, Any]) -> bool:
        """True when this row may assert a replay dependency closure."""

        flag = record.get(cls._PROVENANCE_FLAG_FIELD)
        if flag is not None:
            return bool(flag)
        origin = cls._record_origin_schema_version(record)
        return origin is not None and origin >= cls._PROVENANCE_SCHEMA_VERSION

    def _evict_advisory_index_records(
        self,
        source_hash: str,
        preamble_hash: str,
    ) -> None:
        """Drop advisory copies of one body from both lookup tiers."""

        if not source_hash:
            return
        for index in (self._by_exact_key, self._by_canonical_statement):
            for key in list(index):
                bucket = index[key]
                kept = [
                    item
                    for item in bucket
                    if not (
                        str(item.get("source_hash") or "") == source_hash
                        and str(item.get("preamble_hash") or "") == preamble_hash
                        and item.get(self._PROVENANCE_FLAG_FIELD) is False
                    )
                ]
                if len(kept) != len(bucket):
                    index[key] = kept

    def _supersede_advisory_source_key(
        self,
        source_key: str,
        record: Dict[str, Any],
    ) -> None:
        """Let a provenance-bearing row replace the advisory copy it upgrades.

        Without this the advisory row would keep the ``_source_hashes`` slot
        and ``lookup`` could return the stripped copy in preference to the
        record that actually carries a replay closure.
        """

        if source_key not in self._advisory_source_keys:
            return
        self._evict_advisory_index_records(
            str(record.get("source_hash") or ""),
            str(record.get("preamble_hash") or ""),
        )
        self._advisory_source_keys.discard(source_key)
        self._source_hashes.discard(source_key)

    def _advisory_records_superseded_by(
        self,
        record: Mapping[str, Any],
    ) -> List[Dict[str, Any]]:
        """Snapshot advisory candidates displaced by an upgrade receipt."""

        source_hash = str(record.get("source_hash") or "")
        preamble_hash = str(record.get("preamble_hash") or "")
        source_key = f"{source_hash}:{preamble_hash}"
        if not source_hash or source_key not in self._advisory_source_keys:
            return []
        retained: Dict[Tuple[str, str], Dict[str, Any]] = {}
        for tier, index in (
            ("exact", self._by_exact_key),
            ("canonical", self._by_canonical_statement),
        ):
            for records in index.values():
                for candidate in records:
                    identity = (
                        str(candidate.get("source_hash") or ""),
                        str(candidate.get("preamble_hash") or ""),
                    )
                    if (
                        self._record_is_provenance_bearing(candidate)
                        or identity != (source_hash, preamble_hash)
                    ):
                        continue
                    saved = retained.setdefault(
                        identity,
                        _clone_cache_record(candidate),
                    )
                    tier_ranks = saved.setdefault(self._RESTORE_TIER_RANKS_FIELD, {})
                    tier_ranks[tier] = {
                        field_name: int(candidate.get(field_name) or 0)
                        for field_name in (
                            "_cache_hits",
                            "_cache_last_hit_seq",
                            "_cache_insert_seq",
                        )
                    }
        return list(retained.values())

    def _restore_advisory_records(
        self,
        records: Sequence[Mapping[str, Any]],
    ) -> None:
        """Restore candidates displaced by a receipt that later rolled back."""

        for raw_record in records:
            record = _clone_cache_record(raw_record)
            tier_ranks = record.pop(self._RESTORE_TIER_RANKS_FIELD, {})
            source_hash = str(record.get("source_hash") or "")
            preamble_hash = str(record.get("preamble_hash") or "")
            source_key = f"{source_hash}:{preamble_hash}"
            if not source_hash or source_key in self._source_hashes:
                continue
            self._index_record_context.append(
                (
                    (
                        source_hash,
                        preamble_hash,
                        str(record.get("statement_hash") or ""),
                    ),
                    set(tier_ranks) if tier_ranks else None,
                    tier_ranks,
                    True,
                )
            )
            try:
                self._index_record(record)
            finally:
                self._index_record_context.pop()
            self._source_hashes.add(source_key)
            self._advisory_source_keys.add(source_key)

    def _remove_owner_record_from_indexes(self, owner_record_id: str) -> None:
        """Remove one owner while preserving surviving lookup-tier state."""

        retained: List[Tuple[Dict[str, Any], bool]] = []
        seen: Set[str] = set()
        local_ids = set(self._local_owner_record_ids)
        for records in self._by_theorem_name.values():
            for raw_record in records:
                record = _clone_cache_record(raw_record)
                source_hash = str(record.get("source_hash") or text_hash(str(record.get("source") or "")))
                preamble_hash = str(record.get("preamble_hash") or "")
                record_id = self._owner_record_id(
                    source_hash,
                    preamble_hash,
                    str(record.get("theorem_name") or ""),
                )
                if record_id == owner_record_id or record_id in seen:
                    continue
                seen.add(record_id)
                retained.append((record, record_id in local_ids))

        surviving_authoritative_keys = {
            (
                str(record.get("source_hash") or text_hash(str(record.get("source") or ""))),
                str(record.get("preamble_hash") or ""),
            )
            for record, _local in retained
        }
        for index in (self._by_exact_key, self._by_canonical_statement):
            for key in list(index):
                index[key] = [
                    record
                    for record in index[key]
                    if not self._record_is_provenance_bearing(record)
                    or (
                        str(
                            record.get("source_hash")
                            or text_hash(str(record.get("source") or ""))
                        ),
                        str(record.get("preamble_hash") or ""),
                    )
                    in surviving_authoritative_keys
                ]
                if not index[key]:
                    del index[key]

        self._by_theorem_name.clear()
        self._owner_record_ids.clear()
        self._local_owner_record_ids.clear()
        self._source_hashes = {
            f"{str(record.get('source_hash') or text_hash(str(record.get('source') or '')))}:"
            f"{str(record.get('preamble_hash') or '')}"
            for index in (self._by_exact_key, self._by_canonical_statement)
            for records in index.values()
            for record in records
        }
        # A valid authoritative body may be capped out of both lookup tiers
        # while its theorem-owner memberships remain live. Keep that body
        # identity reserved so adding another owner cannot reinsert it as a
        # fresh lookup candidate and displace the currently served body.
        self._source_hashes.update(
            f"{source_hash}:{preamble_hash}"
            for source_hash, preamble_hash in surviving_authoritative_keys
        )
        self._advisory_source_keys = {
            f"{str(record.get('source_hash') or text_hash(str(record.get('source') or '')))}:"
            f"{str(record.get('preamble_hash') or '')}"
            for index in (self._by_exact_key, self._by_canonical_statement)
            for records in index.values()
            for record in records
            if not self._record_is_provenance_bearing(record)
        }
        for record, local in retained:
            source_hash = str(record.get("source_hash") or text_hash(str(record.get("source") or "")))
            preamble_hash = str(record.get("preamble_hash") or "")
            record_id = self._owner_record_id(
                source_hash,
                preamble_hash,
                str(record.get("theorem_name") or ""),
            )
            self._index_theorem_record(record)
            self._owner_record_ids.add(record_id)
            if local:
                self._local_owner_record_ids.add(record_id)

    def _prepare_store_record(
        self,
        helper_block: str,
        *,
        preamble: str,
        theorem_name: str,
        phase: str,
        support_names: Sequence[str] = (),
        support_source_hashes: Optional[Dict[str, str]] = None,
        replay_context_names: Sequence[str] = (),
        replay_context_source_hashes: Optional[Dict[str, str]] = None,
    ) -> Optional[Tuple[Dict[str, Any], str]]:
        source = str(helper_block or "").strip()
        name = helper_decl_name(source) or ""
        statement = helper_decl_statement(source)
        if not source or not name or not statement:
            return None
        if graph_statement_non_theorem_reason(statement):
            return None
        # Enforce this at the cache boundary, not only in the dossier-aware
        # publication adapters below.  ``store`` is public and several
        # maintenance/import paths ingest records without a live dossier; a
        # checked ``P -> P`` projection is useful local context but must never
        # become durable evidence or seed a later run.
        if verified_helper_is_premise_projection(source):
            return None
        if not classify_auxiliary_statement_quality(statement).cache_publishable:
            return None
        if _proof_state_helper_policy_rejection(
            source,
            expected_statement=statement,
        ):
            return None
        source_hash = text_hash(source)
        preamble_hash = text_hash(preamble)
        owner_record_id = self._owner_record_id(
            source_hash,
            preamble_hash,
            theorem_name,
        )
        normalized_statement = _normalize_cache_statement(statement)
        return (
            {
                "schema_version": self.schema_version,
                "name": name,
                "statement": normalized_statement,
                "statement_hash": text_hash(normalized_statement),
                "statement_preview": _compact_search_text(statement, limit=4000),
                "preamble_hash": preamble_hash,
                "source": source,
                "source_hash": source_hash,
                "theorem_name": str(theorem_name or ""),
                "phase": str(phase or ""),
                # Written explicitly (rather than inferred from the version)
                # so a consumer can demand a positive provenance receipt
                # instead of reading the *absence* of the advisory flag.
                self._PROVENANCE_FLAG_FIELD: True,
                "support_names": [
                    str(support_name or "").strip()
                    for support_name in support_names
                    if str(support_name or "").strip()
                    and str(support_name or "").strip() != name
                ],
                "support_source_hashes": {
                    str(support_name or "").strip(): str(
                        support_hash or ""
                    ).strip()
                    for support_name, support_hash in dict(
                        support_source_hashes or {}
                    ).items()
                    if str(support_name or "").strip()
                    and str(support_hash or "").strip()
                },
                "replay_context_names": [
                    str(context_name or "").strip()
                    for context_name in replay_context_names
                    if str(context_name or "").strip()
                    and str(context_name or "").strip() != name
                ],
                "replay_context_source_hashes": {
                    str(context_name or "").strip(): str(
                        context_hash or ""
                    ).strip()
                    for context_name, context_hash in dict(
                        replay_context_source_hashes or {}
                    ).items()
                    if str(context_name or "").strip()
                    and str(context_hash or "").strip()
                },
                "created_ts": time.time(),
            },
            owner_record_id,
        )

    @classmethod
    def default_path(cls) -> Path:
        return _PROJECT_ROOT / "runs" / "mini_prover_cache" / "verified_helpers.jsonl"

    def lookup(
        self,
        statement: str,
        *,
        preamble: str,
        max_hits: int = 3,
    ) -> List[Dict[str, Any]]:
        """Return matching cache records, Tier 1 then Tier 2.

        Tier 1 hits (same preamble) are returned first; Tier 2 hits
        (cross-preamble, same canonical statement) follow, deduplicated by
        ``source_hash``. The combined result is capped at ``max_hits``.

        Callers re-compile the returned bodies via
        ``_accept_proof_state_helper`` before treating them as proven, so
        cross-preamble candidates that don't compile are silently skipped.
        """

        if self._cache_is_disabled():
            return []
        cap = max(0, int(max_hits or 0))
        if cap <= 0:
            return []
        self.refresh_read_paths()
        selected = self._select_lookup_records(
            statement,
            preamble=preamble,
            cap=cap,
        )
        self._touch_index_records_preserving_order(
            [record for _tier, record in selected]
        )
        out: List[Dict[str, Any]] = []
        for tier, record in selected:
            copy = _clone_cache_record(record)
            # Tag the record so callers can attribute hits per tier without
            # recomputing the keys themselves.
            copy["_lookup_tier"] = tier
            out.append(copy)
        return out

    def _select_lookup_records(
        self,
        statement: str,
        *,
        preamble: str,
        cap: int,
    ) -> List[Tuple[str, Dict[str, Any]]]:
        """Select a capped Tier-1/Tier-2 batch without touching hit ranks."""

        exact_key = self._exact_key(statement, preamble=preamble)
        canonical_key = self._canonical_key(statement)
        seen_source_hashes: Set[str] = set()
        selected: List[Tuple[str, Dict[str, Any]]] = []
        for tier, index, key in (
            ("tier1", self._by_exact_key, exact_key),
            ("tier2", self._by_canonical_statement, canonical_key),
        ):
            for record in list(index.get(key, [])):
                source_hash = str(record.get("source_hash") or "")
                if source_hash in seen_source_hashes:
                    continue
                seen_source_hashes.add(source_hash)
                selected.append((tier, record))
                if len(selected) >= max(0, int(cap or 0)):
                    return selected
        return selected

    def records_for_theorem(
        self,
        theorem_name: str,
        *,
        max_records: int = 64,
        preamble: Optional[str] = None,
    ) -> List[Dict[str, Any]]:
        """Return cached helpers previously proved for ``theorem_name``.

        This is intentionally broader than ``lookup``: a new run of the same
        Putnam problem should start with the whole verified helper toolbox from
        prior attempts, not only helpers whose statements already match an
        open proof-state frontier node. Consumers must still re-kernel-check
        every returned helper under the current preamble before recording it.
        """

        if self._cache_is_disabled():
            return []
        name = str(theorem_name or "").strip()
        cap = max(0, int(max_records or 0))
        if not name or cap <= 0:
            return []
        self.refresh_read_paths()

        candidates = [
            _clone_cache_record(record)
            for record in list(self._by_theorem_name.get(name, ()) or ())
            # Same-problem rehydration reconstructs a replay dependency closure
            # below and reports ``_replay_closure_missing`` against it.  A
            # pre-provenance row has no closure to reconstruct, so admitting it
            # here would present "no dependencies" as an authoritative fact.
            # Those rows stay in the advisory ``lookup`` tier instead.
            if self._record_is_provenance_bearing(record)
        ]

        requested_preamble_hash = (
            text_hash(str(preamble or "")) if preamble is not None else ""
        )
        candidates.sort(
            key=lambda record: (
                -int(
                    bool(requested_preamble_hash)
                    and str(record.get("preamble_hash") or "")
                    == requested_preamble_hash
                ),
                -float(record.get("created_ts") or 0.0),
                str(record.get("name") or ""),
                str(record.get("source_hash") or ""),
            )
        )
        deduplicated_candidates: List[Dict[str, Any]] = []
        seen_source_hashes: Set[str] = set()
        for record in candidates:
            source_hash = str(record.get("source_hash") or "").strip()
            source = str(record.get("source") or "").strip()
            source_key = source_hash or text_hash(source)
            if not source_key or source_key in seen_source_hashes:
                continue
            seen_source_hashes.add(source_key)
            deduplicated_candidates.append(record)

        selected_fact_keys: Set[str] = set()
        ordered_fact_keys: List[str] = []
        for record in deduplicated_candidates:
            source = str(record.get("source") or "").strip()
            statement = helper_decl_statement(source)
            fact_key = canonicalize_lean_statement_for_identity(statement) or (
                str(record.get("source_hash") or "").strip() or text_hash(source)
            )
            if fact_key in selected_fact_keys:
                continue
            selected_fact_keys.add(fact_key)
            ordered_fact_keys.append(fact_key)
            if len(ordered_fact_keys) >= cap:
                break

        # The cap counts mathematical candidate facts, not proof bodies. Keep
        # every body for each selected fact in newest-first order so a stale or
        # environment-specific body cannot erase a viable fallback.
        selected: List[Dict[str, Any]] = []
        selected_source_keys: Set[str] = set()
        for record in deduplicated_candidates:
            source = str(record.get("source") or "").strip()
            statement = helper_decl_statement(source)
            fact_key = canonicalize_lean_statement_for_identity(statement) or (
                str(record.get("source_hash") or "").strip() or text_hash(source)
            )
            if fact_key not in selected_fact_keys:
                continue
            selected.append(record)
            selected_source_keys.add(
                str(record.get("source_hash") or "").strip() or text_hash(source)
            )

        records_by_name: Dict[str, List[Dict[str, Any]]] = {}
        for record in deduplicated_candidates:
            name_key = str(record.get("name") or "").strip() or helper_decl_name(
                str(record.get("source") or "")
            )
            if name_key:
                records_by_name.setdefault(name_key, []).append(record)
        pending = list(selected)
        for record in pending:
            replay_expected_hashes = {
                str(dependency_name or "").strip(): str(
                    source_hash or ""
                ).strip()
                for dependency_name, source_hash in dict(
                    record.get("replay_context_source_hashes") or {}
                ).items()
                if str(dependency_name or "").strip()
                and str(source_hash or "").strip()
            }
            support_expected_hashes = {
                str(dependency_name or "").strip(): str(
                    source_hash or ""
                ).strip()
                for dependency_name, source_hash in dict(
                    record.get("support_source_hashes") or {}
                ).items()
                if str(dependency_name or "").strip()
                and str(source_hash or "").strip()
            }
            conflicting_expected_hash_names = {
                str(name or "").strip()
                for name in set(support_expected_hashes).intersection(
                    replay_expected_hashes
                )
                if str(name or "").strip()
                and str(support_expected_hashes.get(name) or "").strip()
                and str(replay_expected_hashes.get(name) or "").strip()
                and str(support_expected_hashes.get(name) or "").strip()
                != str(replay_expected_hashes.get(name) or "").strip()
            }
            expected_hashes = {
                **support_expected_hashes,
                **replay_expected_hashes,
            }
            source = str(record.get("source") or "").strip()
            record_name = str(record.get("name") or "").strip() or helper_decl_name(
                source
            )
            dependency_names = {
                str(raw_name or "").strip()
                for raw_name in (
                    list(record.get("support_names") or [])
                    + list(record.get("replay_context_names") or [])
                )
                if str(raw_name or "").strip()
            }
            # A durable exact-source receipt is itself dependency evidence.
            # Do not silently discard it merely because an older/partial row
            # omitted the parallel ordered-name field.
            dependency_names.update(support_expected_hashes)
            dependency_names.update(replay_expected_hashes)
            dependency_names.update(
                lean_referenced_helper_names(
                    source,
                    tuple(records_by_name),
                    skip=record_name,
                    allow_arbitrary_dot_methods=True,
                )
            )
            dependency_names.discard(str(record_name or "").strip())
            replay_names = [
                str(raw_name or "").strip()
                for raw_name in list(record.get("replay_context_names") or [])
                if str(raw_name or "").strip()
            ]
            for dependency_name in sorted(dependency_names):
                if dependency_name not in replay_names:
                    replay_names.append(dependency_name)
            record["replay_context_names"] = replay_names
            missing_closure: List[Dict[str, str]] = []
            for dependency_name in sorted(dependency_names):
                if dependency_name in conflicting_expected_hash_names:
                    missing_closure.append(
                        {
                            "name": dependency_name,
                            "expected_source_hash": "",
                            "reason": (
                                "conflicting_dependency_source_receipts"
                            ),
                        }
                    )
                    continue
                options = records_by_name.get(dependency_name, [])
                expected_hash = str(expected_hashes.get(dependency_name) or "").strip()
                dependencies = (
                    [
                        option
                        for option in options
                        if str(option.get("source_hash") or "").strip()
                        == expected_hash
                    ]
                    if expected_hash
                    else list(options)
                )
                if not dependencies:
                    missing_closure.append(
                        {
                            "name": dependency_name,
                            "expected_source_hash": expected_hash,
                            "reason": (
                                "exact_dependency_source_missing"
                                if expected_hash
                                else "dependency_source_missing"
                            ),
                        }
                    )
                    continue
                for dependency in dependencies:
                    dependency_source = str(
                        dependency.get("source") or ""
                    ).strip()
                    source_key = (
                        str(dependency.get("source_hash") or "").strip()
                        or text_hash(dependency_source)
                    )
                    if not source_key or source_key in selected_source_keys:
                        continue
                    selected_source_keys.add(source_key)
                    selected.append(dependency)
                    pending.append(dependency)
            if missing_closure:
                record["_replay_closure_missing"] = missing_closure
            else:
                record.pop("_replay_closure_missing", None)

        # Closure discovery order depends on graph traversal. Return records in
        # the cache's deterministic newest/exact-preamble ordering so fallback
        # preference remains stable regardless of which body referenced them.
        ordered_selected = [
            record
            for record in deduplicated_candidates
            if (
                str(record.get("source_hash") or "").strip()
                or text_hash(str(record.get("source") or "").strip())
            )
            in selected_source_keys
        ]
        self._touch_index_records_preserving_order(ordered_selected)
        out: List[Dict[str, Any]] = []
        for record in ordered_selected:
            copied = _clone_cache_record(record)
            copied["_lookup_tier"] = "same_theorem"
            out.append(copied)
        return out

    def retrieval_records(self, *, max_records: int = 50_000) -> List[Dict[str, Any]]:
        """Return unique verified bodies for semantic discovery.

        These rows are *candidates*, not certificates in the caller's current
        environment.  Retrieval consumers must re-kernel-check ``source``
        before making a declaration available to proof generation.  Keeping
        this boundary on the cache avoids exposing its private indexes to the
        federated retrieval service while preserving the cache's fail-closed
        disabled-marker and incremental refresh semantics.
        """

        if self._cache_is_disabled():
            return []
        cap = max(0, int(max_records or 0))
        if cap <= 0:
            return []
        self.refresh_read_paths()
        candidates: List[Dict[str, Any]] = []
        seen_source_hashes: Set[str] = set()
        for statement_hash in sorted(self._by_canonical_statement):
            for raw_record in self._by_canonical_statement[statement_hash]:
                record = _clone_cache_record(raw_record)
                source = str(record.get("source") or "").strip()
                source_hash = str(record.get("source_hash") or "").strip()
                identity = source_hash or text_hash(source)
                if not source or not identity or identity in seen_source_hashes:
                    continue
                seen_source_hashes.add(identity)
                candidates.append(record)
        candidates.sort(
            key=lambda record: (
                -float(record.get("created_ts") or 0.0),
                str(record.get("name") or ""),
                str(record.get("source_hash") or ""),
            )
        )
        return candidates[:cap]

    @staticmethod
    def _owner_record_id(
        source_hash: str,
        preamble_hash: str,
        theorem_name: str,
    ) -> str:
        """Return the persistence identity for one body-owner membership."""

        return ":".join(
            (
                str(source_hash or ""),
                str(preamble_hash or ""),
                str(theorem_name or "").strip(),
            )
        )

    def _index_theorem_record(self, record: Dict[str, Any]) -> None:
        theorem_name = str(record.get("theorem_name") or "").strip()
        if not theorem_name:
            return
        self._by_theorem_name.setdefault(theorem_name, []).append(
            _clone_cache_record(record)
        )

    def store(
        self,
        helper_block: str,
        *,
        preamble: str,
        theorem_name: str,
        phase: str,
        support_names: Sequence[str] = (),
        support_source_hashes: Optional[Dict[str, str]] = None,
        replay_context_names: Sequence[str] = (),
        replay_context_source_hashes: Optional[Dict[str, str]] = None,
    ) -> bool:
        if self._cache_is_disabled():
            return False
        prepared = self._prepare_store_record(
            helper_block,
            preamble=preamble,
            theorem_name=theorem_name,
            phase=phase,
            support_names=support_names,
            support_source_hashes=support_source_hashes,
            replay_context_names=replay_context_names,
            replay_context_source_hashes=replay_context_source_hashes,
        )
        if prepared is None:
            return False
        record, owner_record_id = prepared
        try:
            lock_file = self._acquire_path_lock(self.path, exclusive=True)
            try:
                # A rollback can write this marker while store() waits for
                # the lock.  Recheck while holding it, before append/index.
                if self._cache_is_disabled():
                    return False
                if owner_record_id in self._local_owner_record_ids:
                    return False
                with self.path.open("a", encoding="utf-8") as fp:
                    fp.write(json.dumps(record, ensure_ascii=False) + "\n")
            finally:
                self._release_path_lock(lock_file)
        except Exception as exc:
            # B3 fix (2026-05-11): record the failure observably so the
            # summary writer can surface it. Without this trace, callers
            # who ignore the False return (all 5 production sites) would
            # silently lose cross-problem cache reuse for this helper.
            self._record_store_failure(exc)
            return False
        self._index_stored_record(record, owner_record_id)
        return True

    def begin_deadline_aware_store(
        self,
        helper_block: str,
        *,
        preamble: str,
        theorem_name: str,
        phase: str,
        support_names: Sequence[str] = (),
        support_source_hashes: Optional[Dict[str, str]] = None,
        replay_context_names: Sequence[str] = (),
        replay_context_source_hashes: Optional[Dict[str, str]] = None,
        deadline_exhausted: Callable[[], bool],
    ) -> Optional[DeadlineAwareCachePublication]:
        """Reserve a reversible publication receipt for an elapsed turn.

        Returning ``None`` means the cache has nothing publishable (or cannot
        be safely locked); the caller may still accept its already verified
        helper because cache persistence is advisory.
        """

        if self._cache_is_disabled():
            return None
        prepared = self._prepare_store_record(
            helper_block,
            preamble=preamble,
            theorem_name=theorem_name,
            phase=phase,
            support_names=support_names,
            support_source_hashes=support_source_hashes,
            replay_context_names=replay_context_names,
            replay_context_source_hashes=replay_context_source_hashes,
        )
        if prepared is None:
            return None
        record, owner_record_id = prepared
        try:
            lock_file = self._acquire_path_lock(
                self.path,
                exclusive=True,
                nonblocking=True,
            )
        except Exception as exc:
            # Cache publication is advisory.  An elapsed turn must never
            # block its event loop behind another process's cache receipt.
            if not isinstance(exc, BlockingIOError):
                self._record_store_failure(exc)
            return None
        # The new receipt owns this exclusive lock until its enclosing
        # transaction seals it.  Recheck under the lock to close the
        # wait-behind-rollback marker race.
        if self._cache_is_disabled() or owner_record_id in self._local_owner_record_ids:
            self._release_path_lock(lock_file)
            return None
        return DeadlineAwareCachePublication(
            cache=self,
            record=record,
            owner_record_id=owner_record_id,
            deadline_exhausted=deadline_exhausted,
            lock_file=lock_file,
        )

    # ------------------------------------------------------------------
    # Index keys.
    # ------------------------------------------------------------------

    @staticmethod
    def _exact_key(statement: str, *, preamble: str) -> str:
        """Tier 1: (canonical_stmt_hash, preamble_hash)."""

        normalized_statement = _normalize_cache_statement(statement)
        return f"{text_hash(normalized_statement)}:{text_hash(preamble)}"

    @staticmethod
    def _canonical_key(statement: str) -> str:
        """Tier 2: canonical_stmt_hash alone (cross-preamble fallback)."""

        return text_hash(_normalize_cache_statement(statement))

    # Legacy alias retained for any external caller.
    @staticmethod
    def _key(statement: str, *, preamble: str) -> str:
        return MiniVerifiedLemmaCache._exact_key(statement, preamble=preamble)

    # Per-bucket caps: Tier 1 bucket holds records for ONE
    # (canonical_stmt, preamble) — at most a handful of distinct
    # bodies for the same fact under the same preamble is realistic.
    # Tier 2 bucket holds records for ONE canonical statement across
    # ALL preambles ever seen — for popular generic lemmas this can
    # be much wider, so the cap is higher.
    _TIER1_BUCKET_CAP = 8
    _TIER2_BUCKET_CAP = 64

    def _next_access_seq(self) -> int:
        self._cache_access_seq += 1
        return self._cache_access_seq

    @staticmethod
    def _cache_record_rank(record: Dict[str, Any]) -> Tuple[int, int, int, float]:
        return (
            int(record.get("_cache_hits") or 0),
            int(record.get("_cache_last_hit_seq") or 0),
            int(record.get("_cache_insert_seq") or 0),
            float(record.get("created_ts") or 0.0),
        )

    def _trim_cache_bucket(self, bucket: List[Dict[str, Any]], cap: int) -> None:
        bucket.sort(key=self._cache_record_rank, reverse=True)
        del bucket[max(0, int(cap or 0)) :]

    def _runtime_rank_snapshot(
        self,
    ) -> Dict[str, Dict[Tuple[str, str, str], Dict[str, int]]]:
        """Capture rank and membership independently for each lookup tier."""

        snapshot: Dict[str, Dict[Tuple[str, str, str], Dict[str, int]]] = {
            "exact": {},
            "canonical": {},
        }
        for tier, index in (
            ("exact", self._by_exact_key),
            ("canonical", self._by_canonical_statement),
        ):
            for records in index.values():
                for record in records:
                    identity = (
                        str(record.get("source_hash") or ""),
                        str(record.get("preamble_hash") or ""),
                        str(record.get("statement_hash") or ""),
                    )
                    if not all(identity):
                        continue
                    rank = {
                        field_name: int(record.get(field_name) or 0)
                        for field_name in (
                            "_cache_hits",
                            "_cache_last_hit_seq",
                            "_cache_insert_seq",
                        )
                    }
                    prior = snapshot[tier].get(identity)
                    if prior is None or tuple(rank.values()) > tuple(prior.values()):
                        snapshot[tier][identity] = rank
        return snapshot

    def _apply_runtime_rank_snapshot(
        self,
        snapshot: Mapping[
            str,
            Mapping[Tuple[str, str, str], Mapping[str, int]],
        ],
    ) -> None:
        """Restore survivor tier membership/ranks, then enforce tier caps."""

        known_identities = {
            identity
            for tier_snapshot in snapshot.values()
            for identity in tier_snapshot
        }
        for tier, index, cap in (
            ("exact", self._by_exact_key, self._TIER1_BUCKET_CAP),
            ("canonical", self._by_canonical_statement, self._TIER2_BUCKET_CAP),
        ):
            tier_snapshot = snapshot.get(tier, {})
            for key in list(index):
                bucket = index[key]
                bucket[:] = [
                    record
                    for record in bucket
                    if (
                        (
                            str(record.get("source_hash") or ""),
                            str(record.get("preamble_hash") or ""),
                            str(record.get("statement_hash") or ""),
                        )
                        not in known_identities
                        or (
                            str(record.get("source_hash") or ""),
                            str(record.get("preamble_hash") or ""),
                            str(record.get("statement_hash") or ""),
                        )
                        in tier_snapshot
                    )
                ]
                for record in bucket:
                    identity = (
                        str(record.get("source_hash") or ""),
                        str(record.get("preamble_hash") or ""),
                        str(record.get("statement_hash") or ""),
                    )
                    rank = tier_snapshot.get(identity)
                    if rank is not None:
                        record.update(rank)
                        self._cache_access_seq = max(
                            self._cache_access_seq,
                            int(rank.get("_cache_last_hit_seq") or 0),
                            int(rank.get("_cache_insert_seq") or 0),
                        )
                self._trim_cache_bucket(bucket, cap)
                if not bucket:
                    del index[key]

    def _touch_index_record(self, record: Dict[str, Any]) -> None:
        self._touch_index_records_preserving_order([record])

    def _touch_index_records_preserving_order(
        self,
        records: Sequence[Mapping[str, Any]],
    ) -> None:
        """Touch one selected batch without permuting its service order."""

        valid: List[Tuple[str, str, str]] = []
        seen: Set[Tuple[str, str, str]] = set()
        for record in records:
            identity = (
                str(record.get("source_hash") or ""),
                str(record.get("preamble_hash") or ""),
                str(record.get("statement_hash") or ""),
            )
            if not all(identity) or identity in seen:
                continue
            seen.add(identity)
            valid.append(identity)
        if not valid:
            return

        access_sequences = [self._next_access_seq() for _item in valid]
        affected: Dict[int, Tuple[List[Dict[str, Any]], int]] = {}
        for (source_hash, preamble_hash, statement_hash), access_seq in zip(
            valid,
            reversed(access_sequences),
        ):
            exact_key = f"{statement_hash}:{preamble_hash}"
            for bucket, cap in (
                (
                    self._by_exact_key.get(exact_key, []),
                    self._TIER1_BUCKET_CAP,
                ),
                (
                    self._by_canonical_statement.get(statement_hash, []),
                    self._TIER2_BUCKET_CAP,
                ),
            ):
                touched = False
                for candidate in bucket:
                    if (
                        str(candidate.get("source_hash") or "") == source_hash
                        and str(candidate.get("preamble_hash") or "")
                        == preamble_hash
                    ):
                        candidate["_cache_hits"] = (
                            int(candidate.get("_cache_hits") or 0) + 1
                        )
                        candidate["_cache_last_hit_seq"] = access_seq
                        touched = True
                if touched:
                    affected[id(bucket)] = (bucket, cap)
        for bucket, cap in affected.values():
            self._trim_cache_bucket(bucket, cap)

    def _index_record(
        self,
        record: Dict[str, Any],
    ) -> None:
        """Insert ``record`` into both Tier 1 and Tier 2 buckets, with
        hit-aware per-tier caps (8 / 64). The Tier 2 cap is higher because a
        popular canonical statement may have been proven under many
        problem-specific preambles; capping at 8 silently evicts
        cross-problem witnesses (defect surfaced by adversarial review,
        2026-05-08). Hot entries are retained by lookup count with recency
        as the tie-breaker, so a useful cross-problem witness is not displaced
        by a stream of cold variants."""

        statement = str(record.get("statement") or "")
        preamble_hash = str(record.get("preamble_hash") or "")
        statement_hash = str(record.get("statement_hash") or "") or text_hash(statement)
        if not statement or not preamble_hash or not statement_hash:
            return
        exact_key = f"{statement_hash}:{preamble_hash}"
        canonical_key = statement_hash
        if self._index_record_context:
            target_identity, tiers, tier_runtime_ranks, preserve_runtime_rank = (
                self._index_record_context[-1]
            )
            if target_identity != (
                str(record.get("source_hash") or ""),
                preamble_hash,
                statement_hash,
            ):
                tiers = None
                tier_runtime_ranks = None
                preserve_runtime_rank = False
        else:
            tiers = None
            tier_runtime_ranks = None
            preserve_runtime_rank = False
        trim = not self._defer_cache_bucket_trim
        for tier, index, key, cap in (
            ("exact", self._by_exact_key, exact_key, self._TIER1_BUCKET_CAP),
            (
                "canonical",
                self._by_canonical_statement,
                canonical_key,
                self._TIER2_BUCKET_CAP,
            ),
        ):
            if tiers is not None and tier not in tiers:
                continue
            bucket = index.setdefault(key, [])
            indexed = _clone_cache_record(record)
            if tier_runtime_ranks is not None:
                indexed.update(tier_runtime_ranks.get(tier, {}))
            indexed.setdefault("_cache_hits", 0)
            indexed.setdefault("_cache_last_hit_seq", 0)
            if preserve_runtime_rank and "_cache_insert_seq" in indexed:
                self._cache_access_seq = max(
                    self._cache_access_seq,
                    int(indexed.get("_cache_insert_seq") or 0),
                )
            else:
                indexed["_cache_insert_seq"] = self._next_access_seq()
            bucket.append(indexed)
            if trim:
                self._trim_cache_bucket(bucket, cap)

    def _record_ingest_keys(
        self,
        record: Dict[str, Any],
        *,
        dedupe_owner_records: bool = True,
    ) -> Optional[Tuple[str, str, str, str, Dict[str, Any]]]:
        """Return migrated index keys and record for a cache row, or None.

        ``source_key`` preserves global body de-duplication for lookup;
        ``owner_record_id`` preserves independent same-theorem membership.
        ``exact_key`` and ``canonical_key`` are the Tier 1 and Tier 2 index
        keys. Rows loaded from older schema files may carry a stale
        normalized statement or statement hash; migrate those fields through
        the current normalizer before indexing or appending them.  Rows written
        before ``_PROVENANCE_SCHEMA_VERSION`` are migrated into the advisory
        tier: their provenance fields are stripped and the migrated record is
        flagged, because that provenance cannot be re-derived from source text.
        Only a future schema is rejected outright, and every rejection is
        counted so a bump is never a silent empty index.
        """

        origin_schema_version = self._record_origin_schema_version(record)
        if origin_schema_version is None:
            self._note_ingest(
                "schema_rejected",
                f"schema_unmigratable v{record.get('schema_version')!r}",
            )
            return None
        source = str(record.get("source") or "").strip()
        (
            semantic_rejection,
            source_statement,
            statement,
            source_hash,
            statement_hash,
        ) = _cached_semantic_record_analysis(
            source,
            str(record.get("statement") or ""),
        )
        preamble_hash = str(record.get("preamble_hash") or "").strip()
        if not source or not statement or not preamble_hash or not source_hash:
            self._note_ingest("field_rejected", "missing source/statement/preamble")
            return None
        if semantic_rejection == "non_theorem":
            self._note_ingest("field_rejected", "non_theorem_statement")
            return None
        # Re-evaluate old and externally-produced rows on ingestion so caches
        # written before the premise-projection quality tag existed cannot
        # bypass the current publication invariant on reload/read-through.
        if semantic_rejection == "projection_rejected":
            self._note_ingest("projection_rejected", "premise_projection")
            return None
        if semantic_rejection == "quality_rejected":
            self._note_ingest("quality_rejected", "auxiliary_quality")
            return None
        if semantic_rejection == "policy_rejected":
            self._note_ingest("policy_rejected", "helper_policy")
            return None
        if semantic_rejection:
            self._note_ingest("field_rejected", semantic_rejection)
            return None
        source_key = f"{source_hash}:{preamble_hash}"
        theorem_name = str(record.get("theorem_name") or "").strip()
        owner_record_id = self._owner_record_id(
            source_hash,
            preamble_hash,
            theorem_name,
        )
        if dedupe_owner_records and owner_record_id in self._owner_record_ids:
            self._note_ingest("owner_deduped", theorem_name or source_key)
            return None
        exact_key = f"{statement_hash}:{preamble_hash}"
        canonical_key = statement_hash
        migrated = _clone_cache_record(record)
        migrated["statement"] = statement
        migrated["statement_hash"] = statement_hash
        migrated["source_hash"] = source_hash
        migrated["theorem_name"] = theorem_name
        provenance_bearing = (
            origin_schema_version >= self._PROVENANCE_SCHEMA_VERSION
        )
        migrated[self._PROVENANCE_FLAG_FIELD] = provenance_bearing
        if origin_schema_version != self.schema_version:
            migrated[self._ORIGIN_SCHEMA_FIELD] = origin_schema_version
        if provenance_bearing:
            migrated["schema_version"] = self.schema_version
        else:
            # ``merge_records_from_path`` persists this dict.  Keep the
            # original version on an advisory row so a build without this
            # migration still fails closed on it instead of reading the
            # rewritten version as "current" and trusting its empty closure.
            migrated["schema_version"] = origin_schema_version
            for provenance_field in self._PROVENANCE_FIELDS:
                migrated.pop(provenance_field, None)
        return exact_key, canonical_key, source_key, owner_record_id, migrated

    def _ingest_record(self, record: Dict[str, Any], *, local: bool = False) -> bool:
        keys = self._record_ingest_keys(
            record,
            dedupe_owner_records=not local,
        )
        if keys is None:
            return False
        _exact_key, _canonical_key, source_key, owner_record_id, migrated = keys
        provenance_bearing = self._record_is_provenance_bearing(migrated)
        if provenance_bearing:
            if owner_record_id in self._owner_record_ids:
                # The non-local path already counted this in
                # _record_ingest_keys' dedupe_owner_records check.
                if local:
                    self._note_ingest(
                        "owner_deduped",
                        str(migrated.get("theorem_name") or source_key),
                    )
                return False
            self._supersede_advisory_source_key(source_key, migrated)
        already_indexed = source_key in self._source_hashes
        if not already_indexed:
            # Use _index_record so both tiers stay in sync. Pass a fresh copy to
            # protect the on-disk record from later in-memory mutations.
            self._index_record(migrated)
            self._source_hashes.add(source_key)
            if not provenance_bearing:
                self._advisory_source_keys.add(source_key)
        if not provenance_bearing:
            # Advisory tier: a reusable candidate body for statement lookup and
            # retrieval, but it holds no owner slot -- taking one would block
            # the republication that upgrades it -- and it is never added to
            # the same-theorem toolbox that reconstructs replay closures.
            self._note_ingest("schema_advisory")
            return True
        self._index_theorem_record(migrated)
        self._owner_record_ids.add(owner_record_id)
        if local:
            self._local_owner_record_ids.add(owner_record_id)
        self._count_schema_migration_if_needed(record)
        return True

    def merge_records_from_path(self, path: Path) -> int:
        self.last_merge_errors = []
        if self._cache_is_disabled():
            return 0
        merge_path = Path(path)
        try:
            if merge_path.resolve() == self.path.resolve():
                return 0
        except Exception:
            if merge_path == self.path:
                return 0
        if not merge_path.exists():
            return 0
        merged = 0
        try:
            trusted_text = self._read_trusted_locked_text(merge_path)
        except Exception as exc:
            self.last_merge_errors.append(
                f"{merge_path}: read failed: {type(exc).__name__}: {exc}"
            )
            return 0
        if trusted_text is None:
            self.last_merge_errors.append(
                f"{merge_path}: skipped deadline-publication-disabled cache source"
            )
            return 0
        lines = trusted_text.splitlines()
        for line_no, line in enumerate(lines, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except Exception as exc:
                preview = line.strip().replace("\n", " ")[:160]
                self.last_merge_errors.append(
                    f"{merge_path}:{line_no}: invalid JSON: "
                    f"{type(exc).__name__}: {exc}; preview={preview!r}"
                )
                continue
            if not isinstance(record, dict):
                continue
            keys = self._record_ingest_keys(
                record,
                dedupe_owner_records=False,
            )
            if keys is None:
                continue
            _exact_key, _canonical_key, source_key, owner_record_id, migrated = keys
            if owner_record_id in self._owner_record_ids:
                self._note_ingest(
                    "owner_deduped",
                    str(migrated.get("theorem_name") or source_key),
                )
                continue
            try:
                lock_file = self._acquire_path_lock(self.path, exclusive=True)
                try:
                    # Source trust is checked under its own lock above.  The
                    # destination can independently become fail-closed while
                    # this merge waits here, so decide destination trust while
                    # holding its append lock and do not index a rejected row.
                    if self._cache_is_disabled():
                        self.last_merge_errors.append(
                            f"{self.path}: destination disabled during merge"
                        )
                        break
                    with self.path.open("a", encoding="utf-8") as fp:
                        fp.write(json.dumps(migrated, ensure_ascii=False) + "\n")
                finally:
                    self._release_path_lock(lock_file)
            except Exception as exc:
                self.last_merge_errors.append(
                    f"{merge_path}:{line_no}: append failed: "
                    f"{type(exc).__name__}: {exc}"
                )
                continue
            provenance_bearing = self._record_is_provenance_bearing(migrated)
            if provenance_bearing:
                self._supersede_advisory_source_key(source_key, migrated)
            if source_key not in self._source_hashes:
                self._index_record(migrated)
                self._source_hashes.add(source_key)
                if not provenance_bearing:
                    self._advisory_source_keys.add(source_key)
            if provenance_bearing:
                self._index_theorem_record(migrated)
                self._owner_record_ids.add(owner_record_id)
                self._local_owner_record_ids.add(owner_record_id)
                self._count_schema_migration_if_needed(record)
            else:
                self._note_ingest("schema_advisory")
            merged += 1
        return merged

    def refresh_read_paths(self) -> int:
        """Ingest records appended to configured read-through cache paths."""

        if self._cache_is_disabled():
            return 0
        loaded = 0
        for read_path in self._read_paths:
            loaded += self._load_new_records(Path(read_path))
        return loaded

    def _clear_indexes_for_storage_reload(self) -> None:
        """Clear derived state before replaying every configured source."""

        self._by_exact_key.clear()
        self._by_canonical_statement.clear()
        self._by_theorem_name.clear()
        self._source_hashes.clear()
        self._advisory_source_keys.clear()
        self._owner_record_ids.clear()
        self._local_owner_record_ids.clear()
        self._read_path_line_counts.clear()
        self._read_path_snapshots.clear()

    def _reload_all_storage(self) -> int:
        """Rebuild indexes after a read-through source was replaced."""

        # An overridable ingestion hook may inspect or refresh the same cache.
        # The outer reload already owns the complete pre-clear rank snapshot
        # and will visit every configured source, so a nested rebuild must not
        # clear its partially reconstructed indexes or reset trim policy.
        if self._storage_reload_depth > 0:
            return 0
        lookup_ranks = self._runtime_rank_snapshot()
        loaded = 0
        self._storage_reload_depth += 1
        try:
            self._clear_indexes_for_storage_reload()
            self._defer_cache_bucket_trim = True
            for read_path in self._read_paths:
                loaded += self._load_new_records(
                    Path(read_path),
                    rebuild_on_replacement=False,
                )
            self._load(self.path)
        finally:
            self._defer_cache_bucket_trim = False
            self._storage_reload_depth -= 1
        self._apply_runtime_rank_snapshot(lookup_ranks)
        return loaded

    def _load_new_records(
        self,
        path: Path,
        *,
        rebuild_on_replacement: bool = True,
    ) -> int:
        if self._cache_is_disabled():
            return 0
        load_path = Path(path)
        key = self._read_path_key(load_path)
        if not load_path.exists():
            return 0
        try:
            trusted_snapshot = self._read_trusted_locked_snapshot(load_path)
        except Exception:
            return 0
        if trusted_snapshot is None:
            return 0
        trusted_text, snapshot = trusted_snapshot
        lines = trusted_text.splitlines()
        start = int(self._read_path_line_counts.get(key, 0) or 0)
        previous_snapshot = self._read_path_snapshots.get(key)
        replaced = bool(
            previous_snapshot is not None
            and (
                snapshot[:2] != previous_snapshot[:2]
                or snapshot[2] < previous_snapshot[2]
                or (
                    snapshot[2] == previous_snapshot[2]
                    and snapshot[3:] != previous_snapshot[3:]
                )
            )
        )
        if replaced and rebuild_on_replacement:
            return self._reload_all_storage()
        if replaced:
            start = 0
        if start > len(lines):
            start = 0
        loaded = 0
        next_start = start
        for line_no, line in enumerate(lines[start:], start=start):
            if not line.strip():
                next_start += 1
                continue
            try:
                record = json.loads(line)
            except Exception:
                if line_no >= len(lines) - 1:
                    break
                next_start += 1
                continue
            next_start += 1
            if not isinstance(record, dict):
                continue
            if self._ingest_record(record):
                loaded += 1
        self._read_path_line_counts[key] = next_start
        self._read_path_snapshots[key] = snapshot
        return loaded

    def _load(self, path: Path) -> None:
        if self._cache_is_disabled():
            return
        load_path = Path(path)
        if not load_path.exists():
            return
        try:
            trusted_snapshot = self._read_trusted_locked_snapshot(load_path)
        except Exception:
            return
        if trusted_snapshot is None:
            return
        trusted_text, snapshot = trusted_snapshot
        lines = trusted_text.splitlines()
        key = self._read_path_key(load_path)
        next_start = 0
        for line_no, line in enumerate(lines):
            if not line.strip():
                next_start += 1
                continue
            try:
                record = json.loads(line)
            except Exception:
                # A concurrently staged final row may be incomplete.  Keep
                # its cursor pending so a later refresh can ingest it once the
                # append becomes complete.
                if line_no >= len(lines) - 1:
                    break
                next_start += 1
                continue
            next_start += 1
            if not isinstance(record, dict):
                continue
            self._ingest_record(record, local=True)
        self._read_path_line_counts[key] = next_start
        self._read_path_snapshots[key] = snapshot


def cache_owner_theorem_name(dossier: Any) -> str:
    """Resolve the root theorem namespace for durable helper publication.

    Recursive child dossiers retain their local theorem names for Lean and
    graph execution.  Their inherited cache owner points at the root problem,
    which is the exact namespace queried by same-problem cache seeding.
    """

    return str(
        getattr(dossier, "cache_owner_theorem_name", "")
        or getattr(dossier, "theorem_name", "")
        or ""
    ).strip()


def store_verified_helper_for_dossier(
    proof_cache: Any,
    helper_block: str,
    *,
    preamble: str,
    dossier: Any,
    phase: str,
) -> bool:
    """Publish one helper only through its durable dossier owner.

    The helper must already have passed the dossier's policy/quality gate.  A
    child dossier is intentionally non-publishing until its parent accepts the
    helper, preventing transient recursive artifacts from becoming seeds for a
    later root run.
    """

    if proof_cache is None or dossier is None:
        return False
    if not bool(getattr(dossier, "proof_cache_publish_enabled", True)):
        return False
    owner = cache_owner_theorem_name(dossier)
    source = str(helper_block or "").strip()
    if not owner or not source:
        return False
    # ``record_verified_helper`` retains certain advisory certificates for
    # diagnostics/graph bookkeeping even when they are deliberately withheld
    # from usable proof context.  Cache seeding must obey the same quality
    # boundary as a live session, so direct writers fail closed unless the
    # owning dossier exposes this exact helper as visible.
    visible = getattr(dossier, "is_verified_helper_context_visible", None)
    if not callable(visible):
        return False
    helper_name = helper_decl_name(source)
    if not helper_name:
        return False
    try:
        if not bool(visible(helper_name)):
            return False
    except Exception:
        return False
    helper = (getattr(dossier, "verified_helpers", {}) or {}).get(helper_name)
    if verified_helper_is_premise_projection(helper or source):
        return False
    if not classify_auxiliary_statement_quality(
        helper_decl_statement(source)
    ).cache_publishable:
        return False
    try:
        store = proof_cache.store
        kwargs: Dict[str, Any] = {
            "preamble": str(preamble or ""),
            "theorem_name": owner,
            "phase": str(phase or ""),
        }
        try:
            parameters = inspect.signature(store).parameters
            accepts_extra_kwargs = any(
                parameter.kind is inspect.Parameter.VAR_KEYWORD
                for parameter in parameters.values()
            )
        except (TypeError, ValueError):
            parameters = {}
            accepts_extra_kwargs = True
        if helper is not None:
            provenance_values = {
                "support_names": list(
                    getattr(helper, "support_names", []) or []
                ),
                "support_source_hashes": dict(
                    getattr(helper, "support_source_hashes", {}) or {}
                ),
                "replay_context_names": list(
                    getattr(helper, "replay_context_names", []) or []
                ),
                "replay_context_source_hashes": dict(
                    getattr(helper, "replay_context_source_hashes", {}) or {}
                ),
            }
            for parameter_name, value in provenance_values.items():
                if accepts_extra_kwargs or parameter_name in parameters:
                    kwargs[parameter_name] = value
        return bool(store(source, **kwargs))
    except Exception:
        # The cache already records its own I/O failures.  This defensive
        # boundary also keeps third-party/test cache adapters from breaking a
        # verified proof path.
        return False


def stage_verified_helper_for_dossier(
    proof_cache: Any,
    helper_block: str,
    *,
    preamble: str,
    dossier: Any,
    phase: str,
    deadline_exhausted: Callable[[], bool],
) -> Optional[DeadlineAwareCachePublication]:
    """Stage one helper for atomically visible elapsed-turn publication.

    Unknown cache adapters expose only an irreversible ``store`` API.  During
    an elapsed turn they are deliberately not called: accepting a helper is
    still correct, while a post-deadline persistent cache write is not.
    """

    if proof_cache is None or dossier is None:
        return None
    if not bool(getattr(dossier, "proof_cache_publish_enabled", True)):
        return None
    owner = cache_owner_theorem_name(dossier)
    source = str(helper_block or "").strip()
    if not owner or not source:
        return None
    visible = getattr(dossier, "is_verified_helper_context_visible", None)
    if not callable(visible):
        return None
    helper_name = helper_decl_name(source)
    if not helper_name:
        return None
    try:
        if not bool(visible(helper_name)):
            return None
    except Exception:
        return None
    helper = (getattr(dossier, "verified_helpers", {}) or {}).get(helper_name)
    if verified_helper_is_premise_projection(helper or source):
        return None
    if not classify_auxiliary_statement_quality(
        helper_decl_statement(source)
    ).cache_publishable:
        return None
    begin = getattr(proof_cache, "begin_deadline_aware_store", None)
    if not callable(begin):
        return None
    try:
        kwargs: Dict[str, Any] = {
            "preamble": str(preamble or ""),
            "theorem_name": owner,
            "phase": str(phase or ""),
            "deadline_exhausted": deadline_exhausted,
        }
        try:
            parameters = inspect.signature(begin).parameters
            accepts_extra_kwargs = any(
                parameter.kind is inspect.Parameter.VAR_KEYWORD
                for parameter in parameters.values()
            )
        except (TypeError, ValueError):
            parameters = {}
            accepts_extra_kwargs = True
        if helper is not None:
            provenance_values = {
                "support_names": list(
                    getattr(helper, "support_names", []) or []
                ),
                "support_source_hashes": dict(
                    getattr(helper, "support_source_hashes", {}) or {}
                ),
                "replay_context_names": list(
                    getattr(helper, "replay_context_names", []) or []
                ),
                "replay_context_source_hashes": dict(
                    getattr(helper, "replay_context_source_hashes", {}) or {}
                ),
            }
            for parameter_name, value in provenance_values.items():
                if accepts_extra_kwargs or parameter_name in parameters:
                    kwargs[parameter_name] = value
        return begin(source, **kwargs)
    except Exception:
        return None


def publish_verified_dossier_helpers_to_cache(
    proof_cache: Any,
    *,
    dossier: Any,
    preamble: str,
    phase: str,
) -> Dict[str, int]:
    """Publish all currently visible helpers owned by ``dossier``.

    This is the ownership-boundary backstop for helpers merged by complex
    recursive/graph actions.  Ordinary direct writers can call the single-item
    helper above; repeated publication is safe because cache identity includes
    the owner namespace.
    """

    summary = {"eligible": 0, "stored": 0, "skipped": 0}
    if proof_cache is None or dossier is None:
        return summary
    if not bool(getattr(dossier, "proof_cache_publish_enabled", True)):
        return summary
    visible = getattr(dossier, "is_verified_helper_context_visible", None)
    helpers = getattr(dossier, "verified_helpers", {}) or {}
    values = helpers.values() if isinstance(helpers, dict) else ()
    for item in values:
        source = str(getattr(item, "source", "") or "").strip()
        if not source:
            summary["skipped"] += 1
            continue
        if verified_helper_is_premise_projection(item):
            summary["skipped"] += 1
            continue
        if not classify_auxiliary_statement_quality(
            helper_decl_statement(source)
        ).cache_publishable:
            summary["skipped"] += 1
            continue
        if callable(visible):
            try:
                if not bool(visible(item)):
                    summary["skipped"] += 1
                    continue
            except Exception:
                summary["skipped"] += 1
                continue
        summary["eligible"] += 1
        if store_verified_helper_for_dossier(
            proof_cache,
            source,
            preamble=preamble,
            dossier=dossier,
            phase=phase or str(getattr(item, "phase", "") or ""),
        ):
            summary["stored"] += 1
    return summary


def _cache_path_segment(text: str) -> str:
    segment = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(text or "").strip())
    return segment.strip("._-") or "run"


def _bounded_cache_path_segment(text: str, *, limit: int = 80) -> str:
    segment = _cache_path_segment(text)
    max_len = max(16, int(limit or 80))
    if len(segment) <= max_len:
        return segment
    digest = text_hash(segment)
    prefix_len = max(1, max_len - len(digest) - 1)
    return f"{segment[:prefix_len]}.{digest}"


def _proof_state_cache_path_for_sample(
    base_path: Path,
    *,
    sample_index: int,
    sample_count: int,
    run_id: str = "",
) -> Path:
    """Return the cache path visible to one proof-state sample.

    A single-sample run keeps the configured persistent cache path.  Parallel
    samples get run/sample-scoped cache files for write isolation;
    ``_make_proof_state_cache`` wires sibling files as read-through paths so
    freshly proved helpers can still be reused during the run.
    """

    path = Path(base_path)
    count = max(1, int(sample_count or 1))
    if count <= 1 and not str(run_id or "").strip():
        return path
    suffix = path.suffix or ".jsonl"
    stem = path.name[: -len(path.suffix)] if path.suffix else path.name
    parts: List[str] = []
    if str(run_id or "").strip():
        parts.append(_bounded_cache_path_segment(run_id))
    if count > 1:
        parts.append(f"sample{max(0, int(sample_index or 0)) + 1}")
    return path.with_name(f"{stem}.{'.'.join(parts)}{suffix}")


def _make_proof_state_cache(
    *,
    enabled: bool,
    base_path: Optional[Path],
    sample_index: int = 0,
    sample_count: int = 1,
    run_id: str = "",
    validated_seed: Optional[MiniVerifiedLemmaCache] = None,
    store_failure_metric_sink: Optional[Callable[[str, int], None]] = None,
) -> Optional[MiniVerifiedLemmaCache]:
    if not enabled:
        return None
    path = Path(base_path) if base_path is not None else MiniVerifiedLemmaCache.default_path()
    cache_path = _proof_state_cache_path_for_sample(
        path,
        sample_index=sample_index,
        sample_count=sample_count,
        run_id=run_id,
    )
    count = max(1, int(sample_count or 1))
    read_paths: List[Path] = []
    if count > 1:
        if cache_path != path:
            read_paths.append(path)
        for index in range(count):
            sibling_path = _proof_state_cache_path_for_sample(
                path,
                sample_index=index,
                sample_count=count,
                run_id=run_id,
            )
            if sibling_path != cache_path:
                read_paths.append(sibling_path)
    return MiniVerifiedLemmaCache(
        cache_path,
        read_paths=tuple(dict.fromkeys(read_paths)),
        validated_seed=validated_seed,
        store_failure_metric_sink=store_failure_metric_sink,
    )


def _proof_state_helper_policy_rejection(
    helper_block: str,
    *,
    expected_statement: str = "",
) -> str:
    """Return a reason if a cached/proof-state helper is not a single safe decl."""

    source = str(helper_block or "").strip()
    if not source:
        return "empty_helper"
    forbidden = _find_forbidden_lean_command([source], "by\n  trivial")
    if forbidden is not None:
        return f"forbidden_lean_command:{forbidden}"
    leading, chunks = _split_top_level_chunks(source)
    if leading.strip() or len(chunks) != 1:
        return "not_single_helper_declaration"
    sanitized_chunk = _strip_lean_comments_and_strings(chunks[0])
    if _SAFE_TOP_LEVEL_HELPER_RE.match(sanitized_chunk) is None:
        return "not_safe_theorem_or_lemma"
    if helper_decl_name(source) is None:
        return "missing_helper_name"
    if is_answer_unsafe_helper_source(source):
        return "answer_unsafe_helper"
    if has_sorry_or_admit(source):
        return "proof_placeholder"
    statement = helper_decl_statement(source)
    if not statement:
        return "missing_helper_statement"
    if expected_statement:
        left = _normalize_cache_statement(statement)
        right = _normalize_cache_statement(expected_statement)
        if left != right:
            return "statement_mismatch"
    stripped_source = _strip_lean_comments_and_strings(source).strip()
    stripped_chunk = _strip_lean_comments_and_strings(chunks[0]).strip()
    if stripped_source != stripped_chunk:
        return "not_single_helper_declaration"
    return ""
