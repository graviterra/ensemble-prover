"""Search project and Mathlib declarations for proof-repair candidates."""

from __future__ import annotations

import difflib
import heapq
import hashlib
import json
import logging
import math
import re
import time
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from .config import LeanConfig, RetrievalConfig
from .lemma_retriever import (
    LemmaEntry,
    _iter_lean_files,
    _resolve_project_dir_root,
    _scan_file,
)
from .utils import estimate_tokens

logger = logging.getLogger(__name__)

_STOPWORDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "import",
    "mathlib",
    "proof",
    "return",
    "exact",
    "complete",
    "candidate",
    "candidates",
    "fragment",
    "fragments",
    "lean",
    "given",
    "show",
    "have",
    "this",
    "that",
    "with",
    "from",
    "into",
    "then",
    "else",
    "true",
    "false",
    "type",
    "goal",
    "state",
}
_GENERIC_QUERY_TOKENS = {
    "measure",
    "real",
    "set",
    "theory",
    "type",
    "goal",
    "proof",
    "radius",
    "volume",
    "integral",
}
_IDENTIFIER_QUERY_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
_TOKEN_RE = re.compile(r"[A-Za-z0-9_'.]+")
_LEAN_SYMBOL_RE = re.compile(r"->|=>|:=|[∀∃∑→↔=<>≤≥∈∉⊆∣∧∨¬⊢≠]")
# D3 fix (2026-05-08): map Lean operator symbols to stable token names so
# BM25 retrieval can match operator semantics, not just identifiers. Tokens
# are namespaced with leading + trailing double underscore so they cannot
# collide with any valid Lean identifier (which forbids leading double
# underscores at the source level for reserved-name purposes).
_LEAN_SYMBOL_TOKEN_MAP: Dict[str, str] = {
    "∀": "__sym_forall__",
    "∃": "__sym_exists__",
    "∑": "__sym_sum__",
    "→": "__sym_arrow__",
    "↔": "__sym_iff__",
    "=": "__sym_eq__",
    "<": "__sym_lt__",
    ">": "__sym_gt__",
    "≤": "__sym_le__",
    "≥": "__sym_ge__",
    "∈": "__sym_mem__",
    "∉": "__sym_not_mem__",
    "⊆": "__sym_subset__",
    "∣": "__sym_dvd__",
    "∧": "__sym_and__",
    "∨": "__sym_or__",
    "¬": "__sym_not__",
    "⊢": "__sym_entails__",
    "->": "__sym_arrow__",
    "=>": "__sym_darrow__",
    ":=": "__sym_assign__",
    "≠": "__sym_ne__",
}
# Schema version bumps force a fresh index build. Version 4 added the durable
# per-source content manifest; version 5 binds that manifest to the exact
# serialized declaration index so valid-JSON corruption cannot masquerade as
# a healthy cache hit.
_MATHLIB_API_INDEX_SCHEMA_VERSION = 5
_MATHLIB_API_SOURCE_MANIFEST_VERSION = 1
_SOURCE_SNAPSHOT_MAX_ATTEMPTS = 3

# Full Mathlib currently contains more than 200k declarations.  A theorem
# statement contains many ubiquitous Lean tokens, so taking the union of every
# posting list turns retrieval into an effectively unbounded corpus scan.  The
# detailed scorer is deliberately limited to a deterministic, rare-token-first
# pool.  Exact identifier hits are always retained outside the pool budget.
_MIN_SCORING_CANDIDATES = 2048
_MAX_SCORING_CANDIDATES = 8192
_SCORING_CANDIDATES_PER_RESULT = 256
_MAX_CANDIDATE_POOL_MULTIPLIER = 4
_MAX_INFORMATIVE_QUERY_TOKENS = 24
_MAX_FUZZY_QUERY_CHARS = 160


def _tokenize(text: str) -> List[str]:
    raw = str(text or "")
    lowered = raw.lower()
    base_parts = _TOKEN_RE.findall(lowered)
    tokens: List[str] = []
    for part in base_parts:
        cleaned = part.strip("'.")
        if not cleaned:
            continue
        if len(cleaned) >= 2 and cleaned not in _STOPWORDS:
            tokens.append(cleaned)
        split_parts = [item for item in re.split(r"[_.']+", cleaned) if item]
        for item in split_parts:
            if len(item) >= 2 and item not in _STOPWORDS:
                tokens.append(item)
    # Append symbol tokens AFTER identifier tokens so any caller that uses
    # the prefix as a feature still sees identifiers first.
    for symbol in _LEAN_SYMBOL_RE.findall(raw):
        mapped = _LEAN_SYMBOL_TOKEN_MAP.get(symbol)
        if mapped is not None:
            tokens.append(mapped)
    return tokens


def _atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_suffix(path.suffix + ".tmp")
    tmp_path.write_text(content, encoding="utf-8")
    tmp_path.replace(path)


def _extract_symbols(text: str) -> List[str]:
    return list(dict.fromkeys(_LEAN_SYMBOL_RE.findall(text)))


def _normalize_stmt(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip())


def _jaccard(a: str, b: str) -> float:
    at = set(_TOKEN_RE.findall((a or "").lower()))
    bt = set(_TOKEN_RE.findall((b or "").lower()))
    if not at or not bt:
        return 0.0
    return len(at & bt) / max(1, len(at | bt))


def _estimate_tokens(text: str, *, model: Optional[str] = None) -> int:
    s = (text or "").strip()
    if not s:
        return 0
    return max(1, int(estimate_tokens(s, model=model)))


def _resolve_mathlib_api_paths(cfg: RetrievalConfig) -> Tuple[Path, Path]:
    index_path = Path(str(cfg.index_path or "./runs/lemma_index.jsonl")).expanduser()
    meta_path = Path(str(cfg.meta_path or "./runs/lemma_index.meta.json")).expanduser()
    return (
        index_path.with_name("mathlib_api_index.jsonl"),
        meta_path.with_name("mathlib_api_index.meta.json"),
    )


def _mathlib_api_config_fingerprint(
    cfg: RetrievalConfig,
    *,
    include_project: bool,
    schema_version: int = _MATHLIB_API_INDEX_SCHEMA_VERSION,
) -> str:
    payload = {
        "schema_version": int(schema_version),
        "mathlib_root": str(cfg.mathlib_root or ""),
        "project_root": str(cfg.project_root or ""),
        "include_docstrings": bool(cfg.include_docstrings),
        "include_project": bool(include_project),
        "max_lemmas": int(cfg.max_lemmas),
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _hash_source_file(path: Path) -> str:
    """Hash one source file; isolated so cache-hit tests can forbid byte reads."""

    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


class _SourceSnapshotChangedError(RuntimeError):
    """A source changed while its content identity was being captured."""


def _source_manifest_fingerprint(records: Sequence[Dict[str, Any]]) -> str:
    """Content identity independent of timestamps and filesystem order."""

    digest = hashlib.sha256()
    normalized = sorted(records, key=lambda item: str(item.get("path") or ""))
    for record in normalized:
        digest.update(str(record.get("path") or "").encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(record.get("content_sha256") or "").encode("ascii"))
        digest.update(b"\0")
    digest.update(str(len(normalized)).encode("ascii"))
    return digest.hexdigest()


def _source_manifest_record(
    path: Path,
    *,
    content_sha256: str,
    stat_result: Any = None,
) -> Dict[str, Any]:
    stat_result = stat_result if stat_result is not None else path.stat()
    return {
        "path": str(path),
        "size": int(stat_result.st_size),
        "mtime_ns": int(stat_result.st_mtime_ns),
        # ctime closes the same-size/same-mtime invalidation hole on normal
        # local filesystems: restoring mtime after a write still changes ctime.
        "ctime_ns": int(stat_result.st_ctime_ns),
        "content_sha256": str(content_sha256),
    }


def _source_stat_identity(stat_result: Any) -> Tuple[int, int, int]:
    return (
        int(stat_result.st_size),
        int(stat_result.st_mtime_ns),
        int(stat_result.st_ctime_ns),
    )


def _hash_source_file_stably(
    path: Path,
    initial_stat: Any,
) -> Tuple[str, Any]:
    """Hash a stable snapshot or fail closed if a source keeps changing."""

    before = initial_stat
    for _attempt in range(2):
        digest = _hash_source_file(path)
        after = path.stat()
        if _source_stat_identity(before) == _source_stat_identity(after):
            return digest, after
        before = after
    raise _SourceSnapshotChangedError(
        f"Mathlib API source changed during cache validation: {path}"
    )


@dataclass(frozen=True)
class _SourceManifestValidation:
    records: Tuple[Dict[str, Any], ...]
    fingerprint: str
    reason: str
    valid_for_cached_index: bool
    metadata_changed: bool
    full_hash_files: int
    reused_digest_files: int


def _validate_source_manifest(
    paths: Sequence[Path],
    meta: Optional[Dict[str, Any]],
) -> _SourceManifestValidation:
    """Validate cached source identity using stats, hashing only changed files."""

    sorted_paths = sorted(paths, key=lambda item: str(item))
    raw_manifest = meta.get("source_manifest") if isinstance(meta, dict) else None
    try:
        manifest_version = int(
            (meta or {}).get("source_manifest_version", 0) or 0
        )
    except (TypeError, ValueError):
        manifest_version = 0
    manifest_usable = bool(
        manifest_version == _MATHLIB_API_SOURCE_MANIFEST_VERSION
        and isinstance(raw_manifest, list)
    )
    stored_by_path: Dict[str, Dict[str, Any]] = {}
    if manifest_usable:
        for raw_record in raw_manifest:
            if not isinstance(raw_record, dict):
                manifest_usable = False
                break
            path_key = str(raw_record.get("path") or "")
            content_sha256 = str(raw_record.get("content_sha256") or "")
            try:
                size = int(raw_record.get("size", -1))
                mtime_ns = int(raw_record.get("mtime_ns", -1))
                ctime_ns = int(raw_record.get("ctime_ns", -1))
            except (TypeError, ValueError):
                manifest_usable = False
                break
            if (
                not path_key
                or re.fullmatch(r"[0-9a-f]{64}", content_sha256) is None
                or min(size, mtime_ns, ctime_ns) < 0
                or path_key in stored_by_path
            ):
                manifest_usable = False
                break
            stored_by_path[path_key] = raw_record

    records: List[Dict[str, Any]] = []
    full_hash_files = 0
    reused_digest_files = 0
    metadata_changed = False
    current_path_keys = {str(path) for path in sorted_paths}
    file_set_changed = bool(
        manifest_usable and current_path_keys != set(stored_by_path)
    )
    for path in sorted_paths:
        stat_result = path.stat()
        path_key = str(path)
        stored = stored_by_path.get(path_key) if manifest_usable else None
        stat_unchanged = bool(
            stored is not None
            and int(stored.get("size", -1)) == int(stat_result.st_size)
            and int(stored.get("mtime_ns", -1)) == int(stat_result.st_mtime_ns)
            and int(stored.get("ctime_ns", -1)) == int(stat_result.st_ctime_ns)
        )
        if stat_unchanged:
            content_sha256 = str(stored.get("content_sha256") or "")
            reused_digest_files += 1
        else:
            content_sha256, stat_result = _hash_source_file_stably(
                path,
                stat_result,
            )
            full_hash_files += 1
            metadata_changed = metadata_changed or stored is not None
        records.append(
            _source_manifest_record(
                path,
                content_sha256=content_sha256,
                stat_result=stat_result,
            )
        )

    fingerprint = _source_manifest_fingerprint(records)
    expected_fingerprint = str((meta or {}).get("fingerprint") or "")
    valid = bool(
        manifest_usable
        and not file_set_changed
        and expected_fingerprint
        and fingerprint == expected_fingerprint
    )
    if not manifest_usable:
        reason = "source_manifest_missing_or_invalid"
    elif file_set_changed:
        reason = "source_file_set_changed"
    elif fingerprint != expected_fingerprint:
        reason = "source_content_changed"
    elif metadata_changed:
        reason = "source_metadata_refreshed"
    else:
        reason = "source_manifest_cache_hit"
    return _SourceManifestValidation(
        records=tuple(records),
        fingerprint=fingerprint,
        reason=reason,
        valid_for_cached_index=valid,
        metadata_changed=metadata_changed,
        full_hash_files=full_hash_files,
        reused_digest_files=reused_digest_files,
    )


def _source_manifest_stats_still_match(
    records: Sequence[Dict[str, Any]],
) -> bool:
    for record in records:
        try:
            current = Path(str(record.get("path") or "")).stat()
            expected = (
                int(record.get("size", -1)),
                int(record.get("mtime_ns", -1)),
                int(record.get("ctime_ns", -1)),
            )
        except (OSError, TypeError, ValueError):
            return False
        if _source_stat_identity(current) != expected:
            return False
    return True


def _source_files_for_roots(roots: Sequence[Path]) -> List[Path]:
    exclude_dirs = ["build", ".lake", ".git", "external", "Temp"]
    paths: List[Path] = []
    seen: set[str] = set()
    for root in roots:
        for path in _iter_lean_files(root, exclude_dirs=exclude_dirs):
            key = str(path)
            if key in seen:
                continue
            seen.add(key)
            paths.append(path)
    return paths


def _source_snapshot_still_matches(
    roots: Sequence[Path],
    records: Sequence[Dict[str, Any]],
) -> bool:
    """Check both file membership and metadata for one captured snapshot."""

    if not _source_manifest_stats_still_match(records):
        return False
    try:
        current_paths = {str(path) for path in _source_files_for_roots(roots)}
    except OSError:
        return False
    recorded_paths = {str(record.get("path") or "") for record in records}
    return current_paths == recorded_paths


def _capture_stable_source_snapshot(
    roots: Sequence[Path],
    meta: Optional[Dict[str, Any]],
) -> Tuple[List[Path], _SourceManifestValidation]:
    """Capture one stable source set, retrying bounded concurrent mutations.

    Editors commonly publish Lean files by atomically replacing or renaming
    them. A path can therefore disappear between directory enumeration and
    ``stat`` even though the project settles immediately afterward. Serving a
    manifest for the old set is unsound, while aborting a long-running Mini
    startup on that transient race is unnecessary. Re-enumerate the complete
    set and retry; persistent mutation fails closed after a fixed bound.
    """

    last_error = "source set kept changing"
    for _attempt in range(_SOURCE_SNAPSHOT_MAX_ATTEMPTS):
        try:
            paths = _source_files_for_roots(roots)
            validation = _validate_source_manifest(paths, meta)
        except (OSError, _SourceSnapshotChangedError) as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            continue
        if _source_snapshot_still_matches(roots, validation.records):
            return paths, validation
        last_error = "source membership or metadata changed during capture"
    raise RuntimeError(
        "Mathlib API sources did not stabilize during bounded snapshot "
        f"capture: {last_error}"
    )


def _resolve_mathlib_api_roots(
    cfg: RetrievalConfig, lean_cfg: LeanConfig, *, include_project: bool
) -> Tuple[List[Path], Optional[Path], Optional[Path], List[str]]:
    if cfg.project_root:
        project_candidate = Path(str(cfg.project_root)).expanduser().resolve()
        project_root = project_candidate if project_candidate.exists() else None
    else:
        project_root = _resolve_project_dir_root(lean_cfg.project_dir)

    if cfg.mathlib_root:
        mathlib_candidate = Path(str(cfg.mathlib_root)).expanduser().resolve()
        mathlib_root = mathlib_candidate if mathlib_candidate.exists() else None
    elif project_root is not None:
        mathlib_candidate = project_root / ".lake" / "packages" / "mathlib" / "Mathlib"
        mathlib_root = mathlib_candidate if mathlib_candidate.exists() else None
    else:
        mathlib_root = None

    roots: List[Path] = []
    missing_required: List[str] = []
    if mathlib_root is not None:
        roots.append(mathlib_root)
    else:
        missing_required.append("mathlib")
    if include_project:
        if project_root is not None:
            roots.append(project_root)
        else:
            missing_required.append("project")
    return roots, project_root, mathlib_root, missing_required


def _entry_source_counts(entries: Sequence[LemmaEntry]) -> Dict[str, int]:
    counts = Counter(
        str(getattr(entry, "source", "") or "unknown") for entry in entries
    )
    return {key: int(value) for key, value in sorted(counts.items()) if int(value) > 0}


def _build_mathlib_api_entries(
    roots: Sequence[Path],
    *,
    mathlib_root: Optional[Path],
    include_docstrings: bool,
    max_entries: int,
    file_paths: Optional[Sequence[Path]] = None,
) -> List[LemmaEntry]:
    entries: List[LemmaEntry] = []
    if file_paths is not None:
        all_paths: Iterable[Path] = file_paths
    else:
        all_paths = (
            p
            for root in roots
            if root and root.exists()
            for p in _iter_lean_files(
                root, exclude_dirs=["build", ".lake", ".git", "external", "Temp"]
            )
        )
    for path in all_paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as exc:
            logger.warning("build_mathlib_api_entries: failed to read %s: %s", path, exc)
            continue
        for entry in _scan_file(text, path):
            if not include_docstrings:
                entry.docstring = ""
            source = "project"
            if mathlib_root is not None:
                try:
                    path.relative_to(mathlib_root)
                    source = "mathlib"
                except Exception:
                    source = "project"
            entry.source = source
            entries.append(entry)
            if len(entries) >= max_entries:
                return entries
    return entries


@dataclass
class MathlibApiIndexMeta:
    created_ts: float
    fingerprint: str
    file_count: int
    entry_count: int
    config_fingerprint: str
    source_counts: Dict[str, int]
    index_content_sha256: str = ""
    source_manifest: Tuple[Dict[str, Any], ...] = ()
    source_manifest_version: int = _MATHLIB_API_SOURCE_MANIFEST_VERSION
    schema_version: int = _MATHLIB_API_INDEX_SCHEMA_VERSION


class MathlibApiIndex:
    def __init__(
        self,
        entries: Optional[List[LemmaEntry]] = None,
        *,
        content_sha256: str = "",
    ):
        self.entries: List[LemmaEntry] = list(entries or [])
        self.content_sha256 = str(content_sha256 or "")

    def save(self, path: Path, meta_path: Path, meta: MathlibApiIndexMeta) -> None:
        index_content = "".join(
            json.dumps(asdict(entry), ensure_ascii=False) + "\n" for entry in self.entries
        )
        meta.index_content_sha256 = hashlib.sha256(
            index_content.encode("utf-8")
        ).hexdigest()
        _atomic_write_text(path, index_content)
        _atomic_write_text(meta_path, json.dumps(asdict(meta), ensure_ascii=False))

    @staticmethod
    def load(path: Path) -> Optional["MathlibApiIndex"]:
        if not path.exists():
            return None
        index_content = path.read_text(encoding="utf-8")
        entries: List[LemmaEntry] = []
        for line in index_content.splitlines():
            if not line.strip():
                continue
            try:
                entries.append(LemmaEntry(**json.loads(line)))
            except Exception as exc:
                logger.debug(
                    "MathlibApiIndex.load: skipping corrupted entry in %s: %s", path, exc
                )
        return MathlibApiIndex(
            entries,
            content_sha256=hashlib.sha256(
                index_content.encode("utf-8")
            ).hexdigest(),
        )


def _loaded_index_matches_meta(
    loaded_index: MathlibApiIndex,
    meta: Optional[Dict[str, Any]],
) -> bool:
    """Check that a parsed cache still has the entries its metadata promises.

    Atomic publication prevents ordinary partial writes, but it does not make
    an already-published JSONL file immune to truncation or corruption.  The
    loader intentionally skips malformed rows, so accepting the resulting
    prefix without this check would silently turn a healthy 200k-declaration
    corpus into a smaller (or empty) one while still reporting a cache hit.
    """

    if not isinstance(meta, dict):
        return False
    expected_content_sha256 = str(meta.get("index_content_sha256") or "")
    if (
        re.fullmatch(r"[0-9a-f]{64}", expected_content_sha256) is None
        or loaded_index.content_sha256 != expected_content_sha256
    ):
        return False
    try:
        expected_entry_count = int(meta.get("entry_count", -1))
    except (TypeError, ValueError):
        return False
    if expected_entry_count < 0 or len(loaded_index.entries) != expected_entry_count:
        return False
    raw_source_counts = meta.get("source_counts")
    if not isinstance(raw_source_counts, dict):
        return False
    try:
        expected_source_counts = {
            str(key): int(value) for key, value in raw_source_counts.items()
        }
    except (TypeError, ValueError):
        return False
    return _entry_source_counts(loaded_index.entries) == expected_source_counts


@dataclass(frozen=True)
class MathlibApiSearchHit:
    entry: Any
    score: float
    reasons: Tuple[str, ...]
    details: Dict[str, float]


class MathlibApiSearcher:
    """Deterministic, read-only API lookup over static Mathlib/project entries.

    This intentionally excludes local declarations, generated support lemmas,
    and proven-lemma memory. Those belong to separate support channels.
    """

    def __init__(
        self,
        entries: Sequence[Any],
        *,
        include_project: bool = False,
        include_docstrings: bool = False,
        index_path: Optional[Path] = None,
        meta_path: Optional[Path] = None,
        goal_conditioned: bool = True,
        goal_query_weight: float = 1.0,
        max_prompt_lemmas: int = 30,
        prompt_budget_enabled: bool = True,
        prompt_budget_tokens: int = 1200,
        prompt_budget_hard_cap_tokens: int = 20000,
        prompt_budget_dedup_jaccard: float = 0.92,
    ) -> None:
        allowed_sources = {"mathlib", "project"} if include_project else {"mathlib"}
        filtered = [
            entry
            for entry in entries
            if str(getattr(entry, "source", "") or "").strip().lower() in allowed_sources
        ]
        self._entries: List[Any] = list(filtered)
        self._entry_tokens: List[Counter[str]] = []
        self._name_index: Dict[str, List[int]] = {}
        self._full_name_index: Dict[str, List[int]] = {}
        self._token_index: Dict[str, List[int]] = {}
        self._token_df: Dict[str, int] = {}
        self._include_docstrings = bool(include_docstrings)
        self._index_path = str(index_path) if index_path is not None else ""
        self._meta_path = str(meta_path) if meta_path is not None else ""
        self._goal_conditioned = bool(goal_conditioned)
        self._goal_query_weight = max(0.0, float(goal_query_weight))
        self._max_prompt_lemmas = max(1, int(max_prompt_lemmas))
        self._prompt_budget_enabled = bool(prompt_budget_enabled)
        self._prompt_budget_tokens = max(0, int(prompt_budget_tokens))
        self._prompt_budget_hard_cap_tokens = max(0, int(prompt_budget_hard_cap_tokens))
        self._prompt_budget_dedup_jaccard = max(
            0.0, min(1.0, float(prompt_budget_dedup_jaccard))
        )
        corpus_hasher = hashlib.sha256()
        for entry in self._entries:
            for field_name in (
                "name",
                "full_name",
                "kind",
                "type",
                "namespace",
                "docstring",
                "source",
                "module",
                "file",
            ):
                corpus_hasher.update(
                    str(getattr(entry, field_name, "") or "").encode("utf-8")
                )
                corpus_hasher.update(b"\0")
            corpus_hasher.update(b"\n")
        self._capability_corpus_sha256 = corpus_hasher.hexdigest()
        self._tokenizer_model: Optional[str] = None
        self._startup_telemetry: Dict[str, Any] = {}
        self._build_indexes()

    def request_config(self) -> Dict[str, Any]:
        """Stable semantic identity for recursive paid-lane accounting."""

        return {
            "schema_version": 1,
            "entry_count": len(self._entries),
            "corpus_sha256": self._capability_corpus_sha256,
            "include_docstrings": self._include_docstrings,
            "index_path": self._index_path,
            "meta_path": self._meta_path,
            "goal_conditioned": self._goal_conditioned,
            "goal_query_weight": self._goal_query_weight,
            "max_prompt_lemmas": self._max_prompt_lemmas,
            "prompt_budget_enabled": self._prompt_budget_enabled,
            "prompt_budget_tokens": self._prompt_budget_tokens,
            "prompt_budget_hard_cap_tokens": self._prompt_budget_hard_cap_tokens,
            "prompt_budget_dedup_jaccard": self._prompt_budget_dedup_jaccard,
            "tokenizer_model": self._tokenizer_model,
        }

    @classmethod
    def load_or_build(
        cls,
        cfg: RetrievalConfig,
        lean_cfg: LeanConfig,
        *,
        include_project: bool = False,
    ) -> Optional["MathlibApiSearcher"]:
        startup_started = time.monotonic()
        index_path, meta_path = _resolve_mathlib_api_paths(cfg)
        meta: Optional[Dict[str, Any]] = None
        if meta_path.exists():
            try:
                loaded_meta = json.loads(meta_path.read_text(encoding="utf-8"))
            except Exception as exc:
                logger.warning(
                    "Mathlib API index meta parse failed for %s: %s", meta_path, exc
                )
                loaded_meta = None
            if isinstance(loaded_meta, dict):
                meta = loaded_meta

        validation_started = time.monotonic()
        roots, _project_root, mathlib_root, missing_required = (
            _resolve_mathlib_api_roots(
                cfg, lean_cfg, include_project=include_project
            )
        )
        if missing_required:
            logger.warning(
                "Mathlib API search unavailable; missing roots=%s project_root=%r mathlib_root=%r lean.project_dir=%r",
                ",".join(sorted(missing_required)),
                cfg.project_root,
                cfg.mathlib_root,
                lean_cfg.project_dir,
            )
            return None

        all_files, manifest_validation = _capture_stable_source_snapshot(
            roots,
            meta,
        )
        fingerprint = manifest_validation.fingerprint
        config_fingerprint = _mathlib_api_config_fingerprint(
            cfg, include_project=include_project
        )
        need_rebuild = False
        rebuild_reasons: List[str] = []
        if not index_path.exists():
            need_rebuild = True
            rebuild_reasons.append("index_missing")
        elif meta is None:
            need_rebuild = True
            rebuild_reasons.append("meta_missing")
        else:
            if not manifest_validation.valid_for_cached_index:
                need_rebuild = True
                rebuild_reasons.append(manifest_validation.reason)
            if meta.get("config_fingerprint") != config_fingerprint:
                need_rebuild = True
                rebuild_reasons.append("config_fingerprint_mismatch")
            try:
                meta_schema_version = int(meta.get("schema_version", 0) or 0)
            except (TypeError, ValueError):
                meta_schema_version = 0
            if meta_schema_version != _MATHLIB_API_INDEX_SCHEMA_VERSION:
                need_rebuild = True
                rebuild_reasons.append("schema_version_mismatch")

        validation_elapsed_s = time.monotonic() - validation_started
        metadata_refreshed = False
        if (
            not need_rebuild
            and meta is not None
            and manifest_validation.metadata_changed
        ):
            refreshed_meta = dict(meta)
            refreshed_meta["source_manifest"] = list(manifest_validation.records)
            refreshed_meta["source_manifest_version"] = (
                _MATHLIB_API_SOURCE_MANIFEST_VERSION
            )
            _atomic_write_text(
                meta_path,
                json.dumps(refreshed_meta, ensure_ascii=False),
            )
            meta = refreshed_meta
            metadata_refreshed = True

        rebuild_elapsed_s = 0.0

        def build_entries_from_stable_snapshot() -> List[LemmaEntry]:
            nonlocal all_files
            nonlocal fingerprint
            nonlocal manifest_validation

            for _attempt in range(_SOURCE_SNAPSHOT_MAX_ATTEMPTS):
                entries = _build_mathlib_api_entries(
                    roots,
                    mathlib_root=mathlib_root,
                    include_docstrings=bool(cfg.include_docstrings),
                    max_entries=int(cfg.max_lemmas),
                    file_paths=all_files,
                )
                if _source_snapshot_still_matches(
                    roots,
                    manifest_validation.records,
                ):
                    return entries
                all_files, manifest_validation = _capture_stable_source_snapshot(
                    roots,
                    meta,
                )
                fingerprint = manifest_validation.fingerprint
            raise RuntimeError(
                "Mathlib API sources did not stabilize during bounded "
                "declaration-index construction."
            )

        def publish_rebuilt_index() -> Tuple[MathlibApiIndex, Dict[str, Any]]:
            nonlocal all_files
            nonlocal fingerprint
            nonlocal manifest_validation

            for _attempt in range(_SOURCE_SNAPSHOT_MAX_ATTEMPTS):
                entries = build_entries_from_stable_snapshot()
                source_counts = _entry_source_counts(entries)
                if int(source_counts.get("mathlib", 0)) <= 0:
                    raise RuntimeError(
                        "Mathlib API index rebuild failed closed: rebuilt "
                        "index had 0 Mathlib entries."
                    )
                meta_obj = MathlibApiIndexMeta(
                    created_ts=time.time(),
                    fingerprint=fingerprint,
                    file_count=len(all_files),
                    entry_count=len(entries),
                    config_fingerprint=config_fingerprint,
                    source_counts=source_counts,
                    source_manifest=manifest_validation.records,
                )
                MathlibApiIndex(entries).save(index_path, meta_path, meta_obj)
                rebuilt = MathlibApiIndex.load(index_path)
                rebuilt_meta = asdict(meta_obj)
                if rebuilt is None or not _loaded_index_matches_meta(
                    rebuilt,
                    rebuilt_meta,
                ):
                    raise RuntimeError(
                        "Mathlib API index rebuild produced an invalid cache; "
                        "refusing to serve it."
                    )
                if _source_snapshot_still_matches(
                    roots,
                    manifest_validation.records,
                ):
                    return rebuilt, rebuilt_meta
                all_files, manifest_validation = _capture_stable_source_snapshot(
                    roots,
                    rebuilt_meta,
                )
                fingerprint = manifest_validation.fingerprint
            raise RuntimeError(
                "Mathlib API sources changed throughout bounded cache "
                "publication; refusing to publish a mixed-snapshot index."
            )

        if need_rebuild:
            rebuild_started = time.monotonic()
            if rebuild_reasons:
                logger.info(
                    "Mathlib API index rebuild starting (%s)",
                    ", ".join(rebuild_reasons),
                )
            _rebuilt, meta = publish_rebuilt_index()
            rebuild_elapsed_s = time.monotonic() - rebuild_started

        load_started = time.monotonic()
        loaded_index = MathlibApiIndex.load(index_path)
        index_load_elapsed_s = time.monotonic() - load_started
        if loaded_index is None:
            logger.warning(
                "MathlibApiSearcher: index unavailable. Run scripts/build_mathlib_api_index.py to create it."
            )
            return None
        if not _loaded_index_matches_meta(loaded_index, meta):
            if need_rebuild:
                raise RuntimeError(
                    "Mathlib API index failed integrity validation immediately "
                    "after rebuild; refusing to serve a partial declaration corpus."
                )
            rebuild_started = time.monotonic()
            logger.warning(
                "Mathlib API cached index failed entry-count/source-count "
                "validation; rebuilding from the verified source manifest."
            )
            rebuild_reasons.append("index_integrity_mismatch")
            loaded_index, meta = publish_rebuilt_index()
            need_rebuild = True
            rebuild_elapsed_s += time.monotonic() - rebuild_started
        if not _source_snapshot_still_matches(
            roots,
            manifest_validation.records,
        ):
            rebuild_started = time.monotonic()
            rebuild_reasons.append("source_changed_during_cache_load")
            all_files, manifest_validation = _capture_stable_source_snapshot(
                roots,
                meta,
            )
            fingerprint = manifest_validation.fingerprint
            loaded_index, meta = publish_rebuilt_index()
            need_rebuild = True
            rebuild_elapsed_s += time.monotonic() - rebuild_started
        runtime_index_started = time.monotonic()
        searcher = cls(
            loaded_index.entries,
            include_project=include_project,
            include_docstrings=bool(cfg.include_docstrings),
            index_path=index_path,
            meta_path=meta_path,
            goal_conditioned=bool(cfg.goal_conditioned),
            goal_query_weight=float(cfg.goal_query_weight),
            max_prompt_lemmas=int(cfg.max_prompt_lemmas),
            prompt_budget_enabled=bool(cfg.prompt_budget_enabled),
            prompt_budget_tokens=int(cfg.prompt_budget_tokens),
            prompt_budget_hard_cap_tokens=int(cfg.prompt_budget_hard_cap_tokens),
            prompt_budget_dedup_jaccard=float(cfg.prompt_budget_dedup_jaccard),
        )
        runtime_index_elapsed_s = time.monotonic() - runtime_index_started
        startup_telemetry = {
            "cache_hit": not need_rebuild,
            "validation_reason": manifest_validation.reason,
            "rebuild_reasons": list(dict.fromkeys(rebuild_reasons)),
            "validation_s": round(validation_elapsed_s, 6),
            "rebuild_s": round(rebuild_elapsed_s, 6),
            "index_load_s": round(index_load_elapsed_s, 6),
            "runtime_index_build_s": round(runtime_index_elapsed_s, 6),
            "total_s": round(time.monotonic() - startup_started, 6),
            "source_file_count": len(all_files),
            "source_files_full_hashed": manifest_validation.full_hash_files,
            "source_digests_reused": manifest_validation.reused_digest_files,
            "source_manifest_version": _MATHLIB_API_SOURCE_MANIFEST_VERSION,
            "metadata_refreshed": metadata_refreshed,
            "schema_migrated": "schema_version_mismatch" in rebuild_reasons,
        }
        searcher._startup_telemetry = startup_telemetry
        logger.info("Mathlib API index startup: %s", startup_telemetry)
        return searcher

    def set_tokenizer_model(self, model: Optional[str]) -> None:
        if model and str(model).strip():
            self._tokenizer_model = str(model).strip()
        else:
            self._tokenizer_model = None

    def status(self) -> Dict[str, Any]:
        source_counts: Dict[str, int] = defaultdict(int)
        for entry in self._entries:
            source_counts[str(getattr(entry, "source", "") or "unknown")] += 1
        return {
            "channel": "static_mathlib_api",
            "entry_count": len(self._entries),
            "source_counts": dict(source_counts),
            "index_path": self._index_path,
            "meta_path": self._meta_path,
            "startup": dict(self._startup_telemetry),
        }

    def format_context(self, entries: Sequence[Any]) -> str:
        lines: List[str] = []
        for entry in entries:
            doc = str(getattr(entry, "docstring", "") or "").strip()
            if doc and self._include_docstrings:
                lines.append(f"{entry.name} : {entry.type}  -- {doc}")
            else:
                lines.append(f"{entry.name} : {entry.type}")
        return "\n".join(lines)

    def _build_query_text(self, statement: str, *, goal_state: Optional[str] = None) -> str:
        stmt = (statement or "").strip()
        if not stmt:
            return ""
        if self._goal_conditioned and goal_state and goal_state.strip():
            w = self._goal_query_weight
            if w <= 1e-6:
                return stmt
            reps = max(1, min(3, int(round(w))))
            gs = goal_state.strip()
            return stmt + "\n\n" + "\n".join([gs] * reps)
        return stmt

    def _entry_line(self, entry: Any) -> str:
        doc = str(getattr(entry, "docstring", "") or "").strip()
        if doc and self._include_docstrings:
            return f"{entry.name} : {entry.type}  -- {doc}"
        return f"{entry.name} : {entry.type}"

    def budget_for_prompt(
        self,
        entries: List[Any],
        statement: str,
        *,
        goal_state: Optional[str] = None,
        token_budget: Optional[int] = None,
    ) -> List[Any]:
        if not entries:
            return []
        budget = int(
            token_budget if token_budget is not None else self._prompt_budget_tokens
        )
        if not self._prompt_budget_enabled or budget <= 0:
            hard_cap = int(self._prompt_budget_hard_cap_tokens)
            if hard_cap <= 0:
                return list(entries)
            budget = hard_cap

        max_items = int(self._max_prompt_lemmas)
        dedup_thr = float(self._prompt_budget_dedup_jaccard)
        query_text = self._build_query_text(statement, goal_state=goal_state)
        q_tokens = set(_tokenize(query_text))
        q_syms = set(_extract_symbols(query_text))

        selected: List[Any] = []
        used_tokens: set[str] = set()
        used_syms: set[str] = set()
        used_types: List[str] = []
        used_namespaces: set[str] = set()
        budget_left = int(budget)

        for rank, entry in enumerate(entries):
            if len(selected) >= max_items:
                break
            line = self._entry_line(entry)
            cost = _estimate_tokens(line, model=self._tokenizer_model)
            if cost <= 0 or cost > budget_left:
                continue

            typ_norm = _normalize_stmt(str(getattr(entry, "type", "") or ""))
            if typ_norm and any(_jaccard(typ_norm, seen) >= dedup_thr for seen in used_types):
                continue

            etoks = set(
                _tokenize(
                    f"{str(getattr(entry, 'name', '') or '')} {str(getattr(entry, 'type', '') or '')}"
                )
            )
            esyms = set(_extract_symbols(str(getattr(entry, "type", "") or "")))
            new_tok = len((etoks & q_tokens) - used_tokens)
            new_sym = len((esyms & q_syms) - used_syms)

            namespace = str(getattr(entry, "namespace", "") or "")
            ns = namespace.split(".")[0] if namespace else ""
            ns_pen = 0.25 if (ns and ns in used_namespaces) else 0.0
            prior = 1.0 - (rank / max(1.0, float(len(entries))))
            gain = (1.0 + 0.25 * float(new_tok) + 0.5 * float(new_sym)) * (1.0 - ns_pen)

            if gain < 1.05 and len(selected) >= max(3, max_items // 4):
                continue
            if prior < 0.10 and budget_left < budget * 0.25:
                continue

            selected.append(entry)
            budget_left -= cost
            used_tokens |= etoks & q_tokens
            used_syms |= esyms & q_syms
            if typ_norm:
                used_types.append(typ_norm)
            if ns:
                used_namespaces.add(ns)

        if selected:
            return selected

        fallback: List[Any] = []
        fallback_budget = int(budget)
        fallback_cap = min(max_items, 3)
        for entry in entries:
            if len(fallback) >= fallback_cap:
                break
            cost = _estimate_tokens(self._entry_line(entry), model=self._tokenizer_model)
            if cost <= 0 or cost > fallback_budget:
                continue
            fallback.append(entry)
            fallback_budget -= cost
        return fallback

    def search(
        self,
        query_text: str,
        *,
        goal_state: str = "",
        kind: str = "any",
        max_results: int = 10,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> List[Any]:
        return [
            hit.entry
            for hit in self.search_with_scores(
                query_text,
                goal_state=goal_state,
                kind=kind,
                max_results=max_results,
                deadline_exhausted=deadline_exhausted,
            )
        ]

    def search_with_scores(
        self,
        query_text: str,
        *,
        goal_state: str = "",
        kind: str = "any",
        max_results: int = 10,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> List[MathlibApiSearchHit]:
        def deadline_elapsed() -> bool:
            try:
                return bool(deadline_exhausted and deadline_exhausted())
            except Exception:
                return True

        if deadline_elapsed():
            return []
        query_text = str(query_text or "").strip()
        goal_state = str(goal_state or "").strip()
        if not query_text or not self._entries:
            return []
        limit = max(1, int(max_results))
        effective_query = "\n".join(part for part in (query_text, goal_state) if part)
        query_tokens = _tokenize(effective_query)
        candidate_limit = max(
            _MIN_SCORING_CANDIDATES,
            min(
                _MAX_SCORING_CANDIDATES,
                limit * _SCORING_CANDIDATES_PER_RESULT,
            ),
        )
        candidate_ids = self._candidate_ids(
            query_text,
            query_tokens,
            max_candidates=candidate_limit,
            deadline_exhausted=deadline_elapsed,
        )
        if not candidate_ids:
            return []

        hits: List[MathlibApiSearchHit] = []
        seen_names: set[str] = set()
        for entry_id in candidate_ids:
            if deadline_elapsed():
                break
            entry = self._entries[entry_id]
            entry_kind = str(getattr(entry, "kind", "") or "").strip().lower()
            normalized_kind = str(kind).strip().lower()
            if normalized_kind == "theorem_like":
                if entry_kind not in {"theorem", "lemma", "axiom"}:
                    continue
            elif normalized_kind != "any" and entry_kind != normalized_kind:
                continue
            hit = self._score_entry(
                entry, self._entry_tokens[entry_id], query_text, query_tokens
            )
            if hit is None:
                continue
            entry_name = str(getattr(entry, "name", "") or "").strip()
            if entry_name in seen_names:
                continue
            seen_names.add(entry_name)
            hits.append(hit)

        hits.sort(
            key=lambda hit: (
                -hit.score,
                str(getattr(hit.entry, "name", "") or ""),
            )
        )
        return hits[:limit]

    def _build_indexes(self) -> None:
        name_index: Dict[str, List[int]] = defaultdict(list)
        full_name_index: Dict[str, List[int]] = defaultdict(list)
        token_index: Dict[str, List[int]] = defaultdict(list)
        token_df: Counter[str] = Counter()
        suffix_name_index: Dict[str, List[int]] = defaultdict(list)

        for idx, entry in enumerate(self._entries):
            entry_tokens = Counter(_tokenize(self._entry_text(entry)))
            self._entry_tokens.append(entry_tokens)
            name = str(getattr(entry, "name", "") or "").strip().lower()
            full_name = name
            if name:
                name_index[name].append(idx)
                full_name_index[full_name].append(idx)
                suffix_name_index[name.split(".")[-1]].append(idx)
            for token in entry_tokens:
                token_index[token].append(idx)
            token_df.update(entry_tokens.keys())

        self._name_index = dict(name_index)
        self._full_name_index = dict(full_name_index)
        self._token_index = dict(token_index)
        self._token_df = dict(token_df)
        self._suffix_name_index = dict(suffix_name_index)
        self._name_corpus = tuple(
            dict.fromkeys((*self._name_index.keys(), *self._full_name_index.keys()))
        )

    @staticmethod
    def _entry_text(entry: Any) -> str:
        return "\n".join(
            part
            for part in (
                str(getattr(entry, "name", "") or ""),
                str(getattr(entry, "type", "") or ""),
                str(getattr(entry, "docstring", "") or ""),
                str(getattr(entry, "namespace", "") or ""),
                str(getattr(entry, "file", "") or ""),
            )
            if part
        )

    def _candidate_ids(
        self,
        query_text: str,
        query_tokens: List[str],
        *,
        max_candidates: int = _MAX_SCORING_CANDIDATES,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> List[int]:
        max_candidates = max(1, int(max_candidates or 1))
        exact_candidate_ids: set[int] = set()
        name_candidate_ids: set[int] = set()
        stripped = str(query_text or "").strip()
        lowered = stripped.lower()
        if _IDENTIFIER_QUERY_RE.fullmatch(stripped):
            exact_candidate_ids.update(self._full_name_index.get(lowered, ()))
            exact_candidate_ids.update(self._name_index.get(lowered, ()))
            name_candidate_limit = max_candidates * _MAX_CANDIDATE_POOL_MULTIPLIER
            name_candidate_ids.update(
                self._suffix_name_index.get(lowered, ())[:name_candidate_limit]
            )
            suffix = lowered.split(".")[-1]
            name_candidate_ids.update(
                self._suffix_name_index.get(suffix, ())[:name_candidate_limit]
            )
            if not exact_candidate_ids and not name_candidate_ids:
                try:
                    deadline_elapsed = bool(
                        deadline_exhausted and deadline_exhausted()
                    )
                except Exception:
                    deadline_elapsed = True
                if not deadline_elapsed:
                    for close in self._cooperative_close_name_matches(
                        lowered,
                        n=16,
                        cutoff=0.65,
                        deadline_exhausted=deadline_exhausted,
                    ):
                        name_candidate_ids.update(
                            self._full_name_index.get(close, ())
                        )
                        name_candidate_ids.update(self._name_index.get(close, ()))

        # Deduplicate repeated goal/query tokens and rank them by document
        # frequency.  Rare tokens carry more mathematical information and
        # keep the candidate pool bounded even when the query also contains
        # ubiquitous syntax such as forall/equality/membership.
        corpus_size = max(1, len(self._entries))
        informative_tokens = sorted(
            {
                token
                for token in query_tokens
                if token in self._token_index
            },
            key=lambda token: (int(self._token_df.get(token, corpus_size)), token),
        )[:_MAX_INFORMATIVE_QUERY_TOKENS]
        pool_limit = max_candidates * _MAX_CANDIDATE_POOL_MULTIPLIER
        if len(name_candidate_ids) > pool_limit:
            name_candidate_ids = set(sorted(name_candidate_ids)[:pool_limit])
        # Suffix/fuzzy name matches receive a strong cheap-stage prior but are
        # still subject to the detailed-scoring cap.  Only true exact-name
        # matches sit outside that cap.  Accumulate the complete posting-list
        # union at this cheap stage: truncating the first rare-token posting
        # at ``pool_limit`` made results depend on declaration order and could
        # omit a late declaration matching several query tokens.  The costly
        # declaration scorer remains capped below; this accumulator is bounded
        # by the finite index and cooperatively observes the caller deadline.
        cheap_scores: Dict[int, float] = {
            entry_id: 1_000_000.0 for entry_id in name_candidate_ids
        }
        for token in informative_tokens:
            try:
                if deadline_exhausted and deadline_exhausted():
                    break
            except Exception:
                break
            postings = self._token_index.get(token, ())
            df = max(1, int(self._token_df.get(token, len(postings) or 1)))
            token_weight = math.log(1.0 + (corpus_size / df))
            for posting_index, entry_id in enumerate(postings):
                if posting_index % 256 == 0:
                    try:
                        if deadline_exhausted and deadline_exhausted():
                            break
                    except Exception:
                        break
                cheap_scores[entry_id] = (
                    cheap_scores.get(entry_id, 0.0) + token_weight
                )

        if not cheap_scores and query_tokens:
            for token in query_tokens[:3]:
                for close in self._cooperative_close_name_matches(
                    token,
                    n=8,
                    cutoff=0.8,
                    deadline_exhausted=deadline_exhausted,
                ):
                    for entry_id in self._name_index.get(close, ()):
                        cheap_scores.setdefault(entry_id, 0.0)

        ranked = sorted(
            cheap_scores,
            key=lambda entry_id: (-cheap_scores[entry_id], entry_id),
        )
        exact_ranked = sorted(exact_candidate_ids)
        exact_set = set(exact_ranked)
        return exact_ranked + [
            entry_id
            for entry_id in ranked
            if entry_id not in exact_set
        ][:max_candidates]

    def _cooperative_close_name_matches(
        self,
        query: str,
        *,
        n: int,
        cutoff: float,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> List[str]:
        """Return fuzzy name matches without an uninterruptible corpus scan."""

        limit = max(0, int(n or 0))
        if limit <= 0:
            return []
        matcher = difflib.SequenceMatcher()
        matcher.set_seq2(str(query or ""))
        heap: List[Tuple[float, str]] = []
        for name_index, name in enumerate(self._name_corpus):
            if name_index % 32 == 0:
                try:
                    if deadline_exhausted and deadline_exhausted():
                        break
                except Exception:
                    break
            matcher.set_seq1(name)
            if (
                matcher.real_quick_ratio() < cutoff
                or matcher.quick_ratio() < cutoff
            ):
                continue
            ratio = matcher.ratio()
            if ratio < cutoff:
                continue
            item = (ratio, name)
            if len(heap) < limit:
                heapq.heappush(heap, item)
            elif item > heap[0]:
                heapq.heapreplace(heap, item)
        return [name for _ratio, name in sorted(heap, reverse=True)]

    def _score_entry(
        self,
        entry: Any,
        entry_tokens: Counter[str],
        query_text: str,
        query_tokens: List[str],
    ) -> Optional[MathlibApiSearchHit]:
        query_token_set = set(query_tokens)
        entry_token_set = set(entry_tokens.keys())
        score = 0.0
        reasons: List[str] = []
        details: Dict[str, float] = {}

        stripped = str(query_text or "").strip()
        lowered = stripped.lower()
        entry_name = str(getattr(entry, "name", "") or "").strip()
        entry_name_lower = entry_name.lower()
        name_tokens = set(_tokenize(entry_name))

        if lowered and entry_name_lower == lowered:
            score += 5.0
            reasons.append("exact_name")
            details["exact"] = 1.0
        elif lowered and (
            entry_name_lower.endswith(f".{lowered}")
            or entry_name_lower.split(".")[-1] == lowered
        ):
            score += 3.0
            reasons.append("suffix_name")
            details["exact"] = 0.8
        else:
            details["exact"] = 0.0

        fuzzy = 0.0
        if lowered and len(lowered) <= _MAX_FUZZY_QUERY_CHARS:
            fuzzy = max(
                difflib.SequenceMatcher(None, lowered, entry_name_lower).ratio(),
                difflib.SequenceMatcher(
                    None, lowered, entry_name_lower.split(".")[-1]
                ).ratio(),
            )
        if fuzzy >= 0.75:
            score += 1.5 * fuzzy
            reasons.append("fuzzy_name")
        details["fuzzy"] = float(fuzzy)
        name_overlap = query_token_set & name_tokens
        if name_overlap:
            score += 1.25 * float(len(name_overlap))
            reasons.append("name_token_overlap")
        details["name_overlap"] = float(len(name_overlap))

        lexical = 0.0
        if query_token_set and entry_token_set:
            overlap = query_token_set & entry_token_set
            if overlap:
                lexical = len(overlap) / max(1.0, math.sqrt(len(query_token_set) * len(entry_token_set)))
                score += 1.5 * lexical
                reasons.append("token_overlap")
                overlap_count = len(overlap)
                corpus_size = max(1, len(self._entries))
                idf_overlap = 0.0
                for token in overlap:
                    df = max(1, int(self._token_df.get(token, 0)))
                    idf_overlap += math.log(1.0 + (corpus_size / df))
                score += 0.9 * idf_overlap
                details["idf_overlap"] = float(idf_overlap)
                details["overlap_count"] = float(overlap_count)
                if overlap_count >= 2:
                    score += 0.75 + 0.25 * float(min(3, overlap_count - 2))
                    reasons.append("multi_token_overlap")
                elif len(query_token_set) >= 4:
                    lone_token = next(iter(overlap))
                    if lone_token in _GENERIC_QUERY_TOKENS:
                        score -= 0.75
                        reasons.append("generic_single_token_penalty")
        details["lexical"] = float(lexical)

        if score <= 0.0:
            return None
        return MathlibApiSearchHit(
            entry=entry,
            score=float(score),
            reasons=tuple(reasons),
            details=details,
        )
