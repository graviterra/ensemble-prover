"""Federated retrieval over Mathlib, project, theory, and verified helpers."""

from __future__ import annotations

import hashlib
import inspect
import math
import queue
import re
import threading
import time
import weakref
from collections import defaultdict
from dataclasses import dataclass, replace
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Callable, Mapping, Optional, Protocol, Sequence

from ..putnam import (
    is_putnam_bench_problem_declaration,
    is_putnam_bench_problem_source,
)
from ..theorem_project import scan_lean_declarations

from .model import (
    CandidateOrigin,
    RetrievalCandidate,
    RetrievalQuery,
    RetrievalResult,
    RetrievalSourcePolicy,
    RetrievalSourceReport,
    stable_retrieval_hash,
)


_ENTRY_KINDS = frozenset({"theorem", "lemma", "axiom"})
_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|[∀∃→↔=<>≤≥∈∉⊆∣∧∨¬≠]")
_BINDER_RE = re.compile(
    r"([({]\s*)([A-Za-z_][A-Za-z0-9_']*)(\s*:\s*)"
)
_SYMBOL_NAMES = {
    "∀": "forall",
    "∃": "exists",
    "→": "arrow",
    "↔": "iff",
    "=": "eq",
    "≠": "ne",
    "<": "lt",
    ">": "gt",
    "≤": "le",
    "≥": "ge",
    "∈": "mem",
    "∉": "not_mem",
    "⊆": "subset",
    "∣": "dvd",
    "∧": "and",
    "∨": "or",
    "¬": "not",
}
_AVAILABILITY_ORDER = {
    "already_imported": 0,
    "requires_helper_recheck": 1,
    "requires_bundle_activation": 2,
    "importable": 3,
    "unknown": 4,
    "unavailable": 5,
}
_MAX_LAZY_TYPE_INDEX_ENTRIES = 2_000
_MAX_QUERY_SCOPED_TYPE_ENTRIES = 128
_MAX_TYPE_POSTING_ACCUMULATION = 8_192
_RUNTIME_CONTEXT_SCHEMA_VERSION = 4
_LEGACY_RUNTIME_CORPUS_SCHEMA_VERSION = 2
_LEGACY_RUNTIME_CONTEXT_SCHEMA_VERSION = 3
_RLOCK_TYPE = type(threading.RLock())
_BOUNDED_SEMAPHORE_TYPE = type(threading.BoundedSemaphore(1))
_SOURCE_SLOT_LOCK = threading.Lock()
_SOURCE_SLOTS: dict[
    int, tuple[weakref.ReferenceType[Any], threading.BoundedSemaphore]
] = {}
_BACKEND_LOCK_GUARD = threading.Lock()
_BACKEND_LOCKS: dict[int, tuple[weakref.ReferenceType[Any], threading.RLock]] = {}


def _backend_operation_lock(backend: Any) -> threading.RLock:
    """Canonical operation lock for every alias of one backend object."""

    key = id(backend)
    try:
        backend_ref = weakref.ref(backend)
    except TypeError:
        existing = getattr(backend, "_mini_retrieval_operation_lock", None)
        if isinstance(existing, _RLOCK_TYPE):
            return existing
        lock = threading.RLock()
        try:
            setattr(backend, "_mini_retrieval_operation_lock", lock)
        except Exception as exc:
            raise TypeError(
                "retrieval backend must support weak references or attributes"
            ) from exc
        return lock
    with _BACKEND_LOCK_GUARD:
        existing = _BACKEND_LOCKS.get(key)
        if existing is not None and existing[0]() is backend:
            return existing[1]
        lock = threading.RLock()

        def cleanup(ref: weakref.ReferenceType[Any]) -> None:
            with _BACKEND_LOCK_GUARD:
                current = _BACKEND_LOCKS.get(key)
                if current is not None and current[0] is ref:
                    _BACKEND_LOCKS.pop(key, None)

        backend_ref = weakref.ref(backend, cleanup)
        _BACKEND_LOCKS[key] = (backend_ref, lock)
        return lock


def _source_worker_slot(
    source: "MathematicalRetrievalSource",
) -> threading.BoundedSemaphore:
    """Return a per-backend bulkhead shared by all session forks.

    Python cannot kill an arbitrary cancellation-resistant thread. A global
    semaphore therefore lets one hung provider consume every future adapter
    slot. One detached worker per backend bounds leaks while preserving other
    Mathlib/project/theory/helper sources.
    """

    backend = next(
        (
            getattr(source, attr)
            for attr in ("searcher", "retriever", "library", "cache")
            if getattr(source, attr, None) is not None
        ),
        source,
    )
    key = id(backend)
    try:
        weakref.ref(backend)
    except TypeError:
        existing = getattr(backend, "_mini_retrieval_worker_slot", None)
        if isinstance(existing, _BOUNDED_SEMAPHORE_TYPE):
            return existing
        slot = threading.BoundedSemaphore(1)
        try:
            setattr(backend, "_mini_retrieval_worker_slot", slot)
        except Exception as exc:
            raise TypeError(
                "retrieval backend must support weak references or attributes"
            ) from exc
        return slot
    with _SOURCE_SLOT_LOCK:
        existing = _SOURCE_SLOTS.get(key)
        if existing is not None and existing[0]() is backend:
            return existing[1]
        slot = threading.BoundedSemaphore(1)

        def cleanup(ref: weakref.ReferenceType[Any]) -> None:
            with _SOURCE_SLOT_LOCK:
                current = _SOURCE_SLOTS.get(key)
                if current is not None and current[0] is ref:
                    _SOURCE_SLOTS.pop(key, None)

        backend_ref = weakref.ref(backend, cleanup)
        _SOURCE_SLOTS[key] = (backend_ref, slot)
        return slot


def _entry_value(entry: Any, field: str, default: Any = "") -> Any:
    if isinstance(entry, Mapping):
        return entry.get(field, default)
    return getattr(entry, field, default)


def _entry_name(entry: Any) -> str:
    return str(_entry_value(entry, "name", "") or "").strip()


def _entry_type(entry: Any) -> str:
    return " ".join(str(_entry_value(entry, "type", "") or "").split())


def _entry_kind(entry: Any) -> str:
    return str(_entry_value(entry, "kind", "") or "").strip().lower()


def _is_putnam_bench_problem_entry(entry: Any) -> bool:
    return is_putnam_bench_problem_source(
        str(_entry_value(entry, "file", "") or "")
    ) or is_putnam_bench_problem_declaration(_entry_name(entry))


def _helper_record_id(record: Mapping[str, Any]) -> str:
    """Hash every retrieval-relevant field of one durable helper row."""

    return stable_retrieval_hash(
        {
            "name": str(record.get("name") or "").strip(),
            "statement": str(
                record.get("statement_preview") or record.get("statement") or ""
            ).strip(),
            "source_hash": str(record.get("source_hash") or "").strip(),
            "theorem_name": str(record.get("theorem_name") or "").strip(),
        }
    )


def _deadline_elapsed(deadline_monotonic: Optional[float]) -> bool:
    return bool(
        deadline_monotonic is not None
        and time.monotonic() >= float(deadline_monotonic)
    )


def _retrieval_elapsed(
    deadline_monotonic: Optional[float],
    deadline_exhausted: Optional[Callable[[], bool]],
) -> bool:
    if _deadline_elapsed(deadline_monotonic):
        return True
    if deadline_exhausted is None:
        return False
    try:
        return bool(deadline_exhausted())
    except Exception:
        return True


def _safe_error(exc: BaseException) -> str:
    text = " ".join(str(exc or "").split())
    return f"{type(exc).__name__}: {text}"[:500]


def _content_hash(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _entry_corpus_hash(
    entries: Sequence[Any],
    *,
    root: Path | None = None,
    include_source_content: bool = False,
) -> str:
    """Hash declaration content without binding identity to checkout location."""

    digest = hashlib.sha256()
    source_files: dict[str, Path] = {}
    canonical_entries: list[tuple[tuple[str, ...], Path, str]] = []
    for entry in entries:
        source_path = Path(str(_entry_value(entry, "file", "") or ""))
        if root is not None:
            try:
                stable_path = str(source_path.resolve().relative_to(root.resolve()))
            except (OSError, ValueError):
                stable_path = source_path.name
        else:
            stable_path = _module_from_path(str(source_path)) or source_path.name
        values = (
            _entry_name(entry), _entry_type(entry), _entry_kind(entry),
            stable_path, str(_entry_value(entry, "namespace", "") or ""),
            str(_entry_value(entry, "docstring", "") or ""),
            str(_entry_value(entry, "source", "") or ""),
        )
        canonical_entries.append((values, source_path, stable_path))
    for values, source_path, stable_path in sorted(
        canonical_entries,
        key=lambda item: item[0],
    ):
        for value in values:
            digest.update(str(value).encode("utf-8", errors="replace"))
            digest.update(b"\0")
        if include_source_content:
            source_files.setdefault(stable_path, source_path)
    if include_source_content:
        for stable_path, source_path in sorted(source_files.items()):
            digest.update(stable_path.encode("utf-8", errors="replace"))
            digest.update(b"\0")
            try:
                digest.update(hashlib.sha256(source_path.read_bytes()).digest())
            except OSError:
                digest.update(b"<unavailable>")
    return digest.hexdigest()


def _project_source_manifest_hash(root: Path) -> str:
    """Hash every elaboration-bearing project source/config file stably."""

    digest = hashlib.sha256()
    excluded = {".lake", ".git", "build", "external", "Temp"}
    paths = [
        path
        for path in root.rglob("*.lean")
        if not any(part in excluded for part in path.relative_to(root).parts)
    ]
    paths.extend(
        path
        for name in (
            "lakefile.lean",
            "lakefile.toml",
            "lean-toolchain",
            "lake-manifest.json",
        )
        if (path := root / name).is_file()
    )
    for path in sorted(set(paths), key=lambda item: str(item.relative_to(root))):
        relative = str(path.relative_to(root))
        digest.update(relative.encode("utf-8", errors="replace"))
        digest.update(b"\0")
        try:
            digest.update(hashlib.sha256(path.read_bytes()).digest())
        except OSError:
            digest.update(b"<unavailable>")
    return digest.hexdigest()


def _module_from_path(path: str, *, project_root: Optional[Path] = None) -> str:
    candidate = Path(str(path or ""))
    parts = list(candidate.with_suffix("").parts)
    if "Mathlib" in parts:
        return ".".join(parts[parts.index("Mathlib") :])
    if project_root is not None:
        try:
            relative = candidate.resolve().relative_to(project_root.resolve())
            return ".".join(relative.with_suffix("").parts)
        except (OSError, ValueError):
            pass
    return ""


def lake_module_roots(project_root: Path) -> tuple[Path, ...]:
    """Resolve declared Lake source roots used to map files to module names."""

    requested_root = Path(project_root).resolve()
    root = requested_root
    for candidate in (requested_root, *requested_root.parents):
        if any(
            (candidate / manifest).is_file()
            for manifest in ("lakefile.lean", "lakefile.toml")
        ):
            root = candidate.resolve()
            break
    relative_roots: list[str] = []
    for manifest_name in ("lakefile.lean", "lakefile.toml"):
        manifest = root / manifest_name
        try:
            text = manifest.read_text(encoding="utf-8")
        except OSError:
            continue
        for match in re.finditer(
            r"\bsrcDir\s*(?::=|=)\s*[\"']([^\"']+)[\"']",
            text,
        ):
            value = str(match.group(1) or "").strip()
            if value and value not in relative_roots:
                relative_roots.append(value)
    resolved = [
        (root / relative).resolve()
        for relative in relative_roots
        if (root / relative).is_dir()
    ]
    if root.resolve() not in resolved:
        resolved.append(root.resolve())
    return tuple(sorted(resolved, key=lambda item: (-len(item.parts), str(item))))


def _normalized_analogy_tokens(text: str) -> frozenset[str]:
    normalized = _BINDER_RE.sub(r"\1_\3", str(text or ""))
    normalized = normalized.replace("->", "→").replace("=>", "→")
    tokens: set[str] = set()
    for token in _TOKEN_RE.findall(normalized):
        mapped = _SYMBOL_NAMES.get(token, token.lower().split(".")[-1])
        if mapped and mapped not in {"theorem", "lemma", "def", "by"}:
            tokens.add(mapped)
    return frozenset(tokens)


def _analogy_score(query_text: str, candidate_type: str) -> float:
    left = _normalized_analogy_tokens(query_text)
    right = _normalized_analogy_tokens(candidate_type)
    if not left or not right:
        return 0.0
    return len(left & right) / max(1.0, math.sqrt(len(left) * len(right)))


@dataclass(frozen=True)
class SourceHit:
    entry: Any
    score: float
    channel: str
    origin: CandidateOrigin
    reasons: tuple[str, ...] = ()
    details: Mapping[str, float] | None = None


@dataclass(frozen=True)
class SourceSearchResult:
    hits: tuple[SourceHit, ...]
    report: RetrievalSourceReport


class MathematicalRetrievalSource(Protocol):
    source_id: str
    source_kind: str

    def snapshot_id(self) -> str: ...

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult: ...

    def iter_entries(self) -> Sequence[Any]: ...


class AnswerSafePreambleSource:
    """Session-local declarations that are already visible before the target.

    Generic theorem files are intentionally held out from project indexing so
    their target declaration/body cannot leak into proof search.  That safety
    boundary must not also hide definitions and lemmas in the answer-safe
    preamble.  This source indexes only the pre-extracted preamble text and
    advertises every entry as already active in the current Lean environment.
    """

    source_kind = "project"

    def __init__(
        self,
        preamble: str,
        *,
        lean_preamble: Optional[str] = None,
        theorem_name: str = "",
        source_path: str = "",
        source_id: str = "answer_safe_preamble",
        environment_hash: str = "",
    ) -> None:
        self.source_id = str(source_id or "answer_safe_preamble")
        self.environment_hash = str(environment_hash or "")
        self.theorem_name = str(theorem_name or "").strip()
        self.preamble_hash = hashlib.sha256(
            str(preamble or "").encode("utf-8")
        ).hexdigest()
        executable_preamble = (
            str(preamble or "")
            if lean_preamble is None
            else str(lean_preamble or "")
        )
        self.lean_preamble_hash = hashlib.sha256(
            executable_preamble.encode("utf-8")
        ).hexdigest()
        provenance_path = str(source_path or "<answer-safe-preamble>")
        # Deliberately distinguish this extracted region from the held-out
        # whole source path.  The exact target name is independently excluded.
        self.source_path = f"{provenance_path}#answer-safe-preamble"
        entries: list[Any] = []
        try:
            declarations = scan_lean_declarations(str(preamble or ""))
        except ValueError:
            declarations = ()
        try:
            executable_declarations = scan_lean_declarations(executable_preamble)
        except ValueError:
            executable_declarations = ()
        executable_types = {
            str(declaration.canonical_name or "").strip(): re.sub(
                r"\s+",
                "",
                str(declaration.statement_type or ""),
            )
            for declaration in executable_declarations
            if str(declaration.canonical_name or "").strip()
        }
        for declaration in declarations:
            name = str(declaration.canonical_name or "").strip()
            statement_type = str(declaration.statement_type or "").strip()
            if (
                not name
                or name == self.theorem_name
                or name.endswith("_solution")
                or executable_types.get(name)
                != re.sub(r"\s+", "", statement_type)
            ):
                continue
            entries.append(
                SimpleNamespace(
                    name=name,
                    type=statement_type,
                    kind=str(declaration.kind or "").strip(),
                    file=self.source_path,
                    namespace=".".join(declaration.namespace),
                    docstring=str(declaration.docstring or "").strip(),
                    source="answer_safe_preamble",
                )
            )
        self._entries = tuple(entries)

    def snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "preamble_hash": self.preamble_hash,
                "lean_preamble_hash": self.lean_preamble_hash,
                "theorem_name": self.theorem_name,
                "environment_hash": self.environment_hash,
                "entries": [
                    (_entry_name(entry), _entry_type(entry), _entry_kind(entry))
                    for entry in self._entries
                ],
            }
        )

    def iter_entries(self) -> Sequence[Any]:
        return self._entries

    def _origin(self, entry: Any) -> CandidateOrigin:
        return CandidateOrigin(
            source_kind=self.source_kind,
            source_id=self.source_id,
            source_path=str(_entry_value(entry, "file", self.source_path) or ""),
            source_hash=self.preamble_hash,
            environment_hash=self.environment_hash,
            trust_kind="active_environment_declaration",
            availability="already_imported",
        )

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult:
        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "timeout",
                    index_snapshot_id=self.snapshot_id(),
                ),
            )
        query_text = " ".join(
            item
            for item in (
                query.natural_language,
                query.target_statement,
                query.route_context,
                *query.ordered_local_context,
            )
            if item
        )
        query_tokens = {
            match.group(0).lower() for match in _TOKEN_RE.finditer(query_text)
        }
        scored: list[tuple[float, Any, tuple[str, ...]]] = []
        for entry in self._entries:
            if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
                break
            kind = _entry_kind(entry)
            if query.source_policy.theorem_kinds_only and kind not in _ENTRY_KINDS:
                continue
            name = _entry_name(entry)
            entry_tokens = {
                match.group(0).lower()
                for match in _TOKEN_RE.finditer(
                    " ".join(
                        (
                            name,
                            _entry_type(entry),
                            str(_entry_value(entry, "docstring", "") or ""),
                        )
                    )
                )
            }
            overlap = query_tokens & entry_tokens
            if not overlap:
                continue
            score = len(overlap) / max(1, len(query_tokens))
            lowered_name = name.lower()
            if any(token in lowered_name for token in query_tokens):
                score += 0.25
            scored.append((score, entry, tuple(sorted(overlap))))
        scored.sort(key=lambda item: (-item[0], _entry_name(item[1])))
        hits = tuple(
            SourceHit(
                entry=entry,
                score=float(score),
                channel="answer_safe_preamble_lexical",
                origin=self._origin(entry),
                reasons=("answer_safe_preamble", *overlap[:6]),
                details={"lexical_overlap": float(score)},
            )
            for score, entry, overlap in scored[: max(0, int(max_results or 0))]
        )
        truncated = _retrieval_elapsed(deadline_monotonic, deadline_exhausted)
        return SourceSearchResult(
            hits,
            RetrievalSourceReport(
                self.source_id,
                self.source_kind,
                (
                    "degraded"
                    if hits and truncated
                    else (
                        "timeout"
                        if truncated
                        else ("success_with_hits" if hits else "success_zero_hits")
                    )
                ),
                hit_count=len(hits),
                elapsed_s=time.monotonic() - started,
                index_snapshot_id=self.snapshot_id(),
                truncated=truncated,
            ),
        )


class StaticMathlibSource:
    source_kind = "mathlib"

    def __init__(
        self,
        searcher: Any,
        *,
        source_id: str = "mathlib_api",
        environment_hash: str = "",
        active_imports: Sequence[str] = (),
        searcher_lock: threading.RLock | None = None,
        compatibility_corpus_hash: str = "",
    ) -> None:
        self.searcher = searcher
        self.source_id = str(source_id)
        self.environment_hash = str(environment_hash or "")
        self.base_imports = frozenset(str(item).strip() for item in active_imports)
        self.active_imports = self.base_imports
        self.searcher_lock = searcher_lock or _backend_operation_lock(searcher)
        with self.searcher_lock:
            self._entry_snapshot = tuple(
                getattr(self.searcher, "_entries", ()) or ()
            )
        self._compatibility_corpus_hash = str(compatibility_corpus_hash or "")
        if not self._compatibility_corpus_hash:
            self._compatibility_corpus_hash = _entry_corpus_hash(
                self._entry_snapshot
            )

    def mark_imported(self, module_name: str) -> None:
        clean = str(module_name or "").strip()
        if clean:
            self.active_imports = frozenset((*self.active_imports, clean))

    def reset_imports(self) -> None:
        self.active_imports = self.base_imports

    def snapshot_id(self) -> str:
        # This method is used both before and after an abandonment-safe search.
        # It must never wait for the adapter lock: a timed-out backend may
        # still own that lock in its detached daemon worker.
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "corpus_hash": self._compatibility_corpus_hash,
                "backend_entry_count": len(
                    getattr(self.searcher, "_entries", ()) or ()
                ),
                "backend_epoch": str(
                    getattr(
                        self.searcher,
                        "generation",
                        getattr(self.searcher, "epoch", ""),
                    )
                    or ""
                ),
                "environment_hash": self.environment_hash,
                "active_imports": sorted(self.active_imports),
            }
        )

    def compatibility_snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "corpus_hash": self._compatibility_corpus_hash,
                "environment_hash": self.environment_hash,
            }
        )

    def iter_entries(self) -> Sequence[Any]:
        return self._entry_snapshot

    def _origin(self, entry: Any) -> CandidateOrigin:
        source_path = str(_entry_value(entry, "file", "") or "")
        module_name = _module_from_path(source_path)
        imported = "Mathlib" in self.active_imports or module_name in self.active_imports
        return CandidateOrigin(
            source_kind=self.source_kind,
            source_id=self.source_id,
            module_name=module_name,
            import_text=f"import {module_name}" if module_name else "",
            source_path=source_path,
            source_hash="",
            environment_hash=self.environment_hash,
            trust_kind=(
                "active_environment_declaration"
                if imported
                else "unverified_index_hint"
            ),
            availability=(
                "already_imported"
                if imported
                else ("importable" if module_name else "unknown")
            ),
        )

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult:
        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "timeout",
                    elapsed_s=0.0,
                    index_snapshot_id=self.snapshot_id(),
                ),
            )
        try:
            with self.searcher_lock:
                scored: list[Any] = []
                kinds = (
                    ("theorem_like",)
                    if query.source_policy.theorem_kinds_only
                    else ("any",)
                )
                for kind in kinds:
                    scored.extend(
                        self.searcher.search_with_scores(
                            " ".join(
                                item
                                for item in (
                                    query.natural_language
                                    or query.target_statement,
                                    query.route_context,
                                )
                                if item
                            ),
                            goal_state="\n".join(query.ordered_local_context),
                            kind=kind,
                            max_results=max_results,
                            deadline_exhausted=(
                                lambda: _retrieval_elapsed(
                                    deadline_monotonic,
                                    deadline_exhausted,
                                )
                            ),
                        )
                        or ()
                    )
            by_name: dict[str, Any] = {}
            for hit in scored:
                name = _entry_name(getattr(hit, "entry", None))
                previous = by_name.get(name)
                if name and (
                    previous is None
                    or float(getattr(hit, "score", 0.0) or 0.0)
                    > float(getattr(previous, "score", 0.0) or 0.0)
                ):
                    by_name[name] = hit
            scored = sorted(
                by_name.values(),
                key=lambda hit: (
                    -float(getattr(hit, "score", 0.0) or 0.0),
                    _entry_name(getattr(hit, "entry", None)),
                ),
            )[:max_results]
            hits = tuple(
                SourceHit(
                    entry=hit.entry,
                    score=float(getattr(hit, "score", 0.0) or 0.0),
                    channel="mathlib_lexical",
                    origin=self._origin(hit.entry),
                    reasons=tuple(getattr(hit, "reasons", ()) or ()),
                    details=dict(getattr(hit, "details", {}) or {}),
                )
                for hit in list(scored or ())
                if _entry_name(getattr(hit, "entry", None))
            )
            source_truncated = _retrieval_elapsed(
                deadline_monotonic,
                deadline_exhausted,
            )
            health = (
                "degraded"
                if hits and source_truncated
                else (
                    "timeout"
                    if source_truncated
                    else ("success_with_hits" if hits else "success_zero_hits")
                )
            )
            report = RetrievalSourceReport(
                self.source_id,
                self.source_kind,
                health,
                hit_count=len(hits),
                elapsed_s=time.monotonic() - started,
                error=(
                    "source deadline reached; partial hits retained"
                    if hits and source_truncated
                    else ""
                ),
                index_snapshot_id=self.snapshot_id(),
                truncated=source_truncated,
            )
            return SourceSearchResult(hits, report)
        except Exception as exc:
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "error",
                    elapsed_s=time.monotonic() - started,
                    error=_safe_error(exc),
                    index_snapshot_id=self.snapshot_id(),
                ),
            )


class ProjectSupportSource:
    source_kind = "project"

    def __init__(
        self,
        retriever: Any,
        *,
        project_root: Path,
        source_id: str,
        environment_hash: str = "",
        active_imports: Sequence[str] = (),
        retriever_lock: threading.RLock | None = None,
        compatibility_corpus_hash: str = "",
        active_declarations: Sequence[Sequence[str]] = (),
        module_roots: Sequence[Path] = (),
        source_manifest_hash: str = "",
        dense_artifact_hash: str = "",
        dense_meta_hash: str = "",
    ) -> None:
        self.retriever = retriever
        self.project_root = Path(project_root)
        self.source_id = str(source_id)
        self.environment_hash = str(environment_hash or "")
        self.base_imports = frozenset(str(item).strip() for item in active_imports)
        self.active_imports = self.base_imports
        self.retriever_lock = retriever_lock or _backend_operation_lock(retriever)
        self.active_declarations = frozenset(
            tuple(str(part or "").strip() for part in item)
            for item in active_declarations
            if len(tuple(item)) == 3
        )
        self.module_roots = tuple(module_roots) or lake_module_roots(
            self.project_root
        )
        with self.retriever_lock:
            index = getattr(self.retriever, "index", None)
            self._entry_snapshot = tuple(getattr(index, "entries", ()) or ())
        self._compatibility_corpus_hash = str(compatibility_corpus_hash or "")
        if not self._compatibility_corpus_hash:
            self._compatibility_corpus_hash = _entry_corpus_hash(
                self._entry_snapshot,
                root=self.project_root,
                include_source_content=True,
            )
        self._source_manifest_hash = str(source_manifest_hash or "")
        if not self._source_manifest_hash:
            self._source_manifest_hash = _project_source_manifest_hash(
                self.project_root
            )
        cfg = getattr(self.retriever, "cfg", None)
        self._dense_artifact_hash = str(dense_artifact_hash or "") or _content_hash(
            Path(str(getattr(cfg, "dense_index_path", "") or ""))
        )
        self._dense_meta_hash = str(dense_meta_hash or "") or _content_hash(
            Path(str(getattr(cfg, "dense_meta_path", "") or ""))
        )

    def mark_imported(self, module_name: str) -> None:
        clean = str(module_name or "").strip()
        if clean:
            self.active_imports = frozenset((*self.active_imports, clean))

    def reset_imports(self) -> None:
        self.active_imports = self.base_imports
        self.active_declarations = frozenset()

    def mark_declaration_imported(
        self,
        module_name: str,
        declaration_name: str,
        declaration_type: str,
    ) -> None:
        key = (
            str(module_name or "").strip(),
            str(declaration_name or "").strip(),
            stable_retrieval_hash(" ".join(str(declaration_type or "").split())),
        )
        if all(key):
            self.active_declarations = frozenset((*self.active_declarations, key))

    def snapshot_id(self) -> str:
        current_index = getattr(self.retriever, "index", None)
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "corpus_hash": self._compatibility_corpus_hash,
                "source_manifest_hash": self._source_manifest_hash,
                "backend_index_identity": id(current_index),
                "backend_entry_count": len(
                    getattr(current_index, "entries", ()) or ()
                ),
                "dense_ready": bool(
                    getattr(self.retriever, "_dense_ready", False)
                ),
                "environment_hash": self.environment_hash,
                "active_imports": sorted(self.active_imports),
                "active_declarations": sorted(self.active_declarations),
            }
        )

    def compatibility_snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "corpus_hash": self._compatibility_corpus_hash,
                "source_manifest_hash": self._source_manifest_hash,
                "environment_hash": self.environment_hash,
            }
        )

    def iter_entries(self) -> Sequence[Any]:
        return tuple(
            entry
            for entry in self._entry_snapshot
            if not _is_putnam_bench_problem_entry(entry)
        )

    def _origin(self, entry: Any) -> CandidateOrigin:
        source_path = str(_entry_value(entry, "file", "") or "")
        module_name = next(
            (
                module
                for root in self.module_roots
                if (module := _module_from_path(source_path, project_root=root))
            ),
            "",
        )
        declaration_key = (
            module_name,
            _entry_name(entry),
            stable_retrieval_hash(_entry_type(entry)),
        )
        imported = declaration_key in self.active_declarations
        return CandidateOrigin(
            source_kind=self.source_kind,
            source_id=self.source_id,
            module_name=module_name,
            import_text=f"import {module_name}" if module_name else "",
            source_path=source_path,
            source_hash="",
            environment_hash=self.environment_hash,
            trust_kind=(
                "active_environment_declaration"
                if imported
                else "unverified_index_hint"
            ),
            availability="already_imported" if imported else "importable",
        )

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult:
        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "timeout",
                    index_snapshot_id=self.snapshot_id(),
                ),
            )
        try:
            with self.retriever_lock:
                retrieve_kwargs = {
                    "goal_state": "\n".join(query.ordered_local_context),
                    "max_results": (
                        max_results * 4
                        if query.source_policy.theorem_kinds_only
                        else max_results
                    ),
                    "deadline_exhausted": lambda: _retrieval_elapsed(
                        deadline_monotonic,
                        deadline_exhausted,
                    ),
                    "deadline_monotonic": deadline_monotonic,
                }
                statement = " ".join(
                    item
                    for item in (
                        query.natural_language or query.target_statement,
                        query.route_context,
                    )
                    if item
                )
                # Keep third-party/test retrievers source-compatible while
                # production LemmaRetriever uses cooperative deadlines.  An
                # older explicit signature may reject the two new keywords
                # one at a time, so negotiate each named incompatibility with
                # a bounded retry instead of assuming one retry is sufficient.
                while True:
                    try:
                        _local, scored = self.retriever.retrieve_with_scores(
                            statement,
                            **retrieve_kwargs,
                        )
                        break
                    except TypeError as exc:
                        unsupported = {
                            key
                            for key in (
                                "deadline_exhausted",
                                "deadline_monotonic",
                            )
                            if key in str(exc) and key in retrieve_kwargs
                        }
                        if not unsupported:
                            raise
                        for key in unsupported:
                            retrieve_kwargs.pop(key, None)
            scored = [
                item
                for item in list(scored or ())
                if not _is_putnam_bench_problem_entry(item[0])
            ]
            if query.source_policy.theorem_kinds_only:
                scored = [
                    item
                    for item in list(scored or ())
                    if _entry_kind(item[0]) in _ENTRY_KINDS
                ][:max_results]
            hits = tuple(
                SourceHit(
                    entry=entry,
                    score=float(score),
                    channel="project_hybrid",
                    origin=self._origin(entry),
                    reasons=tuple(
                        key
                        for key, value in dict(details or {}).items()
                        if float(value or 0.0) > 0.0
                    ),
                    details=dict(details or {}),
                )
                for entry, score, details in list(scored or ())
            )
            semantic_missing = bool(
                getattr(self.retriever, "_mini_semantic_requested", False)
                and not getattr(
                    self.retriever,
                    "_mini_semantic_available",
                    False,
                )
            )
            dense_missing = bool(
                getattr(self.retriever, "_mini_dense_requested", False)
                and not getattr(self.retriever, "_dense_ready", False)
            )
            source_truncated = _retrieval_elapsed(
                deadline_monotonic,
                deadline_exhausted,
            )
            health = (
                "degraded"
                if hits and (semantic_missing or dense_missing or source_truncated)
                else (
                    "timeout"
                    if source_truncated
                    else (
                        "success_with_hits"
                        if hits
                        else (
                            "unavailable"
                            if semantic_missing or dense_missing
                            else "success_zero_hits"
                        )
                    )
                )
            )
            degradation_error = ""
            if semantic_missing or dense_missing:
                degradation_error = str(
                    getattr(self.retriever, "_mini_semantic_init_error", "")
                    or getattr(self.retriever, "_embedder_init_error", "")
                    or (
                        "requested semantic/dense retrieval channel unavailable"
                    )
                )
            if source_truncated:
                degradation_error = " ".join(
                    item
                    for item in (
                        degradation_error,
                        "source deadline reached; partial hits retained"
                        if hits
                        else "source deadline reached",
                    )
                    if item
                )
            return SourceSearchResult(
                hits,
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    health,
                    hit_count=len(hits),
                    elapsed_s=time.monotonic() - started,
                    error=degradation_error[:500],
                    index_snapshot_id=self.snapshot_id(),
                    truncated=source_truncated,
                ),
            )
        except Exception as exc:
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "error",
                    elapsed_s=time.monotonic() - started,
                    error=_safe_error(exc),
                    index_snapshot_id=self.snapshot_id(),
                ),
            )


class PublishedTheorySource:
    source_kind = "published_theory"

    def __init__(
        self,
        library: Any,
        *,
        source_id: str = "mini_theory",
        environment_hash: str = "",
        active_bundle_ids: Callable[[], Sequence[str]] | None = None,
        library_lock: threading.RLock | None = None,
        bundle_generation: Optional[Mapping[str, str]] = None,
        entry_snapshot: Optional[Sequence[Any]] = None,
    ) -> None:
        self.library = library
        self.source_id = str(source_id)
        self.environment_hash = str(environment_hash or "")
        self._active_bundle_ids_provider = active_bundle_ids
        self._active_bundle_id_set: frozenset[str] = frozenset()
        canonical_library_lock = getattr(library, "operation_lock", None)
        self.library_lock = (
            canonical_library_lock
            if isinstance(canonical_library_lock, _RLOCK_TYPE)
            else (library_lock or _backend_operation_lock(library))
        )
        if bundle_generation is None:
            with self.library_lock:
                initial_bundles = list(self.library.store.iter_bundles())
            self._bundle_generation = {
                str(getattr(bundle, "bundle_id", "") or ""): str(
                    getattr(bundle, "manifest_hash", "") or ""
                )
                for bundle in initial_bundles
                if str(getattr(bundle, "bundle_id", "") or "")
            }
        else:
            initial_bundles = []
            self._bundle_generation = {
                str(key): str(value)
                for key, value in bundle_generation.items()
                if str(key)
            }
        self.allowed_bundle_ids: frozenset[str] | None = frozenset(
            self._bundle_generation
        )
        self._entry_snapshot = (
            tuple(entry_snapshot)
            if entry_snapshot is not None
            else self._entries_from_bundles(initial_bundles)
        )
        # Corpus generations are checkpointed separately.  Request snapshot
        # reads intentionally avoid the library lock so an abandoned library
        # search cannot wedge every later retrieval at snapshot acquisition.
        self._base_snapshot_id = stable_retrieval_hash(
            {
                "source": self.source_id,
                "environment_hash": self.environment_hash,
                "mode": str(getattr(self.library, "mode", "") or ""),
            }
        )

    def active_bundle_ids(self) -> tuple[str, ...]:
        if self._active_bundle_ids_provider is not None:
            return tuple(
                str(item).strip()
                for item in self._active_bundle_ids_provider() or ()
                if str(item).strip()
            )
        return tuple(sorted(self._active_bundle_id_set))

    def set_active_bundle_ids(self, bundle_ids: Sequence[str]) -> None:
        self._active_bundle_id_set = frozenset(
            str(item).strip() for item in bundle_ids if str(item).strip()
        )
        missing = self._active_bundle_id_set - set(self._bundle_generation)
        if missing:
            with self.library_lock:
                bundles = list(self.library.store.iter_bundles())
            added_bundles = []
            for bundle in bundles:
                bundle_id = str(getattr(bundle, "bundle_id", "") or "")
                if bundle_id in missing:
                    self._bundle_generation[bundle_id] = str(
                        getattr(bundle, "manifest_hash", "") or ""
                    )
                    added_bundles.append(bundle)
            if added_bundles:
                existing = {
                    (
                        _entry_name(entry),
                        _entry_type(entry),
                        str(_entry_value(entry, "_bundle_id", "") or ""),
                    )
                    for entry in self._entry_snapshot
                }
                additions = tuple(
                    entry
                    for entry in self._entries_from_bundles(added_bundles)
                    if (
                        _entry_name(entry),
                        _entry_type(entry),
                        str(_entry_value(entry, "_bundle_id", "") or ""),
                    )
                    not in existing
                )
                self._entry_snapshot = (*self._entry_snapshot, *additions)
        self.allowed_bundle_ids = frozenset(
            (*self.allowed_bundle_ids, *self._active_bundle_id_set)
        )

    def pin_bundle_ids(self, bundle_ids: Sequence[str]) -> None:
        self.allowed_bundle_ids = frozenset(
            str(item).strip() for item in bundle_ids if str(item).strip()
        )

    def bundle_generation(self) -> tuple[tuple[str, str], ...]:
        return tuple(sorted(self._bundle_generation.items()))

    @staticmethod
    def _entries_from_bundles(bundles: Sequence[Any]) -> tuple[Any, ...]:
        entries: list[Any] = []
        for bundle in bundles:
            if str(getattr(bundle, "status", "") or "") != "published":
                continue
            for declaration in list(getattr(bundle, "declarations", ()) or ()):
                entries.append(
                    SimpleNamespace(
                        name=str(getattr(declaration, "fq_name", "") or ""),
                        type=str(getattr(declaration, "type_text", "") or ""),
                        kind=str(
                            getattr(declaration, "declaration_kind", "theorem")
                            or "theorem"
                        ),
                        file=str(getattr(bundle, "module_name", "") or ""),
                        docstring=str(getattr(declaration, "docstring", "") or ""),
                        _bundle_id=str(getattr(bundle, "bundle_id", "") or ""),
                        _module_name=str(getattr(bundle, "module_name", "") or ""),
                    )
                )
        return tuple(entries)

    def snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "base": self._base_snapshot_id,
                "active_bundle_ids": sorted(self.active_bundle_ids()),
                "allowed_bundle_ids": (
                    sorted(self.allowed_bundle_ids)
                    if self.allowed_bundle_ids is not None
                    else None
                ),
            }
        )

    def compatibility_snapshot_id(self) -> str:
        payload: list[tuple[str, str, str]] = []
        # Build-mode stores are durable run memory and legitimately grow after
        # a checkpoint identity is pinned.  The Lean environment hash remains
        # the compatibility boundary; read-only corpora additionally bind the
        # exact published bundle generation.
        if str(getattr(self.library, "mode", "") or "") != "build":
            try:
                with self.library_lock:
                    bundles = list(self.library.store.iter_bundles())
                payload = [
                    (
                        str(getattr(bundle, "bundle_id", "") or ""),
                        str(getattr(bundle, "source_hash", "") or ""),
                        str(
                            getattr(bundle, "compiled_artifact_hash", "")
                            or ""
                        ),
                    )
                    for bundle in bundles
                ]
            except Exception:
                payload = []
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "bundles": payload,
                "environment_hash": self.environment_hash,
                "mode": str(getattr(self.library, "mode", "") or ""),
            }
        )

    def iter_entries(self) -> Sequence[Any]:
        return tuple(
            entry
            for entry in self._entry_snapshot
            if self.allowed_bundle_ids is None
            or str(_entry_value(entry, "_bundle_id", "") or "")
            in self.allowed_bundle_ids
        )

    def _origin(self, hit: Any) -> CandidateOrigin:
        bundle_id = str(getattr(hit, "bundle_id", "") or "")
        module_name = str(getattr(hit, "module_name", "") or "")
        active = bundle_id in set(self.active_bundle_ids())
        return CandidateOrigin(
            source_kind=self.source_kind,
            source_id=self.source_id,
            module_name=module_name,
            import_text=f"import {module_name}" if module_name else "",
            source_path=module_name,
            source_hash="",
            environment_hash=self.environment_hash,
            trust_kind="published_kernel_verified",
            availability=(
                "already_imported" if active else "requires_bundle_activation"
            ),
            required_bundle_ids=(bundle_id,) if bundle_id else (),
        )

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult:
        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "timeout",
                    index_snapshot_id=self.snapshot_id(),
                ),
            )
        try:
            with self.library_lock:
                raw_hits = self.library.search(
                    " ".join(
                        item
                        for item in (
                            query.natural_language or query.target_statement,
                            query.route_context,
                        )
                        if item
                    ),
                    goal_state="\n".join(query.ordered_local_context),
                    max_results=max_results,
                    # Cooperative cancel: the theory retriever scores every entry
                    # under this lock, so give it the deadline instead of letting
                    # a timed-out search hold the lock / source slot.
                    deadline_exhausted=deadline_exhausted,
                )
            if self.allowed_bundle_ids is not None:
                raw_hits = [
                    hit
                    for hit in raw_hits
                    if str(getattr(hit, "bundle_id", "") or "")
                    in self.allowed_bundle_ids
                ]
            hits = tuple(
                SourceHit(
                    entry=SimpleNamespace(
                        name=str(getattr(hit, "fq_name", "") or ""),
                        type=str(getattr(hit, "type_text", "") or ""),
                        kind=str(
                            getattr(hit, "declaration_kind", "theorem")
                            or "theorem"
                        ),
                        file=str(getattr(hit, "module_name", "") or ""),
                        docstring="",
                        _bundle_id=str(getattr(hit, "bundle_id", "") or ""),
                    ),
                    score=float(getattr(hit, "score", 0.0) or 0.0),
                    channel="published_theory_lexical",
                    origin=self._origin(hit),
                    reasons=tuple(getattr(hit, "reasons", ()) or ()),
                )
                for hit in list(raw_hits or ())
            )
            source_truncated = _retrieval_elapsed(
                deadline_monotonic,
                deadline_exhausted,
            )
            health = (
                "degraded"
                if hits and source_truncated
                else (
                    "timeout"
                    if source_truncated
                    else ("success_with_hits" if hits else "success_zero_hits")
                )
            )
            return SourceSearchResult(
                hits,
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    health,
                    hit_count=len(hits),
                    elapsed_s=time.monotonic() - started,
                    error=(
                        "source deadline reached; partial hits retained"
                        if hits and source_truncated
                        else ""
                    ),
                    index_snapshot_id=self.snapshot_id(),
                    truncated=source_truncated,
                ),
            )
        except Exception as exc:
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "error",
                    elapsed_s=time.monotonic() - started,
                    error=_safe_error(exc),
                    index_snapshot_id=self.snapshot_id(),
                ),
            )


class VerifiedHelperSource:
    """Semantic discovery over the persistent kernel-checked helper cache.

    A helper proved under another preamble is intentionally returned as
    ``requires_helper_recheck`` until the current session kernel-checks its
    complete source.  This source never upgrades trust merely because a
    statement looks similar.
    """

    source_kind = "verified_helper"

    def __init__(
        self,
        cache: Any,
        *,
        source_id: str = "verified_helper_cache",
        environment_hash: str = "",
        record_generation: Optional[Mapping[str, str]] = None,
    ) -> None:
        self.cache = cache
        self.cache_lock = _backend_operation_lock(cache)
        self.source_id = str(source_id)
        self.environment_hash = str(environment_hash or "")
        self._active_source_hashes: frozenset[str] = frozenset()
        self._active_helper_names_by_source_hash: dict[str, str] = {}
        self._indexed_snapshot = ""
        self._entries: tuple[Any, ...] = ()
        self._inverted: dict[str, set[int]] = {}
        if record_generation is None:
            getter = getattr(self.cache, "retrieval_records", None)
            initial_records = list(getter() or ()) if callable(getter) else []
            self._record_generation = {
                _helper_record_id(record): str(
                    record.get("source_hash") or ""
                ).strip()
                for record in initial_records
                if str(record.get("source_hash") or "").strip()
            }
        else:
            self._record_generation = {
                str(key): str(value)
                for key, value in record_generation.items()
                if str(key)
            }
        self.allowed_source_hashes: frozenset[str] | None = frozenset(
            self._record_generation.values()
        )
        self.allowed_record_ids: frozenset[str] | None = frozenset(
            self._record_generation
        )

    def mark_rechecked(self, source_hash: str, *, helper_name: str = "") -> None:
        clean = str(source_hash or "").strip()
        if clean:
            landed_name = str(helper_name or "").strip()
            if landed_name:
                self._active_helper_names_by_source_hash[clean] = landed_name
            self._active_source_hashes = frozenset(
                (*self._active_source_hashes, clean)
            )
            if self.allowed_source_hashes is not None:
                self.allowed_source_hashes = frozenset(
                    (*self.allowed_source_hashes, clean)
                )
            if self.allowed_record_ids is not None:
                getter = getattr(self.cache, "retrieval_records", None)
                records = list(getter() or ()) if callable(getter) else []
                # Preserve the pin: a recheck of a shared source_hash must only
                # flip availability for records ALREADY in the allowed set, never
                # union in unrelated pinned-out records that happen to share it.
                additions = tuple(
                    _helper_record_id(record)
                    for record in records
                    if str(record.get("source_hash") or "").strip() == clean
                    and _helper_record_id(record) in self.allowed_record_ids
                )
                for record in records:
                    record_id = _helper_record_id(record)
                    if record_id in additions:
                        self._record_generation[record_id] = clean
                self.allowed_record_ids = frozenset((*self.allowed_record_ids, *additions))
            self._indexed_snapshot = ""

    def pin_source_hashes(self, source_hashes: Sequence[str]) -> None:
        clean_hashes = frozenset(
            str(item).strip() for item in source_hashes if str(item).strip()
        )
        self.allowed_source_hashes = clean_hashes
        # _ensure_index only filters on allowed_record_ids, so enforce the hash
        # pin by deriving the matching record ids — otherwise this pin is a no-op
        # and records with other source hashes still get indexed.
        getter = getattr(self.cache, "retrieval_records", None)
        records = list(getter() or ()) if callable(getter) else []
        self.allowed_record_ids = frozenset(
            _helper_record_id(record)
            for record in records
            if str(record.get("source_hash") or "").strip() in clean_hashes
        )
        self._indexed_snapshot = ""

    def pin_record_ids(self, record_ids: Sequence[str]) -> None:
        self.allowed_record_ids = frozenset(
            str(item).strip() for item in record_ids if str(item).strip()
        )
        self._indexed_snapshot = ""

    def record_generation(self) -> tuple[tuple[str, str], ...]:
        return tuple(sorted(self._record_generation.items()))

    def set_rechecked(self, source_hashes: Sequence[str]) -> None:
        self._active_source_hashes = frozenset(
            str(item).strip() for item in source_hashes if str(item).strip()
        )
        self._active_helper_names_by_source_hash = {
            source_hash: helper_name
            for source_hash, helper_name in self._active_helper_names_by_source_hash.items()
            if source_hash in self._active_source_hashes
        }

    def snapshot_id(self) -> str:
        if self.allowed_record_ids is not None:
            return stable_retrieval_hash(
                {
                    "source": self.source_id,
                    "schema": int(getattr(self.cache, "schema_version", 0) or 0),
                    "allowed_record_ids": sorted(self.allowed_record_ids),
                    "environment_hash": self.environment_hash,
                    "rechecked_source_hashes": sorted(self._active_source_hashes),
                    "rechecked_helper_names": sorted(
                        self._active_helper_names_by_source_hash.items()
                    ),
                }
            )
        paths = [Path(getattr(self.cache, "path", ""))]
        paths.extend(Path(item) for item in getattr(self.cache, "_read_paths", ()) or ())
        path_state: list[tuple[str, int, int]] = []
        for path in paths:
            try:
                stat = path.stat()
                path_state.append((str(path.resolve()), int(stat.st_size), int(stat.st_mtime_ns)))
            except OSError:
                path_state.append((str(path), -1, -1))
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "schema": int(getattr(self.cache, "schema_version", 0) or 0),
                "paths": path_state,
                "environment_hash": self.environment_hash,
                "rechecked_source_hashes": sorted(self._active_source_hashes),
                "rechecked_helper_names": sorted(
                    self._active_helper_names_by_source_hash.items()
                ),
            }
        )

    def compatibility_snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "source": self.source_id,
                "schema": int(getattr(self.cache, "schema_version", 0) or 0),
                "environment_hash": self.environment_hash,
            }
        )

    def _ensure_index(self) -> None:
        snapshot = self.snapshot_id()
        if self._indexed_snapshot == snapshot:
            return
        records = getattr(self.cache, "retrieval_records", None)
        raw_records = list(records() or ()) if callable(records) else []
        entries: list[Any] = []
        inverted: dict[str, set[int]] = defaultdict(set)
        for record in raw_records:
            if (
                self.allowed_record_ids is not None
                and _helper_record_id(record) not in self.allowed_record_ids
            ):
                continue
            name = str(record.get("name") or "").strip()
            statement = str(
                record.get("statement_preview") or record.get("statement") or ""
            ).strip()
            source = str(record.get("source") or "").strip()
            source_hash = str(record.get("source_hash") or "").strip()
            name = self._active_helper_names_by_source_hash.get(source_hash, name)
            if not name or not statement or not source or not source_hash:
                continue
            entry = SimpleNamespace(
                name=name,
                type=statement,
                kind="theorem",
                file=str(getattr(self.cache, "path", "") or ""),
                docstring="",
                source="verified_helper",
                _helper_source=source,
                _source_hash=source_hash,
                _owner_theorem=str(record.get("theorem_name") or ""),
            )
            index = len(entries)
            entries.append(entry)
            for token in _normalized_analogy_tokens(
                f"{name} {statement} {entry._owner_theorem}"
            ):
                inverted[token].add(index)
        self._entries = tuple(entries)
        self._inverted = dict(inverted)
        self._indexed_snapshot = snapshot

    def iter_entries(self) -> Sequence[Any]:
        self._ensure_index()
        return self._entries

    def _origin(self, entry: Any) -> CandidateOrigin:
        source_hash = str(_entry_value(entry, "_source_hash", "") or "")
        return CandidateOrigin(
            source_kind=self.source_kind,
            source_id=self.source_id,
            source_path=str(getattr(self.cache, "path", "") or ""),
            source_hash=source_hash,
            environment_hash=self.environment_hash,
            trust_kind="kernel_checked_foreign_environment",
            availability=(
                "already_imported"
                if source_hash in self._active_source_hashes
                else "requires_helper_recheck"
            ),
            helper_source=str(_entry_value(entry, "_helper_source", "") or ""),
        )

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> SourceSearchResult:
        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "timeout",
                    index_snapshot_id=self.snapshot_id(),
                ),
            )
        try:
            self._ensure_index()
            query_text = " ".join(
                item
                for item in (
                    query.target_statement,
                    query.natural_language,
                    query.route_context,
                    *query.ordered_local_context,
                )
                if item
            )
            tokens = _normalized_analogy_tokens(query_text)
            candidate_ids: set[int] = set()
            for token in tokens:
                candidate_ids.update(self._inverted.get(token, ()))
            scored: list[tuple[float, int]] = []
            for index in candidate_ids:
                if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
                    break
                entry = self._entries[index]
                score = _analogy_score(query_text, f"{_entry_name(entry)} {_entry_type(entry)}")
                if query.theorem_name and str(
                    _entry_value(entry, "_owner_theorem", "") or ""
                ) == query.theorem_name:
                    score += 0.05
                if score > 0.0:
                    scored.append((score, index))
            scored.sort(key=lambda item: (-item[0], _entry_name(self._entries[item[1]])))
            hits = tuple(
                SourceHit(
                    entry=self._entries[index],
                    score=score,
                    channel="verified_helper_semantic",
                    origin=self._origin(self._entries[index]),
                    reasons=("semantic_helper_analogy",),
                    details={"semantic_helper_analogy": score},
                )
                for score, index in scored[:max_results]
            )
            source_truncated = _retrieval_elapsed(
                deadline_monotonic,
                deadline_exhausted,
            )
            health = (
                "degraded"
                if hits and source_truncated
                else (
                    "timeout"
                    if source_truncated
                    else ("success_with_hits" if hits else "success_zero_hits")
                )
            )
            return SourceSearchResult(
                hits,
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    health,
                    hit_count=len(hits),
                    elapsed_s=time.monotonic() - started,
                    error=(
                        "source deadline reached; partial hits retained"
                        if hits and source_truncated
                        else ""
                    ),
                    index_snapshot_id=self.snapshot_id(),
                    truncated=source_truncated,
                ),
            )
        except Exception as exc:
            return SourceSearchResult(
                (),
                RetrievalSourceReport(
                    self.source_id,
                    self.source_kind,
                    "error",
                    elapsed_s=time.monotonic() - started,
                    error=_safe_error(exc),
                    index_snapshot_id=self.snapshot_id(),
                ),
            )


@dataclass(frozen=True)
class FederatedSearchHit:
    entry: Any
    score: float
    reasons: tuple[str, ...]
    details: Mapping[str, float]
    candidate: RetrievalCandidate


class _FederatedTypeIndex:
    """Corpus-independent adapter over Mini's declaration-shape machinery."""

    def __init__(
        self,
        entries: Sequence[tuple[Any, CandidateOrigin]],
        *,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> None:
        from ..proof_state_scheduler import _declaration_shape

        accepted_entries: list[tuple[Any, CandidateOrigin]] = []
        shapes: list[Any] = []
        self.complete = True
        for index, item in enumerate(entries):
            if index % 16 == 0 and deadline_exhausted is not None:
                try:
                    if deadline_exhausted():
                        self.complete = False
                        break
                except Exception:
                    self.complete = False
                    break
            accepted_entries.append(item)
            shapes.append(_declaration_shape(item[0]))
        self._entries = tuple(accepted_entries)
        self._shapes = tuple(shapes)
        inverted: dict[str, set[int]] = defaultdict(set)
        for index, shape in enumerate(self._shapes):
            for token in (
                *shape.constants,
                *shape.namespaces,
                *shape.shape_tags,
                *shape.binder_heads,
                shape.result_head,
            ):
                text = str(token or "").strip()
                if text:
                    inverted[text].add(index)
        self._inverted = dict(inverted)

    def search(
        self,
        query: RetrievalQuery,
        *,
        max_results: int,
        channel: str = "type_shape",
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> tuple[SourceHit, ...]:
        from ..proof_state_scheduler import (
            _declaration_shape,
            _declaration_shape_score,
            _normalized_decl_statement_text,
        )

        query_shape = _declaration_shape(
            SimpleNamespace(
                name=query.theorem_name or "retrieval_query",
                kind="theorem",
                type=query.target_statement,
            )
        )
        constants = set(query.constants or query_shape.constants)
        namespaces = set(query.namespaces or query_shape.namespaces)
        tags = set(query.shape_tags or query_shape.shape_tags)
        binders = set(query.binder_heads or query_shape.binder_heads)
        result_head = query.result_head or query_shape.result_head
        candidate_ids: set[int] = set()
        for token in (*constants, *namespaces, *tags, *binders, result_head):
            candidate_ids.update(self._inverted.get(str(token or ""), ()))
        scored: list[tuple[float, int]] = []
        action = " ".join(query.intended_uses)
        for position, index in enumerate(candidate_ids):
            if position % 16 == 0 and deadline_exhausted is not None:
                try:
                    if deadline_exhausted():
                        break
                except Exception:
                    break
            score = _declaration_shape_score(
                self._shapes[index],
                goal_result=result_head,
                goal_constants=constants,
                goal_namespaces=namespaces,
                goal_tags=tags,
                goal_binders=binders,
                action=action,
            )
            if _normalized_decl_statement_text(
                _entry_type(self._entries[index][0])
            ) == _normalized_decl_statement_text(query.target_statement):
                score += 25.0
            if score > 0.0:
                scored.append((float(score), index))
        scored.sort(key=lambda item: (-item[0], _entry_name(self._entries[item[1]][0])))
        return tuple(
            SourceHit(
                entry=self._entries[index][0],
                score=score,
                channel=channel,
                origin=self._entries[index][1],
                reasons=(channel,),
                details={channel: score},
            )
            for score, index in scored[:max_results]
        )


class MathematicalRetrievalService:
    """One evidence-preserving retrieval boundary for all Mini consumers."""

    # ``search_with_scores`` keeps ``goal_state`` as the formal typed target
    # while adapters use ``natural_language`` for lexical retrieval.  Eager
    # callers may therefore pass an uncapped theorem statement without making
    # backends tokenize and score a duplicate full goal.
    preserves_typed_goal_separately = True

    def __init__(
        self,
        sources: Sequence[MathematicalRetrievalSource],
        *,
        static_mathlib_searcher: Any = None,
        rrf_k: float = 60.0,
        channel_weights: Optional[Mapping[str, float]] = None,
        enable_type_index: bool = True,
        operation_timeout_s: float = 30.0,
    ) -> None:
        self.sources = tuple(sources)
        source_ids = [str(getattr(source, "source_id", "") or "").strip() for source in self.sources]
        if any(not source_id for source_id in source_ids):
            raise ValueError("mathematical retrieval sources require nonempty source_id")
        duplicates = sorted(
            source_id
            for source_id in set(source_ids)
            if source_ids.count(source_id) > 1
        )
        if duplicates:
            raise ValueError(
                "mathematical retrieval source_id values must be unique: "
                + ", ".join(duplicates)
            )
        # Validate the abandonment bulkhead contract at composition time,
        # rather than raising from the first live proof query.
        for source in self.sources:
            _source_worker_slot(source)
        self.static_mathlib_searcher = static_mathlib_searcher
        self.rrf_k = max(1.0, float(rrf_k))
        self.channel_weights = {
            "verified_helper_local": 2.0,
            "type_shape": 1.35,
            "verified_helper_semantic": 1.15,
            **dict(channel_weights or {}),
        }
        self.enable_type_index = bool(enable_type_index)
        self.operation_timeout_s = max(0.05, float(operation_timeout_s))
        self._type_index: Optional[_FederatedTypeIndex] = None
        self._type_index_snapshot_id = ""
        self._type_index_cache: dict[str, _FederatedTypeIndex] = {}
        self.last_result: Optional[RetrievalResult] = None
        self._metric_sink: Optional[Callable[[str, int], None]] = None
        self._latency_samples_ms: list[int] = []
        self.excluded_declaration_names: frozenset[str] = frozenset()
        self.excluded_source_paths: frozenset[str] = frozenset()

    def set_excluded_target(
        self,
        *,
        declaration_names: Sequence[str] = (),
        source_paths: Sequence[str | Path] = (),
    ) -> None:
        self.excluded_declaration_names = frozenset(
            str(item or "").strip()
            for item in declaration_names
            if str(item or "").strip()
        )
        normalized_paths: set[str] = set()
        for item in source_paths:
            if not str(item or "").strip():
                continue
            try:
                normalized_paths.add(str(Path(item).resolve()))
            except OSError:
                normalized_paths.add(str(item))
        self.excluded_source_paths = frozenset(normalized_paths)

    def set_metric_sink(
        self,
        sink: Optional[Callable[[str, int], None]],
    ) -> None:
        self._metric_sink = sink

    def publish_result_metrics(
        self,
        result: Optional[RetrievalResult],
        *,
        consumer: str = "direct",
    ) -> None:
        if result is None or self._metric_sink is None:
            return
        latency_ms = max(0, int(round(float(result.elapsed_s or 0.0) * 1000)))
        self._latency_samples_ms.append(latency_ms)
        del self._latency_samples_ms[:-512]
        increments = {
            "mini_mathematical_retrieval_requests_total": 1,
            "mini_mathematical_retrieval_latency_ms_total": latency_ms,
            f"mini_mathematical_retrieval_{consumer}_requests": 1,
        }
        for upper_ms in (10, 50, 100, 500, 1000):
            if latency_ms <= upper_ms:
                increments[
                    f"mini_mathematical_retrieval_latency_le_{upper_ms}ms"
                ] = 1
        if latency_ms > 1000:
            increments["mini_mathematical_retrieval_latency_gt_1000ms"] = 1
        if result.deadline_exhausted:
            increments["mini_mathematical_retrieval_deadline_truncations"] = 1
        if any(report.health == "stale" for report in result.source_reports):
            increments["mini_mathematical_retrieval_stale_results"] = 1
        source_metric = {
            "mathlib": "mathlib",
            "project": "project",
            "published_theory": "theory",
            "verified_helper": "helper",
        }
        for candidate in result.candidates:
            if candidate.availability != "already_imported":
                key = "mini_mathematical_retrieval_all_inactive_hits"
                increments[key] = increments.get(key, 0) + 1
            for source_kind in {
                origin.source_kind for origin in candidate.origins
            }:
                label = source_metric.get(source_kind)
                if label:
                    key = f"mini_mathematical_retrieval_all_{label}_hits"
                    increments[key] = increments.get(key, 0) + 1
            for channel in candidate.channel_ranks:
                clean_channel = re.sub(r"[^a-z0-9]+", "_", channel.lower()).strip("_")
                if clean_channel:
                    key = (
                        "mini_mathematical_retrieval_channel_"
                        f"{clean_channel}_contributions"
                    )
                    increments[key] = increments.get(key, 0) + 1
        degraded = sum(
            report.health
            not in {"success_with_hits", "success_zero_hits"}
            for report in result.source_reports
        )
        if degraded:
            increments["mini_mathematical_retrieval_all_source_failures"] = degraded
        for key, amount in increments.items():
            try:
                self._metric_sink(key, amount)
            except Exception:
                pass

    def telemetry_status(self) -> dict[str, int]:
        samples = sorted(self._latency_samples_ms)

        def percentile(fraction: float) -> int:
            if not samples:
                return 0
            return samples[min(len(samples) - 1, int((len(samples) - 1) * fraction))]

        return {
            "sample_count": len(samples),
            "latency_ms_p50": percentile(0.50),
            "latency_ms_p95": percentile(0.95),
            "latency_ms_p99": percentile(0.99),
            "latency_ms_max": max(samples, default=0),
        }

    def publish_boundary_failure(
        self,
        *,
        consumer: str,
        elapsed_s: float,
        capacity_exhausted: bool = False,
    ) -> None:
        """Record a wrapper-level timeout/capacity failure with no result."""

        result = RetrievalResult(
            request_id="boundary_failure",
            index_snapshot_id="",
            candidates=(),
            source_reports=(
                RetrievalSourceReport(
                    "federated_retrieval",
                    "service",
                    "unavailable" if capacity_exhausted else "timeout",
                ),
            ),
            elapsed_s=max(0.0, float(elapsed_s)),
            truncated=True,
            deadline_exhausted=not capacity_exhausted,
        )
        self.publish_result_metrics(result, consumer=consumer)
        if capacity_exhausted and self._metric_sink is not None:
            try:
                self._metric_sink(
                    "mini_mathematical_retrieval_capacity_exhaustions",
                    1,
                )
            except Exception:
                pass

    @property
    def environment_hash(self) -> str:
        return next(
            (
                str(getattr(source, "environment_hash", "") or "")
                for source in self.sources
                if str(getattr(source, "environment_hash", "") or "")
            ),
            "",
        )

    @property
    def index_snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "semantics": self._semantic_config_record(),
                "sources": {
                    source.source_id: source.snapshot_id()
                    for source in sorted(
                        self.sources,
                        key=lambda item: item.source_id,
                    )
                },
            }
        )

    @property
    def compatibility_snapshot_id(self) -> str:
        return stable_retrieval_hash(
            {
                "semantics": self._semantic_config_record(),
                "sources": {
                    source.source_id: (
                        source.compatibility_snapshot_id()
                        if callable(
                            getattr(source, "compatibility_snapshot_id", None)
                        )
                        else source.snapshot_id()
                    )
                    for source in sorted(
                        self.sources,
                        key=lambda item: item.source_id,
                    )
                },
            }
        )

    def _semantic_config_record(self) -> dict[str, Any]:
        excluded_config_fragments = (
            "path",
            "root",
            "update_on_start",
            "build_on_start",
            "init_timeout",
            "allow_download",
            "local_files",
        )

        def stable_config(cfg: Any) -> dict[str, Any]:
            record: dict[str, Any] = {}
            for key, value in sorted(vars(cfg).items()) if cfg is not None else ():
                if any(fragment in key for fragment in excluded_config_fragments):
                    continue
                if isinstance(value, (str, int, float, bool)) or value is None:
                    record[key] = value
                elif isinstance(value, (list, tuple)) and all(
                    isinstance(item, (str, int, float, bool)) or item is None
                    for item in value
                ):
                    record[key] = list(value)
            return record

        source_semantics: dict[str, Any] = {}
        for source in self.sources:
            if isinstance(source, StaticMathlibSource):
                source_semantics[source.source_id] = {
                    "goal_conditioned": bool(
                        getattr(source.searcher, "_goal_conditioned", True)
                    ),
                    "goal_query_weight": float(
                        getattr(source.searcher, "_goal_query_weight", 1.0)
                        or 0.0
                    ),
                    "include_docstrings": bool(
                        getattr(source.searcher, "_include_docstrings", False)
                    ),
                    "max_prompt_lemmas": int(
                        getattr(source.searcher, "_max_prompt_lemmas", 30) or 0
                    ),
                    "prompt_budget_enabled": bool(
                        getattr(source.searcher, "_prompt_budget_enabled", True)
                    ),
                    "prompt_budget_tokens": int(
                        getattr(source.searcher, "_prompt_budget_tokens", 1200) or 0
                    ),
                    "prompt_budget_hard_cap_tokens": int(
                        getattr(
                            source.searcher,
                            "_prompt_budget_hard_cap_tokens",
                            20000,
                        )
                        or 0
                    ),
                    "prompt_budget_dedup_jaccard": float(
                        getattr(
                            source.searcher,
                            "_prompt_budget_dedup_jaccard",
                            0.92,
                        )
                        or 0.0
                    ),
                    "tokenizer_model": str(
                        getattr(source.searcher, "_tokenizer_model", "") or ""
                    ),
                }
            elif isinstance(source, ProjectSupportSource):
                cfg = getattr(source.retriever, "cfg", None)
                stable_module_roots: list[str] = []
                for root_index, module_root in enumerate(source.module_roots):
                    try:
                        stable_module_roots.append(
                            str(
                                module_root.resolve().relative_to(
                                    source.project_root.resolve()
                                )
                            )
                            or "."
                        )
                    except ValueError:
                        stable_module_roots.append(f"external:{root_index}")
                source_semantics[source.source_id] = {
                    "module_roots": stable_module_roots,
                    "config": stable_config(cfg),
                    "dense_artifact_hash": source._dense_artifact_hash,
                    "dense_meta_hash": source._dense_meta_hash,
                }
        excluded_sources: list[dict[str, str]] = []
        for raw_path in sorted(self.excluded_source_paths):
            path = Path(raw_path)
            excluded_sources.append(
                {
                    "name": path.name,
                    "content_hash": _content_hash(path),
                }
            )
        return {
            "retrieval_semantics_version": 2,
            "rrf_k": self.rrf_k,
            "channel_weights": dict(sorted(self.channel_weights.items())),
            "enable_type_index": self.enable_type_index,
            "excluded_declaration_names": sorted(
                self.excluded_declaration_names
            ),
            "excluded_sources": excluded_sources,
            "sources": source_semantics,
        }

    def compatibility_status(self) -> dict[str, Any]:
        return {
            "channel": "mathematical_retrieval_service",
            "compatibility_snapshot_id": self.compatibility_snapshot_id,
            "sources": [
                {
                    "source_id": source.source_id,
                    "source_kind": source.source_kind,
                    "compatibility_snapshot_id": (
                        source.compatibility_snapshot_id()
                        if callable(
                            getattr(source, "compatibility_snapshot_id", None)
                        )
                        else source.snapshot_id()
                    ),
                }
                for source in self.sources
            ],
        }

    def status(self) -> dict[str, Any]:
        source_records: list[dict[str, Any]] = []
        for source in self.sources:
            try:
                entry_count = len(source.iter_entries())
                entry_error = ""
            except Exception as exc:
                entry_count = 0
                entry_error = _safe_error(exc)
            source_record = {
                    "source_id": source.source_id,
                    "source_kind": source.source_kind,
                    "snapshot_id": source.snapshot_id(),
                    "entry_count": entry_count,
                    "entry_error": entry_error,
                    "index_state": (
                        "error"
                        if entry_error
                        else (
                            "ready"
                            if entry_count > 0
                            else (
                                "configured_empty"
                                if isinstance(source, ProjectSupportSource)
                                else (
                                    "current_policy_empty"
                                    if isinstance(source, PublishedTheorySource)
                                    else "empty"
                                )
                            )
                        )
                    ),
                    **(
                        {
                            "semantic_requested": bool(
                                getattr(
                                    source.retriever,
                                    "_mini_semantic_requested",
                                    False,
                                )
                            ),
                            "semantic_available": bool(
                                getattr(
                                    source.retriever,
                                    "_mini_semantic_available",
                                    False,
                                )
                            ),
                            "semantic_init_error": str(
                                getattr(
                                    source.retriever,
                                    "_mini_semantic_init_error",
                                    getattr(
                                        source.retriever,
                                        "_embedder_init_error",
                                        "",
                                    ),
                                )
                                or ""
                            )[:500],
                            "dense_requested": bool(
                                getattr(
                                    source.retriever,
                                    "_mini_dense_requested",
                                    False,
                                )
                            ),
                            "dense_available": bool(
                                getattr(source.retriever, "_dense_ready", False)
                            ),
                        }
                        if isinstance(source, ProjectSupportSource)
                        else {}
                    ),
                }
            if isinstance(source, PublishedTheorySource):
                source_record.update(
                    {
                        "policy_version": int(
                            getattr(source.library, "policy_version", 0) or 0
                        ),
                        "schema_version": int(
                            getattr(source.library, "schema_version", 0) or 0
                        ),
                        "environment_key": str(
                            getattr(source.library, "environment_key", "") or ""
                        ),
                    }
                )
            source_records.append(source_record)
        return {
            "channel": "mathematical_retrieval_service",
            "index_snapshot_id": self.index_snapshot_id,
            "sources": source_records,
            "telemetry": self.telemetry_status(),
        }

    def runtime_corpus_snapshot(self) -> dict[str, Any]:
        """Return the complete session-local retrieval context.

        Corpus generations and visibility are one durability boundary.  A
        rollback that restores only the former can leave a source claiming a
        declaration is imported or rechecked after the Lean/session state that
        justified that claim was rolled back.  Keep this record self-contained
        so root, nested, and in-process restore paths do not need to reconstruct
        searcher state from parallel session fields.
        """

        records: dict[str, Any] = {}
        for source in self.sources:
            if source.source_id in records:
                raise ValueError(
                    f"duplicate mutable retrieval source id: {source.source_id}"
                )
            if isinstance(source, StaticMathlibSource):
                records[source.source_id] = {
                    "kind": source.source_kind,
                    "active_imports": sorted(source.active_imports),
                }
            elif isinstance(source, ProjectSupportSource):
                records[source.source_id] = {
                    "kind": source.source_kind,
                    "active_imports": sorted(source.active_imports),
                    "active_declarations": [
                        list(item) for item in sorted(source.active_declarations)
                    ],
                }
            if isinstance(source, VerifiedHelperSource):
                allowed_record_ids = (
                    set(source.allowed_record_ids)
                    if source.allowed_record_ids is not None
                    else {record_id for record_id, _ in source.record_generation()}
                )
                visible_records = [
                    (record_id, source_hash)
                    for record_id, source_hash in source.record_generation()
                    if record_id in allowed_record_ids
                ]
                visible_record_hashes = {
                    source_hash for _record_id, source_hash in visible_records
                }
                # A helper can be kernel-checked into the dossier before its
                # advisory cache publication runs.  The dossier is the durable
                # authority for that proof; the retrieval snapshot must remain
                # self-contained and may preserve visibility only for an exact
                # checkpoint-pinned cache record.  An unbacked active hash is
                # inert today, but serializing it would make restore depend on
                # cache state the checkpoint does not own.
                rechecked_source_hashes = frozenset(
                    set(source._active_source_hashes) & visible_record_hashes
                )
                checkpoint_allowed_source_hashes = frozenset(
                    (
                        set(source.allowed_source_hashes)
                        if source.allowed_source_hashes is not None
                        else visible_record_hashes
                    )
                    & visible_record_hashes
                ) | rechecked_source_hashes
                records[source.source_id] = {
                    "kind": source.source_kind,
                    "records": [
                        [record_id, source_hash]
                        for record_id, source_hash in visible_records
                    ],
                    "allowed_source_hashes": sorted(
                        checkpoint_allowed_source_hashes
                    ),
                    "rechecked_source_hashes": sorted(
                        rechecked_source_hashes
                    ),
                    "rechecked_helper_names": {
                        source_hash: helper_name
                        for source_hash, helper_name in (
                            source._active_helper_names_by_source_hash.items()
                        )
                        if source_hash in rechecked_source_hashes
                    },
                }
            elif isinstance(source, PublishedTheorySource):
                allowed_bundle_ids = (
                    set(source.allowed_bundle_ids)
                    if source.allowed_bundle_ids is not None
                    else {bundle_id for bundle_id, _ in source.bundle_generation()}
                )
                records[source.source_id] = {
                    "kind": source.source_kind,
                    "bundles": [
                        item
                        for item in source.bundle_generation()
                        if item[0] in allowed_bundle_ids
                    ],
                    "active_bundle_ids": sorted(source.active_bundle_ids()),
                }
        return {
            "schema_version": _RUNTIME_CONTEXT_SCHEMA_VERSION,
            "sources": records,
            "excluded_declaration_names": sorted(
                self.excluded_declaration_names
            ),
            "excluded_source_paths": sorted(self.excluded_source_paths),
        }

    def restore_runtime_corpus_snapshot(self, record: Mapping[str, Any]) -> None:
        """Atomically validate and restore a saved retrieval context."""

        if not isinstance(record, Mapping):
            raise ValueError("retrieval runtime snapshot must be a mapping")
        schema_version = int(record.get("schema_version", 0) or 0)
        if schema_version not in {
            _LEGACY_RUNTIME_CORPUS_SCHEMA_VERSION,
            _LEGACY_RUNTIME_CONTEXT_SCHEMA_VERSION,
            _RUNTIME_CONTEXT_SCHEMA_VERSION,
        }:
            raise ValueError("unsupported retrieval runtime snapshot schema")
        raw_saved_sources = record.get("sources")
        if not isinstance(raw_saved_sources, Mapping):
            raise ValueError("retrieval runtime snapshot sources must be a mapping")
        saved_sources = dict(raw_saved_sources)
        if any(not isinstance(source_id, str) for source_id in saved_sources):
            raise ValueError("retrieval runtime source ids must be strings")

        mutable_sources: dict[str, Any] = {}
        for source in self.sources:
            if not isinstance(
                source,
                (
                    StaticMathlibSource,
                    ProjectSupportSource,
                    VerifiedHelperSource,
                    PublishedTheorySource,
                ),
            ):
                continue
            if source.source_id in mutable_sources:
                raise ValueError(
                    f"duplicate mutable retrieval source id: {source.source_id}"
                )
            mutable_sources[source.source_id] = source

        expected_source_ids = (
            set(mutable_sources)
            if schema_version
            in {
                _LEGACY_RUNTIME_CONTEXT_SCHEMA_VERSION,
                _RUNTIME_CONTEXT_SCHEMA_VERSION,
            }
            else {
                source_id
                for source_id, source in mutable_sources.items()
                if isinstance(source, (VerifiedHelperSource, PublishedTheorySource))
            }
        )
        if set(saved_sources) != expected_source_ids:
            missing = sorted(expected_source_ids - set(saved_sources))
            unexpected = sorted(set(saved_sources) - expected_source_ids)
            details = []
            if missing:
                details.append("missing=" + ",".join(missing))
            if unexpected:
                details.append("unexpected=" + ",".join(unexpected))
            raise ValueError(
                "retrieval runtime snapshot source registry differs"
                + (": " + " ".join(details) if details else "")
            )

        if schema_version == _RUNTIME_CONTEXT_SCHEMA_VERSION:
            excluded_declaration_names = frozenset(
                str(item or "").strip()
                for item in record.get("excluded_declaration_names", ()) or ()
                if str(item or "").strip()
            )
            excluded_source_paths = frozenset(
                str(item or "").strip()
                for item in record.get("excluded_source_paths", ()) or ()
                if str(item or "").strip()
            )
        else:
            excluded_declaration_names = self.excluded_declaration_names
            excluded_source_paths = self.excluded_source_paths

        # Build a complete immutable plan before changing any source.  Restore
        # failures must leave the pre-call searcher context byte-for-byte live.
        plan: list[tuple[Any, dict[str, Any]]] = []
        for source_id, saved in saved_sources.items():
            if not isinstance(saved, Mapping):
                raise ValueError(
                    f"checkpoint retrieval source is not a mapping: {source_id}"
                )
            source = mutable_sources[source_id]
            saved_record = dict(saved)
            kind = str(saved_record.get("kind") or "")
            if str(source.source_kind) != kind:
                raise ValueError(
                    f"missing checkpoint retrieval source: {source_id}"
                )

            if isinstance(source, StaticMathlibSource):
                imports = frozenset(
                    str(item or "").strip()
                    for item in saved_record.get("active_imports", ()) or ()
                    if str(item or "").strip()
                )
                if not source.base_imports.issubset(imports):
                    raise ValueError(
                        f"checkpoint mathlib imports omit base imports: {source_id}"
                    )
                plan.append((source, {"active_imports": imports}))
                continue

            if isinstance(source, ProjectSupportSource):
                imports = frozenset(
                    str(item or "").strip()
                    for item in saved_record.get("active_imports", ()) or ()
                    if str(item or "").strip()
                )
                if not source.base_imports.issubset(imports):
                    raise ValueError(
                        f"checkpoint project imports omit base imports: {source_id}"
                    )
                declarations: set[tuple[str, str, str]] = set()
                for raw_declaration in (
                    saved_record.get("active_declarations", ()) or ()
                ):
                    if (
                        not isinstance(raw_declaration, (list, tuple))
                        or len(raw_declaration) != 3
                    ):
                        raise ValueError(
                            "malformed checkpoint project declaration: "
                            f"{source_id}"
                        )
                    declaration = tuple(
                        str(item or "").strip() for item in raw_declaration
                    )
                    if not all(declaration):
                        raise ValueError(
                            "empty checkpoint project declaration: "
                            f"{source_id}"
                        )
                    declarations.add(declaration)
                plan.append(
                    (
                        source,
                        {
                            "active_imports": imports,
                            "active_declarations": frozenset(declarations),
                        },
                    )
                )
                continue

            if isinstance(source, VerifiedHelperSource):
                cache_records = getattr(source.cache, "retrieval_records", None)
                available_generation = dict(source.record_generation())
                available_generation.update({
                    _helper_record_id(item): str(item.get("source_hash") or "").strip()
                    for item in (
                        list(cache_records() or ())
                        if callable(cache_records)
                        else ()
                    )
                    if str(item.get("source_hash") or "").strip()
                })
                if schema_version == _LEGACY_RUNTIME_CORPUS_SCHEMA_VERSION:
                    saved_ids = frozenset(
                        str(item or "").strip()
                        for item in saved_record.get("record_ids", ()) or ()
                        if str(item or "").strip()
                    )
                    if not saved_ids.issubset(available_generation):
                        raise ValueError(
                            f"missing checkpoint helper corpus entries: {source_id}"
                        )
                    saved_records = {
                        record_id: available_generation[record_id]
                        for record_id in saved_ids
                    }
                    allowed_source_hashes = frozenset(saved_records.values())
                else:
                    saved_records: dict[str, str] = {}
                    for raw_pair in saved_record.get("records", ()) or ():
                        if not isinstance(raw_pair, (list, tuple)) or len(raw_pair) != 2:
                            raise ValueError(
                                f"malformed checkpoint helper generation: {source_id}"
                            )
                        record_id = str(raw_pair[0] or "").strip()
                        source_hash = str(raw_pair[1] or "").strip()
                        if not record_id or not source_hash or record_id in saved_records:
                            raise ValueError(
                                f"malformed checkpoint helper generation: {source_id}"
                            )
                        saved_records[record_id] = source_hash
                    if any(
                        available_generation.get(record_id) != source_hash
                        for record_id, source_hash in saved_records.items()
                    ):
                        raise ValueError(
                            f"missing checkpoint helper corpus entries: {source_id}"
                        )
                    allowed_source_hashes = frozenset(
                        str(item or "").strip()
                        for item in (
                            saved_record.get("allowed_source_hashes", ()) or ()
                        )
                        if str(item or "").strip()
                    )
                    if not allowed_source_hashes.issubset(
                        set(available_generation.values())
                    ):
                        raise ValueError(
                            f"missing checkpoint helper source hashes: {source_id}"
                        )
                rechecked = frozenset(
                    str(item or "").strip()
                    for item in (
                        saved_record.get("rechecked_source_hashes", ()) or ()
                    )
                    if str(item or "").strip()
                )
                if schema_version == _LEGACY_RUNTIME_CORPUS_SCHEMA_VERSION:
                    if not rechecked.issubset(set(available_generation.values())):
                        raise ValueError(
                            f"missing checkpoint helper source hashes: {source_id}"
                        )
                    allowed_source_hashes = frozenset(
                        (*allowed_source_hashes, *rechecked)
                    )
                aliases_raw = saved_record.get("rechecked_helper_names") or {}
                if not isinstance(aliases_raw, Mapping):
                    raise ValueError(
                        f"checkpoint helper aliases are not a mapping: {source_id}"
                    )
                aliases = {
                    str(source_hash or "").strip(): str(helper_name or "").strip()
                    for source_hash, helper_name in aliases_raw.items()
                    if str(source_hash or "").strip()
                    and str(helper_name or "").strip()
                }
                if not rechecked.issubset(allowed_source_hashes) or not set(
                    aliases
                ).issubset(rechecked):
                    raise ValueError(
                        f"checkpoint helper visibility is inconsistent: {source_id}"
                    )
                plan.append(
                    (
                        source,
                        {
                            "records": saved_records,
                            "allowed_record_ids": frozenset(saved_records),
                            "allowed_source_hashes": allowed_source_hashes,
                            "rechecked": rechecked,
                            "aliases": aliases,
                        },
                    )
                )
                continue

            if isinstance(source, PublishedTheorySource):
                saved_bundles: dict[str, str] = {}
                for raw_pair in saved_record.get("bundles", ()) or ():
                    if not isinstance(raw_pair, (list, tuple)) or len(raw_pair) != 2:
                        raise ValueError(
                            f"malformed checkpoint theory generation: {source_id}"
                        )
                    bundle_id = str(raw_pair[0] or "").strip()
                    manifest_hash = str(raw_pair[1] or "").strip()
                    if not bundle_id or not manifest_hash or bundle_id in saved_bundles:
                        raise ValueError(
                            f"malformed checkpoint theory generation: {source_id}"
                        )
                    saved_bundles[bundle_id] = manifest_hash
                live_bundles = dict(source.bundle_generation())
                if any(
                    live_bundles.get(bundle_id) != manifest_hash
                    for bundle_id, manifest_hash in saved_bundles.items()
                ):
                    raise ValueError(
                        f"missing checkpoint theory corpus entries: {source_id}"
                    )
                active_bundle_ids = (
                    frozenset()
                    if schema_version == _LEGACY_RUNTIME_CORPUS_SCHEMA_VERSION
                    else frozenset(
                        str(item or "").strip()
                        for item in (
                            saved_record.get("active_bundle_ids", ()) or ()
                        )
                        if str(item or "").strip()
                    )
                )
                if not active_bundle_ids.issubset(saved_bundles):
                    raise ValueError(
                        f"checkpoint active theory bundles are unavailable: {source_id}"
                    )
                if (
                    schema_version
                    in {
                        _LEGACY_RUNTIME_CONTEXT_SCHEMA_VERSION,
                        _RUNTIME_CONTEXT_SCHEMA_VERSION,
                    }
                    and source._active_bundle_ids_provider is not None
                    and frozenset(source.active_bundle_ids()) != active_bundle_ids
                ):
                    raise ValueError(
                        f"checkpoint theory visibility provider differs: {source_id}"
                    )
                plan.append(
                    (
                        source,
                        {
                            "allowed_bundle_ids": frozenset(saved_bundles),
                            "active_bundle_ids": active_bundle_ids,
                            "restore_active": (
                                schema_version
                                in {
                                    _LEGACY_RUNTIME_CONTEXT_SCHEMA_VERSION,
                                    _RUNTIME_CONTEXT_SCHEMA_VERSION,
                                }
                            ),
                        },
                    )
                )

        for source, state in plan:
            if isinstance(source, StaticMathlibSource):
                source.active_imports = state["active_imports"]
            elif isinstance(source, ProjectSupportSource):
                source.active_imports = state["active_imports"]
                source.active_declarations = state["active_declarations"]
            elif isinstance(source, VerifiedHelperSource):
                source._record_generation.update(state["records"])
                source.allowed_record_ids = state["allowed_record_ids"]
                source.allowed_source_hashes = state["allowed_source_hashes"]
                source._active_source_hashes = state["rechecked"]
                source._active_helper_names_by_source_hash = dict(state["aliases"])
                source._indexed_snapshot = ""
            elif isinstance(source, PublishedTheorySource):
                source.allowed_bundle_ids = state["allowed_bundle_ids"]
                if state["restore_active"]:
                    source._active_bundle_id_set = state["active_bundle_ids"]
        self.excluded_declaration_names = excluded_declaration_names
        self.excluded_source_paths = excluded_source_paths

    def set_active_bundle_ids(self, bundle_ids: Sequence[str]) -> None:
        """Update session-visible theory availability without changing trust."""

        for source in self.sources:
            if isinstance(source, PublishedTheorySource):
                source.set_active_bundle_ids(bundle_ids)

    def theory_operation_lock(self, library: Any) -> threading.RLock | None:
        """Return the shared lock protecting a configured theory library."""

        from ensemble_prover.mini_session.session import (
            _dispatch_capability_identity,
        )

        library_identity = _dispatch_capability_identity(library)

        for source in self.sources:
            if (
                isinstance(source, PublishedTheorySource)
                and _dispatch_capability_identity(source.library)
                == library_identity
            ):
                return source.library_lock
        return None

    def fork_session_context(self) -> "MathematicalRetrievalService":
        """Return an isolated availability/result view over shared read indexes."""

        forked_sources: list[MathematicalRetrievalSource] = []
        for source in self.sources:
            if isinstance(source, AnswerSafePreambleSource):
                # Immutable declaration snapshot already scoped to this target.
                forked_sources.append(source)
            elif isinstance(source, StaticMathlibSource):
                forked = StaticMathlibSource(
                    source.searcher,
                    source_id=source.source_id,
                    environment_hash=source.environment_hash,
                    active_imports=tuple(source.base_imports),
                    searcher_lock=source.searcher_lock,
                    compatibility_corpus_hash=(
                        source._compatibility_corpus_hash
                    ),
                )
                forked.active_imports = source.active_imports
                forked_sources.append(forked)
            elif isinstance(source, PublishedTheorySource):
                forked = PublishedTheorySource(
                    source.library,
                    source_id=source.source_id,
                    environment_hash=source.environment_hash,
                    active_bundle_ids=source._active_bundle_ids_provider,
                    library_lock=source.library_lock,
                    bundle_generation=dict(source.bundle_generation()),
                    entry_snapshot=source._entry_snapshot,
                )
                forked.set_active_bundle_ids(source.active_bundle_ids())
                forked.allowed_bundle_ids = source.allowed_bundle_ids
                forked_sources.append(forked)
            elif isinstance(source, ProjectSupportSource):
                forked = ProjectSupportSource(
                    source.retriever,
                    project_root=source.project_root,
                    source_id=source.source_id,
                    environment_hash=source.environment_hash,
                    active_imports=tuple(source.base_imports),
                    retriever_lock=source.retriever_lock,
                    compatibility_corpus_hash=(
                        source._compatibility_corpus_hash
                    ),
                    active_declarations=tuple(source.active_declarations),
                    module_roots=source.module_roots,
                    source_manifest_hash=source._source_manifest_hash,
                    dense_artifact_hash=source._dense_artifact_hash,
                    dense_meta_hash=source._dense_meta_hash,
                )
                forked.active_imports = source.active_imports
                forked_sources.append(forked)
            elif isinstance(source, VerifiedHelperSource):
                forked = VerifiedHelperSource(
                    source.cache,
                    source_id=source.source_id,
                    environment_hash=source.environment_hash,
                    record_generation=dict(source.record_generation()),
                )
                forked._active_source_hashes = source._active_source_hashes
                forked._active_helper_names_by_source_hash = dict(
                    source._active_helper_names_by_source_hash
                )
                forked.allowed_source_hashes = source.allowed_source_hashes
                forked.allowed_record_ids = source.allowed_record_ids
                forked_sources.append(forked)
            else:
                forked_sources.append(source)
        forked_service = MathematicalRetrievalService(
            forked_sources,
            static_mathlib_searcher=self.static_mathlib_searcher,
            rrf_k=self.rrf_k,
            channel_weights=self.channel_weights,
            enable_type_index=self.enable_type_index,
            operation_timeout_s=self.operation_timeout_s,
        )
        forked_service.set_excluded_target(
            declaration_names=tuple(self.excluded_declaration_names),
            source_paths=tuple(self.excluded_source_paths),
        )
        forked_service._metric_sink = self._metric_sink
        return forked_service

    def with_answer_safe_preamble(
        self,
        preamble: str,
        *,
        lean_preamble: Optional[str] = None,
        theorem_name: str = "",
        source_path: str = "",
        environment_hash: str = "",
    ) -> "MathematicalRetrievalService":
        """Bind pre-target local declarations to an isolated session view."""

        retained = tuple(
            source
            for source in self.sources
            if not isinstance(source, AnswerSafePreambleSource)
        )
        local = AnswerSafePreambleSource(
            preamble,
            lean_preamble=lean_preamble,
            theorem_name=theorem_name,
            source_path=source_path,
            environment_hash=environment_hash,
        )
        sources: tuple[MathematicalRetrievalSource, ...] = retained
        if local.iter_entries():
            sources = (*retained, local)
        bound = MathematicalRetrievalService(
            sources,
            static_mathlib_searcher=self.static_mathlib_searcher,
            rrf_k=self.rrf_k,
            channel_weights=self.channel_weights,
            enable_type_index=self.enable_type_index,
            operation_timeout_s=self.operation_timeout_s,
        )
        bound.set_excluded_target(
            declaration_names=tuple(self.excluded_declaration_names),
            source_paths=tuple(self.excluded_source_paths),
        )
        bound._metric_sink = self._metric_sink
        return bound

    def set_verified_helper_cache(
        self,
        cache: Any,
        *,
        environment_hash: str = "",
    ) -> None:
        """Attach the run's durable helper cache as a discovery source.

        ``environment_hash`` must be the current checker/dossier preamble
        hash. Mathlib and project sources keep their Lake fingerprints;
        inheriting those here would alias helper receipts against a shared
        library identity instead of the run's Lean environment.
        """

        retained = tuple(
            source for source in self.sources if not isinstance(source, VerifiedHelperSource)
        )
        if cache is not None:
            # Helper identity follows the current checker/dossier preamble.
            # Do not inherit a Mathlib/project Lake fingerprint: those sources
            # describe the shared library, not the run's Lean environment.
            retained = (
                *retained,
                VerifiedHelperSource(
                    cache,
                    environment_hash=str(environment_hash or ""),
                ),
            )
        self.sources = retained
        self._type_index = None
        self._type_index_snapshot_id = ""

    def mark_verified_helper_rechecked(
        self,
        source_hash: str,
        *,
        helper_name: str = "",
    ) -> None:
        for source in self.sources:
            if isinstance(source, VerifiedHelperSource):
                source.mark_rechecked(source_hash, helper_name=helper_name)

    def set_verified_helpers_rechecked(self, source_hashes: Sequence[str]) -> None:
        for source in self.sources:
            if isinstance(source, VerifiedHelperSource):
                source.set_rechecked(source_hashes)

    def mark_project_module_imported(self, module_name: str) -> None:
        del module_name

    def mark_module_imported(self, module_name: str) -> None:
        for source in self.sources:
            if isinstance(source, StaticMathlibSource):
                source.mark_imported(module_name)

    def mark_source_module_imported(
        self,
        source_id: str,
        module_name: str,
    ) -> None:
        clean_source_id = str(source_id or "").strip()
        for source in self.sources:
            if (
                source.source_id == clean_source_id
                and isinstance(source, StaticMathlibSource)
            ):
                source.mark_imported(module_name)

    def mark_source_declaration_imported(
        self,
        source_id: str,
        module_name: str,
        declaration_name: str,
        declaration_type: str,
    ) -> None:
        clean_source_id = str(source_id or "").strip()
        for source in self.sources:
            if source.source_id == clean_source_id and isinstance(
                source,
                ProjectSupportSource,
            ):
                source.mark_declaration_imported(
                    module_name,
                    declaration_name,
                    declaration_type,
                )

    def set_source_declarations_imported(
        self,
        records: Sequence[Mapping[str, str]],
    ) -> None:
        for source in self.sources:
            if isinstance(source, ProjectSupportSource):
                source.active_declarations = frozenset()
        for record in records:
            self.mark_source_declaration_imported(
                str(record.get("source_id") or ""),
                str(record.get("module_name") or ""),
                str(record.get("declaration_name") or ""),
                str(record.get("declaration_type") or ""),
            )

    def set_project_modules_imported(self, module_names: Sequence[str]) -> None:
        for source in self.sources:
            if isinstance(source, (StaticMathlibSource, ProjectSupportSource)):
                source.reset_imports()
        for module_name in module_names:
            self.mark_module_imported(module_name)

    def set_source_modules_imported(
        self,
        source_modules: Mapping[str, str | Sequence[str]],
    ) -> None:
        for source in self.sources:
            if isinstance(source, (StaticMathlibSource, ProjectSupportSource)):
                source.reset_imports()
        for source_id, module_names in dict(source_modules or {}).items():
            values = (module_names,) if isinstance(module_names, str) else module_names
            for module_name in values:
                self.mark_source_module_imported(source_id, module_name)

    def _source_enabled(
        self, source: MathematicalRetrievalSource, policy: RetrievalSourcePolicy
    ) -> bool:
        if policy.allowed_source_ids and source.source_id not in policy.allowed_source_ids:
            return False
        return {
            "mathlib": policy.include_mathlib,
            "project": policy.include_project,
            "published_theory": policy.include_published_theory,
            "verified_helper": policy.include_verified_helpers,
        }.get(source.source_kind, True)

    def _search_sources_parallel(
        self,
        query: RetrievalQuery,
        *,
        pool_size: int,
        deadline_monotonic: Optional[float],
        deadline_exhausted: Optional[Callable[[], bool]],
    ) -> list[SourceSearchResult]:
        """Search independent adapters concurrently under one hard boundary."""

        enabled = [
            source
            for source in self.sources
            if self._source_enabled(source, query.source_policy)
        ]
        if not enabled:
            return []
        operation_deadline = time.monotonic() + self.operation_timeout_s
        if deadline_monotonic is not None:
            operation_deadline = min(
                operation_deadline,
                float(deadline_monotonic),
            )
        initial_budget = max(0.0, operation_deadline - time.monotonic())
        # Reserve a small deterministic tail for fusion and immutable result
        # construction.  Otherwise a slow adapter can consume the caller's
        # entire deadline and cause already-completed fast results to be
        # discarded at the final acceptance gate.
        fusion_margin = min(0.05, initial_budget * 0.10)
        source_deadline = max(time.monotonic(), operation_deadline - fusion_margin)
        results: queue.Queue[tuple[str, SourceSearchResult]] = queue.Queue()
        pending: set[str] = set()
        unavailable: set[str] = set()

        def launch(source: MathematicalRetrievalSource) -> bool:
            if _retrieval_elapsed(source_deadline, deadline_exhausted):
                return False
            worker_slot = _source_worker_slot(source)
            if not worker_slot.acquire(blocking=False):
                return False
            pending.add(source.source_id)

            def worker() -> None:
                try:
                    if _retrieval_elapsed(source_deadline, deadline_exhausted):
                        result = SourceSearchResult(
                            (),
                            RetrievalSourceReport(
                                source.source_id,
                                source.source_kind,
                                "timeout",
                            ),
                        )
                    else:
                        search_kwargs: dict[str, Any] = {
                            "max_results": pool_size,
                            "deadline_monotonic": source_deadline,
                        }
                        # Built-in adapters accept the caller cancellation
                        # signal so their cooperative backends release locks
                        # immediately.  Preserve source compatibility for
                        # external/legacy adapters that implement the older
                        # fixed-deadline protocol.
                        try:
                            parameters = inspect.signature(source.search).parameters
                            accepts_callback = (
                                "deadline_exhausted" in parameters
                                or any(
                                    parameter.kind
                                    == inspect.Parameter.VAR_KEYWORD
                                    for parameter in parameters.values()
                                )
                            )
                        except (TypeError, ValueError):
                            accepts_callback = False
                        if accepts_callback:
                            search_kwargs["deadline_exhausted"] = deadline_exhausted
                        result = source.search(query, **search_kwargs)
                except BaseException as exc:
                    result = SourceSearchResult(
                        (),
                        RetrievalSourceReport(
                            source.source_id,
                            source.source_kind,
                            "error",
                            error=_safe_error(exc),
                        ),
                    )
                finally:
                    worker_slot.release()
                results.put((source.source_id, result))

            try:
                thread = threading.Thread(
                    target=worker,
                    name=f"mini-retrieval-source-{source.source_id}",
                    daemon=True,
                )
                thread.start()
            except BaseException as exc:
                pending.discard(source.source_id)
                worker_slot.release()
                completed[source.source_id] = SourceSearchResult(
                    (),
                    RetrievalSourceReport(
                        source.source_id,
                        source.source_kind,
                        "error",
                        error=_safe_error(exc),
                    ),
                )
            return True

        completed: dict[str, SourceSearchResult] = {}
        for source in enabled:
            if _retrieval_elapsed(source_deadline, deadline_exhausted):
                break
            if not launch(source):
                # A prior cancellation-resistant call still owns this
                # backend's sole bulkhead. Do not occupy an outer retrieval
                # worker waiting for it: that would let retries against one
                # bad provider exhaust capacity for every unrelated source.
                unavailable.add(source.source_id)
        while pending:
            if _retrieval_elapsed(source_deadline, deadline_exhausted):
                break
            remaining = source_deadline - time.monotonic()
            if remaining <= 0.0:
                break
            try:
                source_id, result = results.get(timeout=min(0.02, remaining))
            except queue.Empty:
                continue
            if source_id not in pending:
                continue
            pending.remove(source_id)
            completed[source_id] = result

        # Cooperative sources commonly observe ``source_deadline`` inside a
        # scoring loop, return the hits completed so far, and enqueue them a
        # scheduling instant after the coordinator's own deadline check.  Give
        # those already-running workers a bounded settlement window inside the
        # reserved fusion tail; otherwise useful partial results are
        # deterministically relabelled as timeouts.  An external cancellation
        # callback remains a hard boundary.
        settlement_deadline = min(
            operation_deadline,
            source_deadline + min(0.01, fusion_margin * 0.5),
        )
        externally_cancelled = False
        while pending and time.monotonic() < settlement_deadline:
            if deadline_exhausted is not None:
                try:
                    if deadline_exhausted():
                        externally_cancelled = True
                        break
                except Exception:
                    externally_cancelled = True
                    break
            remaining = settlement_deadline - time.monotonic()
            if remaining <= 0.0:
                break
            try:
                source_id, result = results.get(timeout=remaining)
            except queue.Empty:
                break
            if source_id not in pending:
                continue
            pending.remove(source_id)
            completed[source_id] = result

        # Include results that were enqueued between the final timed wait and
        # its timeout without spending any more of the fusion budget.
        if not externally_cancelled and deadline_exhausted is not None:
            try:
                externally_cancelled = bool(deadline_exhausted())
            except Exception:
                externally_cancelled = True
        while pending and not externally_cancelled:
            try:
                source_id, result = results.get_nowait()
            except queue.Empty:
                break
            if source_id not in pending:
                continue
            pending.remove(source_id)
            completed[source_id] = result

        ordered: list[SourceSearchResult] = []
        for source in enabled:
            if source.source_id in completed:
                ordered.append(completed[source.source_id])
            elif source.source_id in unavailable:
                ordered.append(
                    SourceSearchResult(
                        (),
                        RetrievalSourceReport(
                            source.source_id,
                            source.source_kind,
                            "unavailable",
                            error="backend worker already in flight",
                        ),
                    )
                )
            else:
                ordered.append(
                    SourceSearchResult(
                        (),
                        RetrievalSourceReport(
                            source.source_id,
                            source.source_kind,
                            "timeout",
                        ),
                    )
                )
        return ordered

    def _all_type_entries(
        self,
        policy: Optional[RetrievalSourcePolicy] = None,
        *,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> list[tuple[Any, CandidateOrigin]]:
        out: list[tuple[Any, CandidateOrigin]] = []
        for source in self.sources:
            if policy is not None and not self._source_enabled(source, policy):
                continue
            entries = source.iter_entries()
            # Large corpora require a persisted/offline type index.  Never
            # parse an entire Mathlib-sized corpus in a live proof action.
            if len(entries) > _MAX_LAZY_TYPE_INDEX_ENTRIES:
                continue
            if len(out) + len(entries) > _MAX_LAZY_TYPE_INDEX_ENTRIES:
                continue
            for entry_index, entry in enumerate(entries):
                if entry_index % 16 == 0 and deadline_exhausted is not None:
                    if deadline_exhausted():
                        return out
                if isinstance(source, AnswerSafePreambleSource):
                    origin = source._origin(entry)
                elif isinstance(source, StaticMathlibSource):
                    origin = source._origin(entry)
                elif isinstance(source, ProjectSupportSource):
                    origin = source._origin(entry)
                elif isinstance(source, PublishedTheorySource):
                    bundle_id = str(_entry_value(entry, "_bundle_id", "") or "")
                    module_name = str(_entry_value(entry, "_module_name", "") or "")
                    active = bundle_id in set(source.active_bundle_ids())
                    origin = CandidateOrigin(
                        source_kind=source.source_kind,
                        source_id=source.source_id,
                        module_name=module_name,
                        import_text=f"import {module_name}" if module_name else "",
                        source_path=module_name,
                        environment_hash=source.environment_hash,
                        trust_kind="published_kernel_verified",
                        availability=(
                            "already_imported"
                            if active
                            else "requires_bundle_activation"
                        ),
                        required_bundle_ids=(bundle_id,) if bundle_id else (),
                    )
                elif isinstance(source, VerifiedHelperSource):
                    origin = source._origin(entry)
                else:
                    continue
                out.append((entry, origin))
        return out

    @staticmethod
    def _origin_for_entry(
        source: MathematicalRetrievalSource,
        entry: Any,
    ) -> Optional[CandidateOrigin]:
        if isinstance(source, AnswerSafePreambleSource):
            return source._origin(entry)
        if isinstance(source, StaticMathlibSource):
            return source._origin(entry)
        if isinstance(source, ProjectSupportSource):
            return source._origin(entry)
        if isinstance(source, PublishedTheorySource):
            bundle_id = str(_entry_value(entry, "_bundle_id", "") or "")
            module_name = str(_entry_value(entry, "_module_name", "") or "")
            active = bundle_id in set(source.active_bundle_ids())
            return CandidateOrigin(
                source_kind=source.source_kind,
                source_id=source.source_id,
                module_name=module_name,
                import_text=f"import {module_name}" if module_name else "",
                source_path=module_name,
                environment_hash=source.environment_hash,
                trust_kind="published_kernel_verified",
                availability=(
                    "already_imported"
                    if active
                    else "requires_bundle_activation"
                ),
                required_bundle_ids=(bundle_id,) if bundle_id else (),
            )
        if isinstance(source, VerifiedHelperSource):
            return source._origin(entry)
        return None

    def _query_scoped_large_type_entries(
        self,
        query: RetrievalQuery,
        *,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> list[tuple[Any, CandidateOrigin]]:
        """Select full-corpus type candidates without full live shape parsing.

        Mathlib and project retrievers already maintain inverted indexes over
        declaration names and types.  Use those indexes only to form a bounded
        recall pool, then apply the independent declaration-shape scorer.  This
        preserves type-directed discovery for research-sized corpora while
        avoiding the former 207k-declaration, >90 second first-query parse.
        """

        query_parts = (
            query.target_statement,
            query.result_head,
            *query.constants,
            *query.namespaces,
            *query.binder_heads,
            *query.shape_tags,
            *query.typeclass_needs,
        )
        generic_lookup_tokens = {
            match.group(0).lower()
            for part in query_parts
            for match in _TOKEN_RE.finditer(str(part or ""))
            if match.group(0).strip()
        }
        raw_query = " ".join(str(part or "") for part in query_parts)
        if not generic_lookup_tokens and not raw_query.strip():
            return []
        out: list[tuple[Any, CandidateOrigin]] = []
        for source in self.sources:
            if deadline_exhausted is not None and deadline_exhausted():
                break
            if not self._source_enabled(source, query.source_policy):
                continue
            entries = source.iter_entries()
            if len(entries) <= _MAX_LAZY_TYPE_INDEX_ENTRIES:
                continue
            # Backend inverted indexes are keyed by the unfiltered snapshot.
            # ProjectSupportSource.iter_entries() may drop PutnamBench contest
            # rows, so ID lookup must use that original snapshot.
            id_entries = (
                source._entry_snapshot
                if isinstance(source, ProjectSupportSource)
                else entries
            )
            candidate_scores: dict[int, float] = defaultdict(float)
            if isinstance(source, StaticMathlibSource):
                from ..mathlib_api_search import _tokenize as mathlib_tokenize

                lookup_tokens = generic_lookup_tokens | set(
                    mathlib_tokenize(raw_query)
                )
                token_index = getattr(source.searcher, "_token_index", {}) or {}
                token_postings = sorted(
                    (
                        (token, tuple(token_index.get(token, ())))
                        for token in lookup_tokens
                    ),
                    key=lambda item: (len(item[1]), item[0]),
                )
                for _token, postings in token_postings:
                    weight = 1.0 / max(1, len(postings))
                    for posting_index, entry_id in enumerate(postings):
                        if posting_index % 64 == 0 and deadline_exhausted is not None:
                            if deadline_exhausted():
                                return out
                        candidate_scores[int(entry_id)] += weight
                        if len(candidate_scores) >= _MAX_TYPE_POSTING_ACCUMULATION:
                            break
            elif isinstance(source, ProjectSupportSource):
                from ..tokenizer import tokenize

                lookup_tokens = generic_lookup_tokens | set(tokenize(raw_query))
                index = getattr(source.retriever, "index", None)
                inverted = getattr(index, "inv_index", {}) or {}
                token_postings = sorted(
                    (
                        (token, tuple(inverted.get(token, ())))
                        for token in lookup_tokens
                    ),
                    key=lambda item: (len(item[1]), item[0]),
                )
                for _token, postings in token_postings:
                    weight = 1.0 / max(1, len(postings))
                    for posting_index, (doc_id, term_frequency) in enumerate(postings):
                        if posting_index % 64 == 0 and deadline_exhausted is not None:
                            if deadline_exhausted():
                                return out
                        candidate_scores[int(doc_id)] += weight * max(
                            1.0,
                            float(term_frequency or 0.0),
                        )
                        if len(candidate_scores) >= _MAX_TYPE_POSTING_ACCUMULATION:
                            break
            if not candidate_scores:
                continue
            ranked_ids = sorted(
                candidate_scores,
                key=lambda entry_id: (-candidate_scores[entry_id], entry_id),
            )[:_MAX_QUERY_SCOPED_TYPE_ENTRIES]
            for position, entry_id in enumerate(ranked_ids):
                if position % 16 == 0 and deadline_exhausted is not None:
                    if deadline_exhausted():
                        break
                if entry_id < 0 or entry_id >= len(id_entries):
                    continue
                entry = id_entries[entry_id]
                if (
                    isinstance(source, ProjectSupportSource)
                    and _is_putnam_bench_problem_entry(entry)
                ):
                    continue
                origin = self._origin_for_entry(source, entry)
                if origin is not None:
                    out.append((entry, origin))
        return out

    def _get_type_index(
        self,
        policy: Optional[RetrievalSourcePolicy] = None,
        *,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> _FederatedTypeIndex:
        snapshot = self.index_snapshot_id
        policy_key = stable_retrieval_hash(
            policy.to_record() if policy is not None else {}
        )
        snapshot = f"{snapshot}:{policy_key}"
        cached = self._type_index_cache.get(snapshot)
        if cached is None:
            cached = _FederatedTypeIndex(
                self._all_type_entries(
                    policy,
                    deadline_exhausted=deadline_exhausted,
                ),
                deadline_exhausted=deadline_exhausted,
            )
            if cached.complete:
                if len(self._type_index_cache) >= 8:
                    self._type_index_cache.pop(next(iter(self._type_index_cache)))
                self._type_index_cache[snapshot] = cached
        self._type_index = cached
        self._type_index_snapshot_id = snapshot
        return cached

    @staticmethod
    def _candidate_key(hit: SourceHit) -> tuple[str, str, str, str, str]:
        return (
            hit.origin.environment_hash,
            hit.origin.module_name,
            _entry_name(hit.entry),
            stable_retrieval_hash(_entry_type(hit.entry)),
            _entry_kind(hit.entry),
        )

    def retrieve(
        self,
        query: RetrievalQuery,
        *,
        deadline_monotonic: Optional[float] = None,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        extra_entries: Sequence[tuple[Any, CandidateOrigin]] = (),
    ) -> RetrievalResult:
        started = time.monotonic()
        operation_deadline = started + self.operation_timeout_s
        caller_deadline = (
            None if deadline_monotonic is None else float(deadline_monotonic)
        )
        if deadline_monotonic is None:
            deadline_monotonic = operation_deadline
        else:
            deadline_monotonic = min(
                float(deadline_monotonic),
                operation_deadline,
            )
        snapshot = self.index_snapshot_id
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            result = RetrievalResult(
                request_id=query.request_id,
                index_snapshot_id=snapshot,
                candidates=(),
                source_reports=(
                    RetrievalSourceReport(
                        "federated_retrieval",
                        "service",
                        "timeout",
                        index_snapshot_id=snapshot,
                    ),
                ),
                elapsed_s=time.monotonic() - started,
                truncated=True,
                deadline_exhausted=True,
            )
            self.last_result = result
            self.publish_result_metrics(result, consumer="direct")
            return result
        if query.index_snapshot_id and query.index_snapshot_id != snapshot:
            reports = tuple(
                RetrievalSourceReport(
                    source.source_id,
                    source.source_kind,
                    "stale",
                    index_snapshot_id=source.snapshot_id(),
                )
                for source in self.sources
                if self._source_enabled(source, query.source_policy)
            )
            result = RetrievalResult(
                query.request_id,
                snapshot,
                (),
                reports,
                time.monotonic() - started,
            )
            self.last_result = result
            self.publish_result_metrics(result, consumer="direct")
            return result

        pool_size = max(query.max_candidates, query.max_candidates * 4)
        # Caller-supplied helpers are already resident and do not depend on a
        # source adapter.  Score them before dispatching fallible/remote
        # sources so an adapter consuming its budget cannot erase useful
        # local evidence.  The operation deadline still bounds construction;
        # any completed prefix remains safe to return under an internal
        # timeout, while caller cancellation is enforced at final acceptance.
        all_hits: list[SourceHit] = []
        if extra_entries:
            def local_deadline_exhausted() -> bool:
                return _retrieval_elapsed(
                    deadline_monotonic,
                    deadline_exhausted,
                )

            local_index = _FederatedTypeIndex(
                extra_entries,
                deadline_exhausted=local_deadline_exhausted,
            )
            all_hits.extend(
                local_index.search(
                    query,
                    max_results=pool_size,
                    channel="verified_helper_local",
                    deadline_exhausted=local_deadline_exhausted,
                )
            )
        source_results = self._search_sources_parallel(
            query,
            pool_size=pool_size,
            deadline_monotonic=deadline_monotonic,
            deadline_exhausted=deadline_exhausted,
        )
        if not source_results:
            source_results.append(
                SourceSearchResult(
                    (),
                    RetrievalSourceReport(
                        "federated_retrieval",
                        "service",
                        "unavailable",
                        index_snapshot_id=snapshot,
                    ),
                )
            )

        all_hits.extend(
            hit for source_result in source_results for hit in source_result.hits
        )
        source_operation_truncated = any(
            source_result.report.health == "timeout"
            or bool(source_result.report.truncated)
            for source_result in source_results
        )
        if (
            self.enable_type_index
            and (
                query.result_head
                or query.constants
                or query.shape_tags
                or query.binder_heads
                or "typed_goal" in query.intended_uses
            )
            and not source_operation_truncated
            and not _retrieval_elapsed(deadline_monotonic, deadline_exhausted)
        ):
            remaining_for_type_s = max(
                0.0,
                float(deadline_monotonic) - time.monotonic(),
            )
            type_fusion_reserve_s = min(
                0.5,
                max(0.05, remaining_for_type_s * 0.2),
            )
            type_phase_deadline = float(deadline_monotonic) - type_fusion_reserve_s

            def type_deadline_exhausted() -> bool:
                return bool(
                    time.monotonic() >= type_phase_deadline
                    or _retrieval_elapsed(
                        deadline_monotonic,
                        deadline_exhausted,
                    )
                )
            # Type guidance independently searches bounded corpora and reranks
            # the lexical/semantic pool.  A
            # lazy whole-corpus shape index made the first Mathlib query parse
            # 207k declarations on the event loop (>90s in a real repro).
            # Candidate-scoped typing is deterministic, policy-safe, and keeps
            # the cheap closer cheap; a persisted offline type index can later
            # add independent recall without reintroducing this stall.
            source_pool = list(all_hits)
            all_hits.extend(
                self._get_type_index(
                    query.source_policy,
                    deadline_exhausted=type_deadline_exhausted,
                ).search(
                    query,
                    max_results=pool_size,
                    deadline_exhausted=type_deadline_exhausted,
                )
            )
            large_type_pool = self._query_scoped_large_type_entries(
                query,
                deadline_exhausted=type_deadline_exhausted,
            )
            if large_type_pool:
                all_hits.extend(
                    _FederatedTypeIndex(
                        large_type_pool,
                        deadline_exhausted=type_deadline_exhausted,
                    ).search(
                        query,
                        max_results=pool_size,
                        deadline_exhausted=type_deadline_exhausted,
                    )
                )
            typed_pool = [(hit.entry, hit.origin) for hit in source_pool]
            if typed_pool:
                all_hits.extend(
                    _FederatedTypeIndex(
                        typed_pool,
                        deadline_exhausted=type_deadline_exhausted,
                    ).search(
                        query,
                        max_results=pool_size,
                        deadline_exhausted=type_deadline_exhausted,
                    )
                )
        deduplicated_hits: dict[
            tuple[tuple[str, str, str, str, str], str, str], SourceHit
        ] = {}
        for hit in all_hits:
            key = (self._candidate_key(hit), hit.origin.source_id, hit.channel)
            previous = deduplicated_hits.get(key)
            if previous is None or hit.score > previous.score:
                deduplicated_hits[key] = hit
        # RRF ranks must reflect each source/channel's own SCORE order, not the
        # order hits happen to arrive in (lexical hits then type_shape batches).
        # Sorting by descending score before the single-pass rank counter makes
        # the highest-scoring hit in each (source_id, channel) group rank 1.
        all_hits = sorted(
            deduplicated_hits.values(),
            key=lambda hit: float(getattr(hit, "score", 0.0) or 0.0),
            reverse=True,
        )

        by_key: dict[tuple[str, str, str, str, str], dict[str, Any]] = {}
        channel_rank: dict[tuple[str, str], int] = defaultdict(int)
        query_text = " ".join(
            part
            for part in (
                query.target_statement,
                query.natural_language,
                query.route_context,
                *query.ordered_local_context,
            )
            if part
        )
        for hit in all_hits:
            if query.source_policy.allowed_source_ids and (
                hit.origin.source_id not in query.source_policy.allowed_source_ids
            ):
                continue
            if not {
                "mathlib": query.source_policy.include_mathlib,
                "project": query.source_policy.include_project,
                "published_theory": query.source_policy.include_published_theory,
                "verified_helper": query.source_policy.include_verified_helpers,
            }.get(hit.origin.source_kind, True):
                continue
            name = _entry_name(hit.entry)
            typ = _entry_type(hit.entry)
            kind = _entry_kind(hit.entry)
            source_path = str(hit.origin.source_path or "")
            try:
                normalized_source_path = str(Path(source_path).resolve())
            except OSError:
                normalized_source_path = source_path
            if (
                not name
                or not typ
                or name == query.theorem_name
                or name in self.excluded_declaration_names
                or normalized_source_path in self.excluded_source_paths
            ):
                continue
            if query.source_policy.theorem_kinds_only and kind not in _ENTRY_KINDS:
                continue
            if (
                not query.source_policy.include_inactive
                and hit.origin.availability != "already_imported"
            ):
                continue
            # Each source emits its own ranked list.  Sharing one counter for
            # same-named channels made configured root order dominate RRF.
            source_channel = (hit.origin.source_id, hit.channel)
            channel_rank[source_channel] += 1
            rank = channel_rank[source_channel]
            key = self._candidate_key(hit)
            state = by_key.setdefault(
                key,
                {
                    "entry": hit.entry,
                    "origins": [],
                    "ranks": {},
                    "scores": {},
                    "reasons": [],
                    "fusion": 0.0,
                },
            )
            if hit.origin not in state["origins"]:
                state["origins"].append(hit.origin)
            state["ranks"][hit.channel] = min(
                rank, int(state["ranks"].get(hit.channel, rank))
            )
            state["scores"][hit.channel] = max(
                float(hit.score), float(state["scores"].get(hit.channel, -math.inf))
            )
            for reason in hit.reasons:
                if reason and reason not in state["reasons"]:
                    state["reasons"].append(reason)
            weight = float(self.channel_weights.get(hit.channel, 1.0))
            state["fusion"] += weight / (self.rrf_k + rank)

        candidates: list[RetrievalCandidate] = []
        for state in by_key.values():
            analogy = _analogy_score(query_text, _entry_type(state["entry"]))
            if analogy > 0.0:
                state["scores"]["analogy"] = analogy
                state["fusion"] += 0.15 * analogy
                state["reasons"].append("analogy_shape")
            origins = tuple(
                sorted(
                    state["origins"],
                    key=lambda origin: (
                        _AVAILABILITY_ORDER.get(origin.availability, 99),
                        origin.source_kind,
                        origin.source_id,
                    ),
                )
            )
            availability = origins[0].availability
            candidates.append(
                RetrievalCandidate(
                    candidate_id="",
                    declaration_name=_entry_name(state["entry"]),
                    type_text=_entry_type(state["entry"]),
                    declaration_kind=_entry_kind(state["entry"]),
                    origins=origins,
                    channel_ranks=state["ranks"],
                    channel_scores=state["scores"],
                    fusion_score=float(state["fusion"]),
                    reasons=tuple(state["reasons"]),
                    availability=availability,
                )
            )
        candidates.sort(
            key=lambda candidate: (
                0
                if "verified_helper_local" in candidate.channel_ranks
                else 1,
                -candidate.fusion_score,
                _AVAILABILITY_ORDER.get(candidate.availability, 99),
                candidate.declaration_name,
            )
        )
        effective_source_counts: dict[str, int] = defaultdict(int)
        for candidate in candidates:
            for source_id in {
                origin.source_id for origin in candidate.origins
            }:
                effective_source_counts[source_id] += 1
        normalized_source_results: list[SourceSearchResult] = []
        for source_result in source_results:
            report = source_result.report
            effective_count = effective_source_counts.get(report.source_id, 0)
            if report.health in {"success_with_hits", "success_zero_hits"}:
                report = replace(
                    report,
                    health=(
                        "success_with_hits"
                        if effective_count > 0
                        else "success_zero_hits"
                    ),
                    hit_count=effective_count,
                )
            normalized_source_results.append(
                SourceSearchResult(source_result.hits, report)
            )
        source_results = normalized_source_results
        elapsed = _retrieval_elapsed(deadline_monotonic, deadline_exhausted)
        caller_cancelled = _retrieval_elapsed(
            caller_deadline,
            deadline_exhausted,
        )
        adapter_timeout = source_operation_truncated
        truncated = (
            len(candidates) > query.max_candidates
            or elapsed
            or adapter_timeout
        )
        # Preserve at least one strong result from as many productive source
        # adapters as the result budget permits, then fill by global rank. This
        # prevents a large Mathlib list from erasing project/theory/helper
        # discovery before activation can be tested.
        if query.source_policy.include_inactive and candidates:
            by_source: dict[str, RetrievalCandidate] = {}
            for candidate in candidates:
                for origin in candidate.origins:
                    by_source.setdefault(origin.source_id, candidate)
            reserved: list[RetrievalCandidate] = []
            for candidate in by_source.values():
                if candidate not in reserved:
                    reserved.append(candidate)
            reserved.sort(key=candidates.index)
            reserved = reserved[: query.max_candidates]
            selected = list(reserved)
            selected_ids = {candidate.candidate_id for candidate in selected}
            # candidate_id is filled by the immutable contract; fall back to
            # object identity defensively for test doubles.
            for candidate in candidates:
                if len(selected) >= query.max_candidates:
                    break
                if candidate in selected or candidate.candidate_id in selected_ids:
                    continue
                selected.append(candidate)
                selected_ids.add(candidate.candidate_id)
            candidates = sorted(selected, key=candidates.index)
        else:
            candidates = candidates[: query.max_candidates]
        if caller_cancelled:
            candidates = []
        final_snapshot = self.index_snapshot_id
        if final_snapshot != snapshot:
            result = RetrievalResult(
                request_id=query.request_id,
                index_snapshot_id=final_snapshot,
                candidates=(),
                source_reports=(
                    *tuple(result.report for result in source_results),
                    RetrievalSourceReport(
                        "federated_retrieval",
                        "service",
                        "stale",
                        index_snapshot_id=final_snapshot,
                    ),
                ),
                elapsed_s=time.monotonic() - started,
                truncated=True,
                deadline_exhausted=elapsed,
            )
            self.last_result = result
            self.publish_result_metrics(result, consumer="direct")
            return result
        result = RetrievalResult(
            request_id=query.request_id,
            index_snapshot_id=snapshot,
            candidates=tuple(candidates),
            source_reports=tuple(result.report for result in source_results),
            elapsed_s=time.monotonic() - started,
            truncated=truncated,
            deadline_exhausted=elapsed or adapter_timeout,
        )
        self.last_result = result
        consumer = next(
            (
                item
                for item in ("proof_state", "repair", "reactive", "eager")
                if item in query.intended_uses
            ),
            "direct",
        )
        self.publish_result_metrics(result, consumer=consumer)
        return result

    async def retrieve_async(
        self,
        query: RetrievalQuery,
        *,
        deadline_monotonic: Optional[float] = None,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
        extra_entries: Sequence[tuple[Any, CandidateOrigin]] = (),
    ) -> RetrievalResult:
        from .async_runtime import (
            RetrievalWorkerCapacityError,
            run_sync_abandonment_safe,
        )

        started = time.monotonic()
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            result = RetrievalResult(
                request_id=query.request_id,
                index_snapshot_id=query.index_snapshot_id,
                candidates=(),
                source_reports=(
                    RetrievalSourceReport(
                        "federated_retrieval",
                        "service",
                        "timeout",
                        index_snapshot_id=query.index_snapshot_id,
                    ),
                ),
                elapsed_s=0.0,
                truncated=True,
                deadline_exhausted=True,
            )
            self.last_result = result
            self.publish_result_metrics(result, consumer="direct")
            return result
        timeout_s = self.operation_timeout_s
        if deadline_monotonic is not None:
            timeout_s = min(
                timeout_s,
                max(0.0, float(deadline_monotonic) - started),
            )
        worker_view = self.fork_session_context()
        capacity_exhausted = False
        try:
            result = await run_sync_abandonment_safe(
                lambda: worker_view.retrieve(
                    query,
                    deadline_monotonic=deadline_monotonic,
                    deadline_exhausted=deadline_exhausted,
                    extra_entries=extra_entries,
                ),
                timeout_s=timeout_s,
                deadline_exhausted=deadline_exhausted,
            )
        except (TimeoutError, RetrievalWorkerCapacityError) as exc:
            capacity_exhausted = isinstance(exc, RetrievalWorkerCapacityError)
            result = RetrievalResult(
                request_id=query.request_id,
                index_snapshot_id=query.index_snapshot_id,
                candidates=(),
                source_reports=(
                    RetrievalSourceReport(
                        "federated_retrieval",
                        "service",
                        (
                            "timeout"
                            if isinstance(exc, TimeoutError)
                            else "unavailable"
                        ),
                        index_snapshot_id=query.index_snapshot_id,
                    ),
                ),
                elapsed_s=time.monotonic() - started,
                truncated=True,
                deadline_exhausted=isinstance(exc, TimeoutError),
            )
        if _retrieval_elapsed(deadline_monotonic, deadline_exhausted):
            result = replace(
                result,
                candidates=(),
                deadline_exhausted=True,
                truncated=True,
            )
        self.last_result = result
        consumer = next(
            (
                item
                for item in ("proof_state", "repair", "reactive", "eager")
                if item in query.intended_uses
            ),
            "direct",
        )
        self.publish_result_metrics(result, consumer=consumer)
        if capacity_exhausted and self._metric_sink is not None:
            try:
                self._metric_sink(
                    "mini_mathematical_retrieval_capacity_exhaustions",
                    1,
                )
            except Exception:
                pass
        return result

    def _compatibility_entry(self, candidate: RetrievalCandidate) -> Any:
        origin = candidate.origins[0]
        return SimpleNamespace(
            name=candidate.declaration_name,
            type=candidate.type_text,
            kind=candidate.declaration_kind,
            file=origin.source_path,
            namespace=candidate.declaration_name.rsplit(".", 1)[0]
            if "." in candidate.declaration_name
            else "",
            docstring="",
            source=origin.source_kind,
            retrieval_candidate=candidate,
        )

    def candidate_entry(self, candidate: RetrievalCandidate) -> Any:
        """Return the declaration-like compatibility view used by Mini executors."""

        return self._compatibility_entry(candidate)

    def search_with_scores(
        self,
        query_text: str,
        *,
        goal_state: str = "",
        kind: str = "any",
        max_results: int = 10,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> list[FederatedSearchHit]:
        normalized_kind = str(kind).strip().lower()
        policy = RetrievalSourcePolicy(
            # ``any`` is the compatibility API's unfiltered mode.  Treating it
            # as theorem-only silently hid definitions (including target-local
            # objects from the answer-safe preamble) before the explicit kind
            # filter below ever saw them.
            theorem_kinds_only=normalized_kind
            in {"theorem", "lemma", "axiom", "theorem_like"}
        )
        query = RetrievalQuery.create(
            target_statement=str(goal_state or query_text),
            natural_language=str(query_text or ""),
            intended_uses=(
                ("discovery", "typed_goal")
                if str(goal_state or "").strip()
                else ("discovery",)
            ),
            source_policy=policy,
            max_candidates=max(1, int(max_results)),
            index_snapshot_id=self.index_snapshot_id,
        )
        result = self.retrieve(query, deadline_exhausted=deadline_exhausted)
        out: list[FederatedSearchHit] = []
        for candidate in result.candidates:
            if normalized_kind == "theorem_like":
                if candidate.declaration_kind not in _ENTRY_KINDS:
                    continue
            elif (
                normalized_kind != "any"
                and candidate.declaration_kind != normalized_kind
            ):
                continue
            out.append(
                FederatedSearchHit(
                    entry=self._compatibility_entry(candidate),
                    score=candidate.fusion_score,
                    reasons=candidate.reasons,
                    details=dict(candidate.channel_scores),
                    candidate=candidate,
                )
            )
        return out[:max_results]

    def search(
        self,
        query_text: str,
        *,
        goal_state: str = "",
        kind: str = "any",
        max_results: int = 10,
        deadline_exhausted: Optional[Callable[[], bool]] = None,
    ) -> list[Any]:
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

    def search_mathlib_with_scores(self, *args: Any, **kwargs: Any) -> list[Any]:
        if self.static_mathlib_searcher is None:
            return []
        return list(self.static_mathlib_searcher.search_with_scores(*args, **kwargs) or [])

    def search_mathlib(self, *args: Any, **kwargs: Any) -> list[Any]:
        if self.static_mathlib_searcher is None:
            return []
        return list(self.static_mathlib_searcher.search(*args, **kwargs) or [])

    def format_context(self, entries: Sequence[Any]) -> str:
        lines: list[str] = []
        for entry in entries:
            candidate = getattr(entry, "retrieval_candidate", None)
            source_label = ""
            if candidate is not None and candidate.origins:
                origin = candidate.origins[0]
                source_label = f"  -- {origin.source_kind}/{origin.availability}"
            lines.append(f"{_entry_name(entry)} : {_entry_type(entry)}{source_label}")
        return "\n".join(lines)
